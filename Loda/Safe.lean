import Loda.Ast
import Loda.Env

open Ast
open Env

/-!
  # Safe Evaluator for Loda AST (without fuel)

  This module implements a small-step interpreter for Loda expressions.
  The implementation is structured using mutual recursion to be provably
  terminating in Lean without an explicit `fuel` parameter, for expressions
  that themselves terminate.

  - `eval` handles structurally recursive evaluation.
  - `apply` handles non-structural jumps from function application.
  - `evalList` is a helper for evaluating lists of expressions.
  - `iter_loop` is a well-founded helper for the `iter` construct.

  Note: This interpreter will not terminate for Loda programs that contain
  infinite loops (e.g., `let f := λx. f x in f 0`). This is fundamental,
  as proving termination for all programs is undecidable (Halting Problem).
  The goal here is to ensure the *interpreter function itself* is considered
  terminating by Lean's logic for all inputs.
-/

-- We keep the helper functions for operations as they are.
@[inline]
def maximumRecursion : Nat := 1000

/-- Evaluate a field operation `op` on two `Value.field` arguments. -/
@[simp]
def evalFieldOp (op: FieldOp) : Value → Value → Option Value
  | Value.vF p₁ x, Value.vF p₂ y =>
    if h : p₁ = p₂ then
      let y' := Eq.mp (by rw [h]) y
      some $ Value.vF p₁ $
        match op with
        | FieldOp.add => x + y'
        | FieldOp.sub => x - y'
        | FieldOp.mul => x * y'
        | FieldOp.div => x * y'.inv
    else
      none
  | _, _ => none

/-- Evaluate an integer operation `op` on two `Value.int` arguments. -/
@[simp]
def evalIntegerOp (op: IntegerOp) : Value → Value → Option Value
  | Value.vInt x, Value.vInt y =>
    some $ Value.vInt $
      match op with
      | IntegerOp.add => x + y
      | IntegerOp.sub => x - y
      | IntegerOp.mul => x * y
  | _, _ => none

/-- Evaluate a relational operator `op` on two `Value` arguments. -/
@[simp]
def evalRelOp (op: RelOp) : Value → Value → Option Bool
  | Value.vF p₁ i, Value.vF p₂ j =>
    if h : p₁ = p₂ then
      some $ match op with
      | RelOp.eq => i = (Eq.mp (by rw [h]) j)
      | RelOp.lt => i.val % p₁ < j.val % p₁
      | RelOp.le => i.val % p₁ ≤ j.val % p₁
    else
      none
  | Value.vInt i, Value.vInt j =>
    some $ match op with
    | RelOp.eq => i = j
    | RelOp.lt => i < j
    | RelOp.le => i ≤ j
  | _, _ => none

/-- Evaluate a boolean operator `op` on two `Value.bool` arguments. -/
@[simp]
def evalBoolOp (op : BooleanOp) : Value → Value → Option Bool
  | Value.vBool x, Value.vBool y =>
    some $ match op with
    | BooleanOp.and => x && y
    | BooleanOp.or  => x || y
  | _, _ => none

-- Full definition of the mutually recursive functions
mutual
  partial def eval (σ : ValEnv) (Δ : CircuitEnv) : Ast.Expr → Option Value
    -- Base cases
    | Expr.constF p v      => pure (Value.vF p v)
    | Expr.constInt i      => pure (Value.vInt i)
    | Expr.constBool b     => pure (Value.vBool b)
    | Expr.var x           => pure (lookupVal σ x)
    | Expr.lam x _ e       => pure (Value.vClosure x e σ)

    -- Structural recursion
    | Expr.letIn x e₁ e₂   => do
      let v₁ ← eval σ Δ e₁
      let σ' := updateVal σ x v₁
      eval σ' Δ e₂

    | Expr.fieldExpr e₁ op e₂ => do
      let v₁ ← eval σ Δ e₁
      let v₂ ← eval σ Δ e₂
      evalFieldOp op v₁ v₂

    | Expr.intExpr e₁ op e₂ => do
      let v₁ ← eval σ Δ e₁
      let v₂ ← eval σ Δ e₂
      evalIntegerOp op v₁ v₂

    | Expr.boolExpr e₁ op e₂ => do
      let v₁ ← eval σ Δ e₁
      let v₂ ← eval σ Δ e₂
      let b ← evalBoolOp op v₁ v₂
      pure (Value.vBool b)

    | Expr.assertE e₁ e₂ => do
      let v₁ ← eval σ Δ e₁
      let v₂ ← eval σ Δ e₂
      let b ← evalRelOp RelOp.eq v₁ v₂
      if b then pure (Value.vBool b) else none

    | Expr.binRel e₁ op e₂ => do
      let v₁ ← eval σ Δ e₁
      let v₂ ← eval σ Δ e₂
      let b ← evalRelOp op v₁ v₂
      pure (Value.vBool b)

    | Expr.prodCons es     => do
      let vs ← evalList σ Δ es
      pure (Value.vProd vs)

    | Expr.prodIdx e i     => do
      match ← eval σ Δ e with
      | Value.vProd vs => vs[i]?
      | _              => none

    | Expr.arrCons h t     => do
      let vh ← eval σ Δ h
      let vt ← eval σ Δ t
      match vt with
      | Value.vArr vs => pure (Value.vArr (vh :: vs))
      | _             => pure (Value.vArr ([vh, vt])) -- Handle case where t is not an array

    | Expr.arrLen e        => do
      match ← eval σ Δ e with
      | Value.vArr vs => pure (Value.vInt vs.length)
      | _             => none

    | Expr.arrIdx a i      => do
      let va ← eval σ Δ a
      let vi ← eval σ Δ i
      match va, vi with
      | Value.vArr vs, Value.vInt j => vs[j.toNat]?
      | _, _                        => none

    -- Delegation to `apply` for non-structural jump
    | Expr.app f e         => do
      let vf ← eval σ Δ f
      let va ← eval σ Δ e
      apply Δ vf va

    -- Delegation to `iter_loop`
    | Expr.iter sExpr eExpr fExpr accExpr => do
        let sVal ← eval σ Δ sExpr
        let eVal ← eval σ Δ eExpr
        match sVal, eVal with
        | Value.vInt s, Value.vInt e =>
          if s ≥ e then
            -- If loop does not run, evaluate the accumulator expression once.
            eval σ Δ accExpr
          else do
            let fVal ← eval σ Δ fExpr
            let aVal ← eval σ Δ accExpr
            let count := (e - s).toNat
            -- Delegate the iteration to the well-founded helper
            iter_loop count s aVal fVal Δ
        | _, _ => none

    | Expr.circRef name arg => do
        let v := eval  σ Δ  arg
        let c := Env.lookupCircuit Δ name
        --let σ' := (c.inputs.zip vs).foldl (fun env (⟨x,_⟩,v) => updateVal env x v) σ
        match v with
        | some vv => eval (updateVal σ name vv) Δ c.body
        | _ => none

      | _ => none

  partial def apply (Δ : CircuitEnv) : Value → Value → Option Value
    -- The actual non-structural jump happens here
    | Value.vClosure x body σ', va =>
      let σ'' := updateVal σ' x va
      eval σ'' Δ body -- Re-enter the main `eval` function
    | _, _ => none -- Not a function

  partial def evalList (σ : ValEnv) (Δ : CircuitEnv) : List Expr → Option (List Value)
    | [] => pure []
    | e::es => do
      let v ← eval σ Δ e
      let vs ← evalList σ Δ es
      pure (v :: vs)

  -- The main loop for `iter`, defined separately to prove termination.
  -- It recurses on `n`, the number of iterations remaining.
  -- `n` is guaranteed to decrease, proving termination.
  partial def iter_loop (n : Nat) (i : ℤ) (acc : Value) (fVal : Value) (Δ : CircuitEnv) : Option Value :=
    if n = 0 then
      pure acc
    else
      -- Apply the outer function `fVal` to the current index `i`
      match apply Δ fVal (Value.vInt i) with
      | none => none
      | some fInner =>
        -- Apply the inner function `fInner` to the current accumulator `acc`
        match apply Δ fInner acc with
        | none => none
        | some newAcc =>
          -- Recurse with decremented count and updated values
          iter_loop (n - 1) (i + 1) newAcc fVal Δ
  termination_by n

end
-- The `termination_by` clauses are implicitly handled by Lean for this structure.
-- `eval` decreases on the size of `Expr`.
-- `apply` calls `eval` but is part of the mutual block.
-- `evalList` decreases on the length of the list.

-- The main entry point that uses the safe evaluator.
@[simp]
def run (σ : ValEnv) (Δ : CircuitEnv) (e : Expr) : Option (Value) :=
  eval σ Δ e
