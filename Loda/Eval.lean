import Loda.Ast
import Loda.Env

open Ast
open Env

/-!
  # Evaluator for Loda AST

  This module implements a small-step interpreter for Loda expressions.
  It provides functions to evaluate binary operations, relations, and
  full `Expr`s under given valuation, circuit, and type environments,
  with a fuel parameter to ensure termination.
-/

namespace Eval

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

/--
  Evaluate an expression `e` under a valuation environment `σ`,
  a circuit environment `δ`, and a fuel bound `fuel`.
  Returns `none` if evaluation gets stuck or fuel is exhausted.
-/
@[simp]
def eval (fuel: ℕ) (σ : ValEnv) (δ : CircuitEnv) : Expr → Option (Value)
  -- E-VALUE
  | Expr.constF p v      => pure (Value.vF p v)
  | Expr.constInt i      => pure (Value.vInt i)
  | Expr.constBool b     => pure (Value.vBool b)

  -- E-VAR
  | Expr.var x           => pure (lookupVal σ x)

  -- E-LAM
  | Expr.lam x _ e       => pure (Value.vClosure x e σ)

  | Expr.letIn x e₁ e₂   => do
    if fuel > 0 then
      let v₁ ← eval (fuel -1) σ δ  e₁
      let σ' := updateVal σ x v₁
      eval (fuel -1) σ' δ e₂
    else
      none

  -- E-APP
  | Expr.app f e         => do
      if fuel > 0 then
        let vf ← eval (fuel -1) σ δ  f
        let va ← eval (fuel -1) σ δ  e
        match vf with
        | Value.vClosure x body σ' =>
          let σ'' := updateVal σ' x va
          eval (fuel -1) σ'' δ body
        | _ => none
      else
        none

  -- E-FBINOP
  | Expr.fieldExpr e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval (fuel - 1) σ δ  e₁
        let v₂ ← eval (fuel - 1) σ δ  e₂
        evalFieldOp op v₁ v₂
      else
        none

  | Expr.intExpr e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval (fuel - 1) σ δ  e₁
        let v₂ ← eval (fuel - 1) σ δ  e₂
        evalIntegerOp op v₁ v₂
      else
        none

  | Expr.binRel e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval (fuel - 1) σ δ  e₁
        let v₂ ← eval (fuel - 1) σ δ  e₂
        let b ← evalRelOp op v₁ v₂
        pure (Value.vBool b)
      else
        none

  -- E-PRODCONS
  | Expr.prodCons es     => do
      if fuel > 0 then
        let vs ← es.mapM (eval (fuel - 1) σ δ )
        pure (Value.vProd vs)
      else
        none

  | Expr.prodIdx e i     => do
      if fuel > 0 then
        let v ← eval (fuel - 1) σ δ  e
        match v with
        | Value.vProd vs => vs[i]?
        | _              => none
      else
        none

  | Expr.arrCons h t     => do
      if fuel > 0 then
        let vh ← eval (fuel - 1) σ δ  h
        let vt ← eval (fuel - 1) σ δ  t
        match vt with
        | Value.vArr vs => pure (Value.vArr (vh :: vs))
        | _             => pure (Value.vArr ([vh, vt]))
      else
        none

  | Expr.arrLen e        => do
      if fuel > 0 then
        let v ← eval (fuel - 1) σ δ  e
        match v with
        | Value.vArr vs => pure (Value.vInt vs.length)
        | _             => none
      else
        none

  | Expr.arrIdx a i      => do
      if fuel > 0 then
        let va ← eval (fuel - 1) σ δ  a
        let vi ← eval (fuel - 1) σ δ  i
        match va, vi with
        | Value.vArr vs, Value.vInt j => vs[j.toNat]?
        | _, _                        => none
      else
        none

  -- E-ITER
  | Expr.iter sExpr eExpr fExpr accExpr => do
      if fuel > 0 then
        let sVal ← eval (fuel - 1) σ δ  sExpr
        let eVal ← eval (fuel - 1) σ δ  eExpr
        match sVal, eVal with
        | Value.vInt s, Value.vInt e => do
            let fVal ← eval (fuel - 1) σ δ  fExpr
            let aVal ← eval (fuel - 1) σ δ  accExpr
            let rec loop (i : ℤ) (fuel': ℕ) (acc : Value) : Option Value :=
              if fuel' = 0 then
                none
              else
                if i ≥ e then pure acc else
                if (fuel - 1) > 0 then
                  match fVal with
                  | Value.vClosure x body σ' => do
                      -- apply f to index i
                      let σ₁ := updateVal σ' x (Value.vInt i)
                      let fInner ← eval (fuel' - 1) σ₁ δ body
                      match fInner with
                      | Value.vClosure y accBody σ₂ => do
                          -- apply resulting closure to accumulator
                          let σ₃ := updateVal σ₂ y acc
                          let newAcc ← eval (fuel' - 1) σ₃ δ accBody
                          loop (i+1) (fuel' - 1) newAcc
                      | _ => none
                  | _ => none
                else
                  none
              termination_by fuel'
            loop s (fuel - 1) aVal
        | _, _ => none
      else
        none

  -- E-CREF
  | Expr.circRef name arg => do
      if fuel > 0 then
        --let vs ← args.mapM (eval (fuel - 1) σ δ )
        let v := eval (fuel - 1) σ δ  arg
        let c := Env.lookupCircuit δ name
        --let σ' := (c.inputs.zip vs).foldl (fun env (⟨x,_⟩,v) => updateVal env x v) σ
        match v with
        | some vv => eval (fuel - 1) (updateVal σ name vv) δ c.body
        | _ => none
      else
        none

  | _ => none
  -- The natural number fuel decreases in every recursive call
  termination_by fuel

end Eval
