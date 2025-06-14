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

/--
  Evaluate an expression `e` under a valuation environment `σ`,
  a circuit environment `Δ`, and a fuel bound `fuel`.
  Returns `none` if evaluation gets stuck or fuel is exhausted.
-/
@[simp]
def eval_with_fuel (fuel: ℕ) (σ : ValEnv) (Δ : CircuitEnv) : Expr → Option (Value)
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
      let v₁ ← eval_with_fuel (fuel -1) σ Δ  e₁
      let σ' := updateVal σ x v₁
      eval_with_fuel (fuel -1) σ' Δ e₂
    else
      none

  -- E-APP
  | Expr.app f e         => do
      if fuel > 0 then
        let vf ← eval_with_fuel (fuel -1) σ Δ  f
        let va ← eval_with_fuel (fuel -1) σ Δ  e
        match vf with
        | Value.vClosure x body σ' =>
          let σ'' := updateVal σ' x va
          eval_with_fuel (fuel -1) σ'' Δ body
        | _ => none
      else
        none

  -- E-FBINOP
  | Expr.fieldExpr e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval_with_fuel (fuel - 1) σ Δ  e₁
        let v₂ ← eval_with_fuel (fuel - 1) σ Δ  e₂
        evalFieldOp op v₁ v₂
      else
        none

  | Expr.intExpr e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval_with_fuel (fuel - 1) σ Δ  e₁
        let v₂ ← eval_with_fuel (fuel - 1) σ Δ  e₂
        evalIntegerOp op v₁ v₂
      else
        none

  | Expr.boolExpr e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval_with_fuel (fuel - 1) σ Δ  e₁
        let v₂ ← eval_with_fuel (fuel - 1) σ Δ  e₂
        let b ← evalBoolOp op v₁ v₂
        pure (Value.vBool b)
      else
        none

  | Expr.binRel e₁ op e₂ => do
      if fuel > 0 then
        let v₁ ← eval_with_fuel (fuel - 1) σ Δ  e₁
        let v₂ ← eval_with_fuel (fuel - 1) σ Δ  e₂
        let b ← evalRelOp op v₁ v₂
        pure (Value.vBool b)
      else
        none

  -- E-PRODCONS
  | Expr.prodCons es     => do
      if fuel > 0 then
        let vs ← es.mapM (eval_with_fuel (fuel - 1) σ Δ )
        pure (Value.vProd vs)
      else
        none

  | Expr.prodIdx e i     => do
      if fuel > 0 then
        let v ← eval_with_fuel (fuel - 1) σ Δ  e
        match v with
        | Value.vProd vs => vs[i]?
        | _              => none
      else
        none

  | Expr.arrCons h t     => do
      if fuel > 0 then
        let vh ← eval_with_fuel (fuel - 1) σ Δ  h
        let vt ← eval_with_fuel (fuel - 1) σ Δ  t
        match vt with
        | Value.vArr vs => pure (Value.vArr (vh :: vs))
        | _             => pure (Value.vArr ([vh, vt]))
      else
        none

  | Expr.arrLen e        => do
      if fuel > 0 then
        let v ← eval_with_fuel (fuel - 1) σ Δ  e
        match v with
        | Value.vArr vs => pure (Value.vInt vs.length)
        | _             => none
      else
        none

  | Expr.arrIdx a i      => do
      if fuel > 0 then
        let va ← eval_with_fuel (fuel - 1) σ Δ  a
        let vi ← eval_with_fuel (fuel - 1) σ Δ  i
        match va, vi with
        | Value.vArr vs, Value.vInt j => vs[j.toNat]?
        | _, _                        => none
      else
        none

  -- E-ITER
  | Expr.iter sExpr eExpr fExpr accExpr => do
      if fuel > 0 then
        let sVal ← eval_with_fuel (fuel - 1) σ Δ  sExpr
        let eVal ← eval_with_fuel (fuel - 1) σ Δ  eExpr
        match sVal, eVal with
        | Value.vInt s, Value.vInt e => do
            let fVal ← eval_with_fuel (fuel - 1) σ Δ  fExpr
            let aVal ← eval_with_fuel (fuel - 1) σ Δ  accExpr
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
                      let fInner ← eval_with_fuel (fuel' - 1) σ₁ Δ body
                      match fInner with
                      | Value.vClosure y accBody σ₂ => do
                          -- apply resulting closure to accumulator
                          let σ₃ := updateVal σ₂ y acc
                          let newAcc ← eval_with_fuel (fuel' - 1) σ₃ Δ accBody
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
        --let vs ← args.mapM (eval (fuel - 1) σ Δ )
        let v := eval_with_fuel (fuel - 1) σ Δ  arg
        let c := Env.lookupCircuit Δ name
        --let σ' := (c.inputs.zip vs).foldl (fun env (⟨x,_⟩,v) => updateVal env x v) σ
        match v with
        | some vv => eval_with_fuel (fuel - 1) (updateVal σ name vv) Δ c.body
        | _ => none
      else
        none

  | _ => none
  -- The natural number fuel decreases in every recursive call
  termination_by fuel

@[simp]
def eval (σ : ValEnv) (Δ : CircuitEnv) : Expr → Option (Value) :=
  eval_with_fuel maximumRecursion σ Δ

end Eval
