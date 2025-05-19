import Loda.Ast
import Loda.Circuit
import Loda.Env

open Ast
open Circuit
open Env

namespace Eval

/-- Evaluate a binary relation. -/
@[simp]
def evalFieldOp : FieldOp → Value → Value → Option Value
  | FieldOp.add,  Value.vF p₁ x, Value.vF p₂ y =>
    if h : p₁ = p₂ then
      some (Value.vF p₁ (x + (Eq.mp (by rw [h]) y)))
    else
      none
  | FieldOp.sub,  Value.vF p₁ x, Value.vF p₂ y =>
    if h : p₁ = p₂ then
      some (Value.vF p₁ (x - (Eq.mp (by rw [h]) y)))
    else
      none
  | FieldOp.mul,  Value.vF p₁ x, Value.vF p₂ y =>
    if h : p₁ = p₂ then
      some (Value.vF p₁ (x * (Eq.mp (by rw [h]) y)))
    else
      none
  | FieldOp.div,  Value.vF p₁ x, Value.vF p₂ y =>
    if h : p₁ = p₂ then
      some (Value.vF p₁ (x * ((Eq.mp (by rw [h]) y.inv))))
    else
      none
  | _,         _,            _            => none

@[simp]
def evalIntegerOp: IntegerOp → Value → Value → Option Value
  | IntegerOp.add, Value.vInt x, Value.vInt y => some (Value.vInt (x + y))
  | IntegerOp.sub, Value.vInt x, Value.vInt y => some (Value.vInt (x - y))
  | IntegerOp.mul, Value.vInt x, Value.vInt y => some (Value.vInt (x * y))
  | _, _, _ => none

/-- Evaluate a binary relation. -/
@[simp]
def evalRelOp : RelOp → Value → Value → Option Bool
  | RelOp.eq,  Value.vF p₁ i, Value.vF p₂ j =>
    if h : p₁ = p₂ then
      some (i = (Eq.mp (by rw [h]) j))
    else
      none
  | RelOp.eq,  Value.vInt i, Value.vInt j => pure (i = j)
  | RelOp.lt,  Value.vInt i, Value.vInt j => pure (i < j)
  | RelOp.le,  Value.vInt i, Value.vInt j => pure (i ≤ j)
  | _,         _,            _            => none

/-- Evaluate an expression in a given environment. -/
@[simp]
def eval (σ : ValEnv) (δ : CircuitEnv) (ctr: ℕ) : Expr → Option (Value)
  -- E-VALUE
  | Expr.constF p v      => pure (Value.vF p v)
  | Expr.constInt i      => pure (Value.vInt i)
  | Expr.constBool b     => pure (Value.vBool b)

  -- E-VAR
  | Expr.var x           => pure (σ x)

  | Expr.letIn x e₁ e₂   => do
    if ctr > 0 then
      let v₁ ← eval σ δ (ctr -1) e₁
      let σ' := setVal σ x v₁
      eval σ' δ (ctr -1) e₂
    else
      none

  -- E-LAM
  | Expr.lam x _ e       => pure (Value.vClosure x e σ)

  -- E-APP
  | Expr.app f e         => do
      if ctr > 0 then
        let vf ← eval σ δ (ctr -1) f
        let va ← eval σ δ (ctr -1) e
        match vf with
        | Value.vClosure x body σ' =>
          let σ'' := setVal σ' x va
          eval σ'' δ (ctr -1) body
        | _ => none
      else
        none

  -- E-FBINOP
  | Expr.fieldExpr e₁ op e₂ => do
      if ctr > 0 then
        let v₁ ← eval σ δ (ctr - 1) e₁
        let v₂ ← eval σ δ (ctr - 1) e₂
        evalFieldOp op v₁ v₂
      else
        none

  | Expr.intExpr e₁ op e₂ => do
      if ctr > 0 then
        let v₁ ← eval σ δ (ctr - 1) e₁
        let v₂ ← eval σ δ (ctr - 1) e₂
        evalIntegerOp op v₁ v₂
      else
        none

  | Expr.binRel e₁ op e₂ => do
      if ctr > 0 then
        let v₁ ← eval σ δ (ctr - 1) e₁
        let v₂ ← eval σ δ (ctr - 1) e₂
        let b ← evalRelOp op v₁ v₂
        pure (Value.vBool b)
      else
        none


  -- E-PRODCONS
  | Expr.prodCons es     => do
      if ctr > 0 then
        let vs ← es.mapM (eval σ δ (ctr - 1))
        pure (Value.vProd vs)
      else
        none
  | Expr.prodIdx e i     => do
      if ctr > 0 then
        let v ← eval σ δ (ctr - 1) e
        match v with
        | Value.vProd vs => vs[i]?
        | _              => none
      else
        none

  | Expr.arrCons h t     => do
      if ctr > 0 then
        let vh ← eval σ δ (ctr - 1) h
        let vt ← eval σ δ (ctr - 1) t
        match vt with
        | Value.vArr vs => pure (Value.vArr (vh :: vs))
        | _             => pure (Value.vArr ([vh, vt]))
      else
        none
  | Expr.arrLen e        => do
      if ctr > 0 then
        let v ← eval σ δ (ctr - 1) e
        match v with
        | Value.vArr vs => pure (Value.vInt vs.length)
        | _             => none
      else
        none
  | Expr.arrIdx a i      => do
      if ctr > 0 then
        let va ← eval σ δ (ctr - 1) a
        let vi ← eval σ δ (ctr - 1) i
        match va, vi with
        | Value.vArr vs, Value.vInt j => vs[j.toNat]?
        | _, _                        => none
      else
        none

  -- E-ITER
  | Expr.iter sExpr eExpr fExpr accExpr => do
      if ctr > 0 then
        let sVal ← eval σ δ (ctr - 1) sExpr
        let eVal ← eval σ δ (ctr - 1) eExpr
        match sVal, eVal with
        | Value.vInt s, Value.vInt e => do
            let fVal ← eval σ δ (ctr - 1) fExpr
            let aVal ← eval σ δ (ctr - 1) accExpr
            let rec loop (i : ℤ) (fuel: ℕ) (acc : Value) : Option Value :=
              if fuel = 0 then
                none
              else
                if i ≥ e then pure acc else
                if (ctr - 1) > 0 then
                  match fVal with
                  | Value.vClosure x body σ' => do
                      -- apply f to index i
                      let σ1 := setVal σ' x (Value.vInt i)
                      let fInner ← eval σ1 δ (fuel - 1) body
                      match fInner with
                      | Value.vClosure y accBody σ2 => do
                          -- apply resulting closure to accumulator
                          let σ3 := setVal σ2 y acc
                          let newAcc ← eval σ3 δ (fuel - 1) accBody
                          loop (i+1) (fuel - 1) newAcc
                      | _ => none
                  | _ => none
                else
                  none
              termination_by fuel
            loop s (ctr - 1) aVal
        | _, _ => none
      else
        none

  -- E-CREF
  | Expr.circRef name args => do
      if ctr > 0 then
        let vs ← args.mapM (eval σ δ (ctr - 1))
        let c := δ name
        let σ' := (c.inputs.zip vs).foldl (fun env (⟨x,_⟩,v) => setVal env x v) σ
        eval σ' δ (ctr - 1) c.body
      else
        none

  | _ => none
  -- The natural number ctr decreases in every recursive call
  termination_by ctr

end Eval
