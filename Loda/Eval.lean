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
  | Value.vF x, Value.vF y =>
    some $ Value.vF $
      match op with
      | FieldOp.add => x + y
      | FieldOp.sub => x - y
      | FieldOp.mul => x * y
      | FieldOp.div => x * y.inv
  | _, _ => none

/-- Evaluate a relational operator `op` on two `Value` arguments. -/
@[simp]
def evalRelOp (op: RelOp) : Value → Value → Option Bool
  | Value.vF i, Value.vF j =>
    some $ match op with
    | RelOp.eq => i = j
    | RelOp.lt => i.val % p < j.val % p
    | RelOp.le => i.val % p ≤ j.val % p
  | _, _ => none

/-- Evaluate a boolean operator `op` on two `Value.bool` arguments. -/
@[simp]
def evalBoolOp (op : BooleanOp) : Value → Value → Option Bool
  | Value.vBool x, Value.vBool y =>
    some $ match op with
    | BooleanOp.and => x && y
    | BooleanOp.or  => x || y
  | _, _ => none

mutual
  inductive EvalProp : ValEnv → CircuitEnv → Expr → Value → Prop
    -- E‑VALUE
    | ConstF        {σ Δ v} : EvalProp σ Δ (Expr.constF v) (Value.vF v)
    | ConstBool     {σ Δ b} : EvalProp σ Δ (Expr.constBool b) (Value.vBool b)

    -- E-NONDET
    | NonDet        {σ Δ v} : EvalProp σ Δ (Expr.wildcard) (Value.vF v)

    -- E‑VAR
    | Var         {σ Δ x v} : lookupVal σ x = v → EvalProp σ Δ (Expr.var x) v

    -- E‑LAM
    | Lam    {σ Δ x τ body} : EvalProp σ Δ (Expr.lam x τ body) (Value.vClosure x body σ)

    -- E‑LET
    | Let      {σ Δ x e₁ e₂ v₁ v₂}
        (ih₁ : EvalProp σ Δ e₁ v₁)
        (ih₂ : EvalProp (updateVal σ x v₁) Δ e₂ v₂) :
        EvalProp σ Δ (Expr.letIn x e₁ e₂) v₂

    -- E‑APP
    | App      {σ Δ f a x body σ' va vb}
        (ih_f : EvalProp σ Δ f (Value.vClosure x body σ'))
        (ih_a : EvalProp σ Δ a va)
        (ih_b : EvalProp (updateVal σ' x va) Δ body vb) :
        EvalProp σ Δ (Expr.app f a) vb

    -- E‑FBINOP
    | FBinOp   {σ Δ e₁ e₂ op i₁ i₂ v}
        (ih₁ : EvalProp σ Δ e₁ (Value.vF i₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vF i₂))
        (r   : evalFieldOp op (Value.vF i₁) (Value.vF i₂) = some v) :
        EvalProp σ Δ (Expr.fieldExpr e₁ op e₂) v

    -- E‑BOOLBINOP
    | BoolOp   {σ Δ e₁ e₂ op b₁ b₂ b}
        (ih₁ : EvalProp σ Δ e₁ (Value.vBool b₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vBool b₂))
        (bv  : evalBoolOp op (Value.vBool b₁) (Value.vBool b₂) = some b) :
        EvalProp σ Δ (Expr.boolExpr e₁ op e₂) (Value.vBool b)

    -- E-BRANCH
    | IfTrue {σ Δ c e₁ e₂ v₁}
        (ihc : EvalProp σ Δ c (Value.vBool true))
        (ih₁ : EvalProp σ Δ e₁ v₁):
        EvalProp σ Δ (Expr.branch c e₁ e₂) (v₁)

    | IfFalse {σ Δ c e₁ e₂ v₂}
        (ihc : EvalProp σ Δ c (Value.vBool false))
        (ih₁ : EvalProp σ Δ e₂ v₂):
        EvalProp σ Δ (Expr.branch c e₁ e₂) (v₂)

    -- E‑ASSERT
    | Assert   {σ Δ e₁ e₂ v₁ v₂ b}
        (ih₁ : EvalProp σ Δ e₁ v₁)
        (ih₂ : EvalProp σ Δ e₂ v₂)
        (ok  : evalRelOp RelOp.eq v₁ v₂ = some b) :
        EvalProp σ Δ (Expr.assertE e₁ e₂) (Value.vBool b)

    -- E‑REL
    | Rel      {σ Δ e₁ e₂ op v₁ v₂ b}
        (ih₁ : EvalProp σ Δ e₁ v₁)
        (ih₂ : EvalProp σ Δ e₂ v₂)
        (r   : evalRelOp op v₁ v₂ = some b) :
        EvalProp σ Δ (Expr.binRel e₁ op e₂) (Value.vBool b)

    -- E‑ARRCONS
    | ArrConsArr {σ Δ h t vh vs}
        (ihh : EvalProp σ Δ h vh)
        (iht : EvalProp σ Δ t (Value.vArr vs)) :
        EvalProp σ Δ (Expr.arrCons h t) (Value.vArr (vh :: vs))

    | ArrConsElem {σ Δ h t vh vt}
        (ihh : EvalProp σ Δ h vh)
        (iht : EvalProp σ Δ t vt)
        (ne   : ¬ ∃ vs, vt = Value.vArr vs) :
        EvalProp σ Δ (Expr.arrCons h t) (Value.vArr [vh, vt])

    -- E‑ARRIDX
    | ArrIdx {σ Δ a i vs j v}
        (iha : EvalProp σ Δ a (Value.vArr vs))
        (ihi : EvalProp σ Δ i (Value.vF j))
        (idx : vs[j.toNat]? = some v) :
        EvalProp σ Δ (Expr.arrIdx a i) v

    -- E‑ITER
    | Iter {σ Δ s e f acc s' e' f' acc' v_final}
        -- Premise 1: Evaluate the start, end, function, and initial accumulator expressions.
        (ih_s : EvalProp σ Δ s (Value.vF s'))
        (ih_e : EvalProp σ Δ e (Value.vF e'))
        (ih_f : EvalProp σ Δ f f')
        (ih_acc : EvalProp σ Δ acc acc')
        -- Premise 2: The loop, starting with the evaluated values, produces a final value.
        (run_loop : EvalLoop σ Δ s'.toNat e'.toNat f' acc' v_final) :
        EvalProp σ Δ (Expr.iter s e f acc) v_final

    -- E‑CREF
    | CircRef  {σ Δ name arg v c out}
        (iha : EvalProp σ Δ arg v)
        (ic  : lookupCircuit Δ name = c)
        (ihb : EvalProp (updateVal σ name v) Δ c.body out) :
        EvalProp σ Δ (Expr.circRef name arg) out

  inductive EvalLoop : ValEnv → CircuitEnv → F → F → Value → Value → Value → Prop where
    /-- L-DONE: The loop terminates if the current index `i` is not less than the end index `e`. -/
    | Done {σ Δ i e f' acc} :
        i.toNat ≥ e.toNat →
        EvalLoop σ Δ i e f' acc acc

    /-- L-STEP: A single step of the loop. -/
    | Step {σ Δ i e f' acc acc_next final_acc x body_f σ_f f_inner y body_acc σ_acc} :
        -- Condition: The loop continues if `i < e`.
        i.toNat < e.toNat →
        -- Premise 1: `f'` must be a closure.
        (h_f_closure : f' = Value.vClosure x body_f σ_f) →
        -- Premise 2: Evaluate the application of `f'` to the current index `i`.
        -- The result `f_inner` is expected to be another closure.
        (ih_f_inner : EvalProp (updateVal σ_f x (Value.vF i)) Δ body_f f_inner) →
        -- Premise 3: The result of the first application must also be a closure.
        (h_inner_closure : f_inner = Value.vClosure y body_acc σ_acc) →
        -- Premise 4: Evaluate the application of the inner closure to the current accumulator `acc`.
        -- The result is the accumulator for the next step, `acc_next`.
        (ih_acc_next : EvalProp (updateVal σ_acc y acc) Δ body_acc acc_next) →
        -- Premise 5: The rest of the loop evaluates correctly from the next state.
        (ih_loop : EvalLoop σ Δ (i + 1) e f' acc_next final_acc) →
        EvalLoop σ Δ i e f' acc final_acc
end

end Eval
