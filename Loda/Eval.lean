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
  | Value.vF x, Value.vF y =>
    some $ Value.vF $
      match op with
      | FieldOp.add => x + y
      | FieldOp.sub => x - y
      | FieldOp.mul => x * y
      | FieldOp.div => x * y.inv
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
  | Value.vF i, Value.vF j =>
    some $ match op with
    | RelOp.eq => i.val % p = j.val % p
    | RelOp.lt => i.val % p < j.val % p
    | RelOp.le => i.val % p ≤ j.val % p
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

mutual
  inductive EvalProp : ValEnv → CircuitEnv → Expr → Value → Prop
    -- E‑VALUE
    | ConstF   {σ Δ v}  : EvalProp σ Δ (Expr.constF v) (Value.vF v)
    | ConstInt {σ Δ i}    : EvalProp σ Δ (Expr.constInt i) (Value.vInt i)
    | ConstBool{σ Δ b}    : EvalProp σ Δ (Expr.constBool b) (Value.vBool b)

    -- E‑VAR
    | Var      {σ Δ x v}  : lookupVal σ x = v → EvalProp σ Δ (Expr.var x) v

    -- E‑LAM
    | Lam      {σ Δ x τ body}  : EvalProp σ Δ (Expr.lam x τ body) (Value.vClosure x body σ)

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

    -- E‑INTBINOP
    | IntOp    {σ Δ e₁ e₂ op i₁ i₂ v}
        (ih₁ : EvalProp σ Δ e₁ (Value.vInt i₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vInt i₂))
        (r   : evalIntegerOp op (Value.vInt i₁) (Value.vInt i₂) = some v) :
        EvalProp σ Δ (Expr.intExpr e₁ op e₂) v

    -- E‑BOOLBINOP
    | BoolOp   {σ Δ e₁ e₂ op b₁ b₂ b}
        (ih₁ : EvalProp σ Δ e₁ (Value.vBool b₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vBool b₂))
        (bv  : evalBoolOp op (Value.vBool b₁) (Value.vBool b₂) = some b) :
        EvalProp σ Δ (Expr.boolExpr e₁ op e₂) (Value.vBool b)

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

    -- E‑PRODCONS
    --| ProdCons {σ Δ es vs}
    --    (ihs : List.Forall₂ (fun e v => EvalProp σ Δ e v) es vs) :
    --    EvalProp σ Δ (Expr.prodCons es) (Value.vProd vs)

    -- E‑PRODIDX
    | ProdIdx  {σ Δ e vs i v}
        (ih  : EvalProp σ Δ e (Value.vProd vs))
        (idx : vs[i]? = some v) :
        EvalProp σ Δ (Expr.prodIdx e i) v

    -- E‑ARRCONS
    | ArrCons  {σ Δ h t vh vt}
        (ihh : EvalProp σ Δ h vh)
        (iht : EvalProp σ Δ t (Value.vArr vt)):
        EvalProp σ Δ (Expr.arrCons h t) (Value.vArr (vh :: vt))

    -- E‑ARRLEN
    | ArrLen   {σ Δ e vs}
        (ih  : EvalProp σ Δ e (Value.vArr vs)) :
        EvalProp σ Δ (Expr.arrLen e) (Value.vInt vs.length)

    -- E‑ARRIDX
    | ArrIdx   {σ Δ a i vs j v}
        (iha : EvalProp σ Δ a (Value.vArr vs))
        (ihi : EvalProp σ Δ i (Value.vInt j))
        (idx : vs[j.toNat]? = some v) :
        EvalProp σ Δ (Expr.arrIdx a i) v

    -- E‑ITER
    | Iter {σ Δ s e f acc s' e' f' acc' v_final}
        -- Premise 1: Evaluate the start, end, function, and initial accumulator expressions.
        (ih_s : EvalProp σ Δ s (Value.vInt s'))
        (ih_e : EvalProp σ Δ e (Value.vInt e'))
        (ih_f : EvalProp σ Δ f f')
        (ih_acc : EvalProp σ Δ acc acc')
        -- Premise 2: The loop, starting with the evaluated values, produces a final value.
        (run_loop : EvalLoop σ Δ s' e' f' acc' v_final) :
        EvalProp σ Δ (Expr.iter s e f acc) v_final

    -- E‑CREF
    | CircRef  {σ Δ name arg v c out}
        (iha : EvalProp σ Δ arg v)
        (ic  : lookupCircuit Δ name = c)
        (ihb : EvalProp (updateVal σ name v) Δ c.body out) :
        EvalProp σ Δ (Expr.circRef name arg) out

  inductive EvalLoop : ValEnv → CircuitEnv → ℤ → ℤ → Value → Value → Value → Prop where
    /-- L-DONE: The loop terminates if the current index `i` is not less than the end index `e`. -/
    | Done {σ Δ i e f' acc} :
        i ≥ e →
        EvalLoop σ Δ i e f' acc acc

    /-- L-STEP: A single step of the loop. -/
    | Step {σ Δ i e f' acc acc_next final_acc x body_f σ_f f_inner y body_acc σ_acc} :
        -- Condition: The loop continues if `i < e`.
        i < e →
        -- Premise 1: `f'` must be a closure.
        (h_f_closure : f' = Value.vClosure x body_f σ_f) →
        -- Premise 2: Evaluate the application of `f'` to the current index `i`.
        -- The result `f_inner` is expected to be another closure.
        (ih_f_inner : EvalProp (updateVal σ_f x (Value.vInt i)) Δ body_f f_inner) →
        -- Premise 3: The result of the first application must also be a closure.
        (h_inner_closure : f_inner = Value.vClosure y body_acc σ_acc) →
        -- Premise 4: Evaluate the application of the inner closure to the current accumulator `acc`.
        -- The result is the accumulator for the next step, `acc_next`.
        (ih_acc_next : EvalProp (updateVal σ_acc y acc) Δ body_acc acc_next) →
        -- Premise 5: The rest of the loop evaluates correctly from the next state.
        (ih_loop : EvalLoop σ Δ (i + 1) e f' acc_next final_acc) →
        EvalLoop σ Δ i e f' acc final_acc
end

/--
  Evaluate an expression `e` under a valuation environment `σ`,
  a circuit environment `Δ`, and a fuel bound `fuel`.
  Returns `none` if evaluation gets stuck or fuel is exhausted.
-/
@[simp]
def eval_with_fuel (fuel: ℕ) (σ : ValEnv) (Δ : CircuitEnv) : Expr → Option (Value)
  -- E-VALUE
  | Expr.constF v      => pure (Value.vF v)
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

  | Expr.assertE e₁ e₂ => do
      if fuel > 0 then
        let v₁ ← eval_with_fuel (fuel - 1) σ Δ  e₁
        let v₂ ← eval_with_fuel (fuel - 1) σ Δ  e₂
        let b ← evalRelOp RelOp.eq v₁ v₂
        if b then
          pure (Value.vBool b)
        else
          none
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
