import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

import Loda.Field

namespace Ast

variable {p : ℕ} [Fact p.Prime]


/-- Field operators =⊙. -/
inductive BooleanOp where
  | and   -- ∧
  | or   -- ∨
  deriving DecidableEq, Repr

/-- Field operators =⊕. -/
inductive IntegerOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  deriving DecidableEq, Repr

/-- Field operators =⊗. -/
inductive FieldOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | div   -- /
  deriving DecidableEq, Repr

/-- Binary relations =⊘. -/
inductive RelOp where
  | eq   -- =
  | lt   -- <
  | le   -- ≤
  deriving DecidableEq, Repr

mutual
  /-- AST of CODA expressions. -/
  inductive Expr where
    | constF      : ∀ p, F p → Expr                  -- field constant
    | constInt    : Int → Expr                       -- integer constant
    | constBool   : Bool → Expr                      -- boolean constant
    | var         : String → Expr                    -- variable x
    | wildcard    : Expr                             -- ⋆
    | assertE     : Expr → Expr → Expr               -- assert e₁ = e₂
    | boolExpr    : Expr → BooleanOp → Expr → Expr
    | intExpr     : Expr → IntegerOp → Expr → Expr
    | fieldExpr   : Expr → FieldOp → Expr → Expr
    | binRel      : Expr → RelOp → Expr → Expr       -- e₁ ⊘ e₂
    | circRef     : String → List Expr → Expr        -- #C e₁ ... eₙ
    | arrCons     : Expr → Expr → Expr               -- e₁ :: e₂
    | arrMap      : Expr → Expr → Expr               -- map e₁ e₂
    | arrLen      : Expr → Expr                      -- length e
    | arrIdx      : Expr → Expr → Expr               -- e₁[e₂]
    | prodCons    : List Expr → Expr                 -- (e₁, ..., eₙ)
    | prodMatch   : Expr → List String → Expr → Expr -- match e with (x₁,...,xₙ)→e
    | prodIdx     : Expr → Nat → Expr                -- e.i
    | lam         : String → Ty → Expr → Expr        -- λx : τ. e
    | app         : Expr → Expr → Expr               -- e₁ e₂
    | letIn       : String → Expr → Expr → Expr      -- let x = e₁ in e₂
    | iter        : Expr → -- start s
                    Expr → -- end e
                    Expr → -- step f
                    Expr → -- acc a
                    Expr      -- iteration body result

  /-- Values of CODA. -/
  inductive Value where
    | vF       : ∀ p, F p → Value
    | vStar    : Value
    | vInt     : Int → Value
    | vBool    : Bool → Value
    | vProd    : List Value → Value
    | vArr     : List Value → Value
    | vClosure : String → Expr → (String → Value) → Value

  /-- Basic Types in CODA. -/
  inductive Ty where
    | unit     : Ty
    | field    : ℕ → Ty                   -- F p
    | int      : Ty                       -- Int
    | bool     : Ty                       -- Bool
    | prod     : List Ty → Ty             -- T₁ × ... × Tₙ (unit is prod [])
    | arr      : Ty → Ty                  -- [T]
    | refin    : Ty → Prop → Ty   -- {ν : T | ϕ}
    | func     : String → Ty → Ty → Ty    -- x: τ₁ → τ₂
    --deriving DecidableEq, Repr
end


open Std (Format)
instance : Repr Value where
  reprPrec
    | Value.vF p x, _ => Format.text s!"F{p}.mk {x.val}"
    | Value.vStar, _    => Format.text "*"
    | Value.vInt i, _   => Format.text (toString i)
    | Value.vBool b, _  => Format.text (toString b)
    | Value.vProd vs, _ => Format.text "Prod"
    | Value.vArr vs, _  => Format.text "Arr"
    | Value.vClosure name _ _, _ => Format.text s!"<closure {name}>"

/-- Circuit Declaration. -/
structure Circuit where
  name    : String
  inputs  : List (String × Ty)
  output  : Ty
  body    : Expr

def beq : Value → Value → Bool
  | Value.vF p₁ x, Value.vF p₂ y        => p₁ = p₂ ∧ x.val % p₁ = y.val % p₁
  | Value.vF _ _, Value.vStar           => true
  | Value.vStar, Value.vF _ _           => true
  | Value.vInt i₁, Value.vInt i₂        => i₁ = i₂
  | Value.vBool b₁, Value.vBool b₂      => b₁ = b₂
  | Value.vProd _, Value.vProd _        => false --(xs.zip ys).all (fun (x, y) => (x = y))
  | Value.vArr _, Value.vArr _          => false
  | Value.vClosure _ _ _, Value.vClosure _ _ _ => false -- closures not comparable
  | _, _                    => false

instance : BEq Value where
  beq := beq

/-- Valuation (environment). -/
def Env := String -> Value

def set (σ: Env) (x : String) (v: Value) : Env :=
  fun y => if y = x then v else σ y

/-- Global circuit definitions; populate this map with your circuits. -/
def CircuitEnv := String -> Circuit

/-- Evaluate a binary relation. -/
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

def evalIntegerOp: IntegerOp → Value → Value → Option Value
  | IntegerOp.add, Value.vInt x, Value.vInt y => some (Value.vInt (x + y))
  | IntegerOp.sub, Value.vInt x, Value.vInt y => some (Value.vInt (x - y))
  | IntegerOp.mul, Value.vInt x, Value.vInt y => some (Value.vInt (x * y))
  | _, _, _ => none

/-- Evaluate a binary relation. -/
def evalRelOp : RelOp → Value → Value → Option Bool
  | RelOp.eq,  Value.vInt i, Value.vInt j => pure (i = j)
  | RelOp.lt,  Value.vInt i, Value.vInt j => pure (i < j)
  | RelOp.le,  Value.vInt i, Value.vInt j => pure (i ≤ j)
  | _,         _,            _            => none

/-- Evaluate an expression in a given environment. -/
@[simp]
def eval (σ : Env) (δ : CircuitEnv) (ctr: ℕ) : Expr → Option (Value)
  -- E-VALUE
  | Expr.constF p v      => pure (Value.vF p v)
  | Expr.constInt i      => pure (Value.vInt i)
  | Expr.constBool b     => pure (Value.vBool b)

  -- E-VAR
  | Expr.var x           => pure (σ x)

  | Expr.letIn x e₁ e₂   => do
    if ctr > 0 then
      let v₁ ← eval σ δ (ctr -1) e₁
      let σ' := set σ x v₁
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
          let σ'' := set σ' x va
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
                      let σ1 := set σ' x (Value.vInt i)
                      let fInner ← eval σ1 δ (fuel - 1) body
                      match fInner with
                      | Value.vClosure y accBody σ2 => do
                          -- apply resulting closure to accumulator
                          let σ3 := set σ2 y acc
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
        let σ' := (c.inputs.zip vs).foldl (fun env (⟨x,_⟩,v) => set env x v) σ
        eval σ' δ (ctr - 1) c.body
      else
        none

  | _ => none
  -- The natural number ctr decreases in every recursive call
  termination_by ctr
end Ast
