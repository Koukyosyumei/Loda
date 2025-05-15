import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Std.Data.HashMap

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

/-- Binary relations =⊘. -/
inductive RelOp where
  | eq   -- =
  | lt   -- <
  | le   -- ≤
  deriving DecidableEq, Repr

mutual
  /-- AST of CODA expressions. -/
  inductive Expr where
    | constF      : ∀ p, F p → Expr         -- field constant
    | constInt    : Int → Expr               -- integer constant
    | constBool   : Bool → Expr              -- boolean constant
    | var         : String → Expr            -- variable x
    | wildcard    : Expr                     -- ⋆
    | assertE     : Expr → Expr → Expr       -- assert e₁ = e₂
    | binRel      : Expr → RelOp → Expr → Expr -- e₁ ⊘ e₂
    | circRef     : String → List Expr → Expr -- #C e₁ ... eₙ
    | arrCons     : Expr → Expr → Expr       -- e₁ :: e₂
    | arrMap      : Expr → Expr → Expr       -- map e₁ e₂
    | arrLen      : Expr → Expr              -- length e
    | arrIdx      : Expr → Expr → Expr       -- e₁[e₂]
    | prodCons    : List Expr → Expr         -- (e₁, ..., eₙ)
    | prodMatch   : Expr → List String → Expr → Expr -- match e with (x₁,...,xₙ)→e
    | prodIdx     : Expr → Nat → Expr        -- e.i
    | lam         : String → Ty → Expr → Expr -- λx : τ. e
    | app         : Expr → Expr → Expr       -- e₁ e₂
    | letIn       : String → Expr → Expr → Expr -- let x = e₁ in e₂
    | iter        : String → -- index binder
                    Expr → -- start s
                    Expr → -- end e
                    Expr → -- step f
                    Expr → -- acc a
                    Expr      -- iteration body result
    --deriving Repr

  /-- Logical qualifiers/formulae for refinement types. -/
  inductive Formula where
    | top      : Formula
    | bot      : Formula
    | ff       : Formula  -- false
    | tt       : Formula  -- true
    | rel      : Expr → RelOp → Expr → Formula
    | not      : Formula → Formula
    | and      : Formula → Formula → Formula
    | or       : Formula → Formula → Formula
    | forallB  : String → Nat → Formula → Formula -- ∀ i ∈ [0, k). φ
    --deriving Repr

  /-- Basic Types in CODA. -/
  inductive Ty where
    | field    : ℕ → Ty             -- F p
    | int      : Ty                 -- Int
    | bool     : Ty                 -- Bool
    | prod     : List Ty → Ty       -- T₁ × ... × Tₙ (unit is prod [])
    | arr      : Ty → Ty            -- [T]
    | refin    : String → Ty → Formula → Ty  -- {ν : T | ϕ}
    --deriving DecidableEq, Repr
end

/-- Circuit Declaration. -/
structure Circuit where
  name    : String
  inputs  : List (String × Ty)
  output  : Ty
  body    : Expr

/-- Values of CODA. -/
inductive Value where
  | vF       : ∀ p, F p → Value
  | vInt     : Int → Value
  | vBool    : Bool → Value
  | vProd    : List Value → Value
  | vArr     : List Value → Value
  | vClosure : String → Expr → (String → Value) → Value

/-- Valuation (environment). -/
def Env := String -> Value

/-- Evaluate a binary relation. -/
def evalRelOp : RelOp → Value → Value → Option Bool
  | RelOp.eq,  Value.vInt i, Value.vInt j => pure (i = j)
  | RelOp.lt,  Value.vInt i, Value.vInt j => pure (i < j)
  | RelOp.le,  Value.vInt i, Value.vInt j => pure (i ≤ j)
  | _,         _,            _            => none

def set (σ: Env) (x : String) (v: Value) : Env :=
  fun y => if y = x then v else σ y

/-- Evaluate an expression in a given environment. -/
partial def eval (σ : Env) : Expr → Option (Value)
  -- E-VALUE
  | Expr.constF _ v      => pure (Value.vF _ v)
  | Expr.constInt i      => pure (Value.vInt i)
  | Expr.constBool b     => pure (Value.vBool b)
  -- E-VAR
  | Expr.var x           => pure (σ x)
  | Expr.letIn x e₁ e₂   => do
    let v₁ ← eval σ e₁
    let σ' := set σ x v₁
    eval σ' e₂
  -- E-LAM
  | Expr.lam x _ e       => pure (Value.vClosure x e σ)
  -- E-APP
  | Expr.app f e         => do
      let vf ← eval σ f
      let va ← eval σ e
      match vf with
      | Value.vClosure x body σ' =>
        let σ'' := set σ' x va
        eval σ'' body
      | _ => none
  -- E-FBINOP
  | Expr.binRel e₁ op e₂ => do
      let v₁ ← eval σ e₁
      let v₂ ← eval σ e₂
      let b ← evalRelOp op v₁ v₂
      pure (Value.vBool b)
  -- E-PRODCONS
  | Expr.prodCons es     => do
      let vs ← es.mapM (eval σ)
      pure (Value.vProd vs)
  | Expr.prodIdx e i     => do
      let v ← eval σ e
      match v with
      | Value.vProd vs => vs[i]?
      | _              => none
  | Expr.arrCons h t     => do
      let vh ← eval σ h
      let vt ← eval σ t
      match vt with
      | Value.vArr vs => pure (Value.vArr (vh :: vs))
      | _             => none
  | Expr.arrLen e        => do
      let v ← eval σ e
      match v with
      | Value.vArr vs => pure (Value.vInt vs.length)
      | _             => none
  | Expr.arrIdx a i      => do
      let va ← eval σ a
      let vi ← eval σ i
      match va, vi with
      | Value.vArr vs, Value.vInt j => vs[j.toNat]?
      | _, _                        => none
  -- E-ITER
  | Expr.iter idx sExpr eExpr fExpr accExpr => do
      let sVal ← eval σ sExpr
      let eVal ← eval σ eExpr
      match sVal, eVal with
      | Value.vInt s, Value.vInt e => do
          let fVal ← eval σ fExpr
          let aVal ← eval σ accExpr
          let rec loop (i : ℤ) (acc : Value) : Option Value :=
            if i ≥ e then pure acc else
            match fVal with
            | Value.vClosure x body σ' => do
                -- apply f to index i
                let σ1 := set σ' x (Value.vInt i)
                let fInner ← eval σ1 body
                match fInner with
                | Value.vClosure y accBody σ2 => do
                    -- apply resulting closure to accumulator
                    let σ3 := set σ2 y acc
                    let newAcc ← eval σ3 accBody
                    loop (i+1) newAcc
                | _ => none
            | _ => none
          loop s aVal
      | _, _ => none
  | _ => none
