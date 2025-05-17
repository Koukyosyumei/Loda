import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

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
    | iter        : String → -- index binder
                    Expr → -- start s
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
    | refin    : Value → Ty → Prop → Ty   -- {ν : T | ϕ}
    | func     : String → Ty → Ty → Ty    -- x: τ₁ → τ₂
    --deriving DecidableEq, Repr
end

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
def evalRelOp : RelOp → Value → Value → Option Bool
  | RelOp.eq,  Value.vInt i, Value.vInt j => pure (i = j)
  | RelOp.lt,  Value.vInt i, Value.vInt j => pure (i < j)
  | RelOp.le,  Value.vInt i, Value.vInt j => pure (i ≤ j)
  | _,         _,            _            => none

/-- Evaluate an expression in a given environment. -/
partial def eval (σ : Env) (δ : CircuitEnv) : Expr → Option (Value)
  -- E-VALUE
  | Expr.constF _ v      => pure (Value.vF _ v)
  | Expr.constInt i      => pure (Value.vInt i)
  | Expr.constBool b     => pure (Value.vBool b)
  -- E-VAR
  | Expr.var x           => pure (σ x)
  | Expr.letIn x e₁ e₂   => do
    let v₁ ← eval σ δ e₁
    let σ' := set σ x v₁
    eval σ' δ e₂
  -- E-LAM
  | Expr.lam x _ e       => pure (Value.vClosure x e σ)
  -- E-APP
  | Expr.app f e         => do
      let vf ← eval σ δ f
      let va ← eval σ δ e
      match vf with
      | Value.vClosure x body σ' =>
        let σ'' := set σ' x va
        eval σ'' δ body
      | _ => none
  -- E-FBINOP
  | Expr.binRel e₁ op e₂ => do
      let v₁ ← eval σ δ e₁
      let v₂ ← eval σ δ e₂
      let b ← evalRelOp op v₁ v₂
      pure (Value.vBool b)
  -- E-PRODCONS
  | Expr.prodCons es     => do
      let vs ← es.mapM (eval σ δ)
      pure (Value.vProd vs)
  | Expr.prodIdx e i     => do
      let v ← eval σ δ e
      match v with
      | Value.vProd vs => vs[i]?
      | _              => none
  | Expr.arrCons h t     => do
      let vh ← eval σ δ h
      let vt ← eval σ δ t
      match vt with
      | Value.vArr vs => pure (Value.vArr (vh :: vs))
      | _             => none
  | Expr.arrLen e        => do
      let v ← eval σ δ e
      match v with
      | Value.vArr vs => pure (Value.vInt vs.length)
      | _             => none
  | Expr.arrIdx a i      => do
      let va ← eval σ δ a
      let vi ← eval σ δ i
      match va, vi with
      | Value.vArr vs, Value.vInt j => vs[j.toNat]?
      | _, _                        => none
  -- E-ITER
  | Expr.iter _ sExpr eExpr fExpr accExpr => do
      let sVal ← eval σ δ sExpr
      let eVal ← eval σ δ eExpr
      match sVal, eVal with
      | Value.vInt s, Value.vInt e => do
          let fVal ← eval σ δ fExpr
          let aVal ← eval σ δ accExpr
          let rec loop (i : ℤ) (acc : Value) : Option Value :=
            if i ≥ e then pure acc else
            match fVal with
            | Value.vClosure x body σ' => do
                -- apply f to index i
                let σ1 := set σ' x (Value.vInt i)
                let fInner ← eval σ1 δ body
                match fInner with
                | Value.vClosure y accBody σ2 => do
                    -- apply resulting closure to accumulator
                    let σ3 := set σ2 y acc
                    let newAcc ← eval σ3 δ accBody
                    loop (i+1) newAcc
                | _ => none
            | _ => none
          loop s aVal
      | _, _ => none
  -- E-CREF
  | Expr.circRef name args => do
      let vs ← args.mapM (eval σ δ )
      let c := δ name
      let σ' := (c.inputs.zip vs).foldl (fun env (⟨x,_⟩,v) => set env x v) σ
      eval σ' δ c.body
  | _ => none
