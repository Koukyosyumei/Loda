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
    | refin    : String → Ty → Prop → Ty  -- {ν : T | ϕ}
    | func     : String → Ty → Ty → Ty       -- x: τ₁ → τ₂
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
  | Expr.iter idx sExpr eExpr fExpr accExpr => do
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

/-- Type Environment. -/
def TyEnv := String -> Ty

def setTy (Γ : TyEnv) (x : String) (v: Ty) : TyEnv :=
  fun y => if y = x then v else Γ y

inductive PairwiseProd (R : Ty → Ty → Prop) : List (Ty × Ty) → Prop
| nil : PairwiseProd R []
| cons {ty1 ty2 : Ty} {rest : List (Ty × Ty)} :
    R ty1 ty2 →
    PairwiseProd R rest →
    PairwiseProd R ((ty1, ty2) :: rest)

/-- Subtyping judgment for CODA types -/
inductive SubtypeJudgment : TyEnv → Ty → Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {Γ : TyEnv} {τ : Ty} :
      SubtypeJudgment Γ τ τ
  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {Γ : TyEnv} {τ₁ τ₂ τ₃ : Ty} :
      SubtypeJudgment Γ τ₁ τ₂ →
      SubtypeJudgment Γ τ₂ τ₃ →
      SubtypeJudgment Γ τ₁ τ₃
  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {Γ : TyEnv} {T₁ T₂ : Ty} {φ₁ φ₂ : Prop} :
      SubtypeJudgment Γ T₁ T₂ →
      (φ₁ → φ₂) →
      SubtypeJudgment Γ (Ty.refin "ν" T₁ φ₁) (Ty.refin "ν" T₂ φ₂)

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {Γ : TyEnv} {x y : String} {τx τy τr τs : Ty} :
      SubtypeJudgment Γ τy τx →
      -- Using a fresh variable z to avoid capture
      --let z := "fresh"; -- In real code, generate a truly fresh variable
      --SubtypeJudgment (setTy Γ z τx) (subst τr x (Expr.var z)) (subst τs y (Expr.var z)) →
      SubtypeJudgment Γ (Ty.func x τx τr) (Ty.func y τy τs)

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {Γ : TyEnv} {T₁ T₂ : Ty} :
      SubtypeJudgment Γ T₁ T₂ →
      SubtypeJudgment Γ (Ty.arr T₁) (Ty.arr T₂)

  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {Γ : TyEnv} {Ts₁ Ts₂ : List Ty} :
      Ts₁.length = Ts₂.length →
      PairwiseProd (SubtypeJudgment Γ) (List.zip Ts₁ Ts₂) →
      SubtypeJudgment Γ (Ty.prod Ts₁) (Ty.prod Ts₂)

inductive TypeJudgment: TyEnv -> Expr -> Ty -> Prop where
  | T_Var {Γ x T φ}:
      Γ x = (Ty.refin "v" T φ) →
    TypeJudgment Γ (Expr.var x) (Ty.refin "v" T (Formula.rel (Expr.var "v") RelOp.eq (Expr.var x)))

  | T_Nondet {Γ p} :
    TypeJudgment Γ Expr.wildcard (Ty.field p)

  | T_ConstF {Γ p f} :
    TypeJudgment Γ (Expr.constF p f) (Ty.field p)

  | T_Assert {Γ e1 e2 p} :
    TypeJudgment Γ e1 (Ty.field p) →
    TypeJudgment Γ e2 (Ty.field p) →
    TypeJudgment Γ (Expr.assertE e1 e2) (Ty.refin "v" (Ty.field p) (Formula.rel e1 RelOp.eq e2))

  | T_BinOpField {Γ e1 e2 p} :
    TypeJudgment Γ e1 (Ty.field p) →
    TypeJudgment Γ e2 (Ty.field p) →
    TypeJudgment Γ (Expr.binRel e1 RelOp.eq e2) (Ty.refin "v" (Ty.field p) (Formula.rel (Expr.var "v") RelOp.eq (Expr.binRel e1 RelOp.eq e2)))

  | T_Abs {Γ x τ₁ e τ₂} :
    TypeJudgment (setTy Γ x τ₁) e τ₂ →
    TypeJudgment Γ (Expr.lam x τ₁ e) (Ty.func "_" τ₁ τ₂)

  | T_App {Γ x₁ x₂ s τ₁ τ₂} :
      -- x₁ : (x₁ : τ₁ → τ₂)
      TypeJudgment Γ x₁ (Ty.func s τ₁ τ₂) →
      -- x₂ : τ1
      TypeJudgment Γ x₂ τ₁ →
      -- result: τ2 with s ↦ x₂
      TypeJudgment Γ (Expr.app x₁ x₂) τ₂
