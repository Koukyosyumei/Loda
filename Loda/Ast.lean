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
    | field    : ℕ → Ty             -- F p
    | int      : Ty                 -- Int
    | bool     : Ty                 -- Bool
    | prod     : List Ty → Ty       -- T₁ × ... × Tₙ (unit is prod [])
    | arr      : Ty → Ty            -- [T]
    | refin    : Value → Ty → Prop → Ty  -- {ν : T | ϕ}
    | func     : String → Ty → Ty → Ty       -- x: τ₁ → τ₂
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

/-- Type Environment. -/
def TyEnv := String -> Ty

def setTy (Γ : TyEnv) (x : String) (v: Ty) : TyEnv :=
  fun y => if y = x then v else Γ y

/-- Subtyping judgment for CODA types -/
inductive SubtypeJudgment : Env -> TyEnv → Option Ty → Option Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {σ : Env} {Γ : TyEnv} {τ : Ty} :
      SubtypeJudgment σ Γ (pure τ) (pure τ)
  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {σ : Env} {Γ : TyEnv} {τ₁ τ₂ τ₃ : Ty} :
      SubtypeJudgment σ Γ (pure τ₁) (pure τ₂) →
      SubtypeJudgment σ Γ (pure τ₂) (pure τ₃) →
      SubtypeJudgment σ Γ (pure τ₁) (pure τ₃)
  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {σ : Env} {Γ : TyEnv} {T₁ T₂ : Ty} {φ₁ φ₂ : Prop} {v: Value} :
      SubtypeJudgment σ Γ (pure T₁) (pure T₂) →
      (φ₁ → φ₂) →
      SubtypeJudgment σ Γ (pure (Ty.refin v T₁ φ₁)) (pure (Ty.refin v T₂ φ₂))
  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {σ : Env} {Γ : TyEnv} {x y : String} {z : Value} {τx τy τr τs : Ty} :
      SubtypeJudgment σ Γ (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      -- SubtypeJudgment (set (set σ x z) y z) Γ τr τs →
      SubtypeJudgment σ Γ (pure τr) (pure τs) →
      SubtypeJudgment σ Γ (pure (Ty.func x τx τr)) (pure (Ty.func y τy τs))
  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {σ : Env} {Γ : TyEnv} {T₁ T₂ : Ty} :
      SubtypeJudgment σ Γ (pure T₁) (pure T₂) →
      SubtypeJudgment σ Γ (pure (Ty.arr T₁)) (pure (Ty.arr T₂))
  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {σ : Env} {Γ : TyEnv} {Ts₁ Ts₂ : List Ty} :
      Ts₁.length = Ts₂.length →
      --PairwiseProd (SubtypeJudgment σ Γ) (List.zip Ts₁ Ts₂) →
      (∀ i, i < Ts₁.length → SubtypeJudgment σ Γ Ts₁[i]? Ts₂[i]?) →
      SubtypeJudgment σ Γ (pure (Ty.prod Ts₁)) (pure (Ty.prod Ts₂))

inductive TypeJudgment: Env -> CircuitEnv -> TyEnv -> Expr -> Ty -> Prop where
  | T_Var {σ δ Γ x v T φ}:
      Γ x = (Ty.refin v T φ) →
    TypeJudgment σ δ Γ (Expr.var x) (Ty.refin v T (v = eval σ δ (Expr.var x)))

  | T_VarFunc {σ δ Γ f x τ₁ τ₂}:
      Γ f = (Ty.func x τ₁ τ₂) →
      TypeJudgment σ δ Γ (Expr.var f) (Ty.func x τ₁ τ₂)

  | T_Nondet {σ δ Γ p v} :
    TypeJudgment σ δ Γ Expr.wildcard (Ty.refin v (Ty.field p) True)

  | T_ConstF {σ δ Γ p f} :
    TypeJudgment σ δ Γ (Expr.constF p f) (Ty.field p)

  | T_Assert {σ δ Γ e1 e2 p v} :
    TypeJudgment σ δ Γ e1 (Ty.field p) →
    TypeJudgment σ δ Γ e2 (Ty.field p) →
    TypeJudgment σ δ Γ (Expr.assertE e1 e2) (Ty.refin v (Ty.field p) (eval σ δ e1 = eval σ δ e2))

  | T_BinOpField {σ δ Γ e1 e2 p v} :
    TypeJudgment σ δ Γ e1 (Ty.field p) →
    TypeJudgment σ δ Γ e2 (Ty.field p) →
    TypeJudgment σ δ Γ (Expr.binRel e1 RelOp.eq e2) (Ty.refin v (Ty.field p) (v = eval σ δ (Expr.binRel e1 RelOp.eq e2)))

  | T_Abs {σ δ Γ x τ₁ e τ₂} :
    TypeJudgment σ δ (setTy Γ x τ₁) e τ₂ →
    TypeJudgment σ δ Γ (Expr.lam x τ₁ e) (Ty.func "_" τ₁ τ₂)

  | T_App {σ δ Γ x₁ x₂ s τ₁ τ₂} :
      -- x₁ : (x₁ : τ₁ → τ₂)
      TypeJudgment σ δ Γ x₁ (Ty.func s τ₁ τ₂) →
      -- x₂ : τ1
      TypeJudgment σ δ Γ x₂ τ₁ →
      -- result: τ2 with s ↦ x₂
      TypeJudgment σ δ Γ (Expr.app x₁ x₂) τ₂

/-- Compilation values representing partially evaluated expressions. -/
inductive CompValue where
  | constF      : ∀ p, F p → CompValue         -- field constant
  | constInt    : Int → CompValue              -- integer constant
  | constBool   : Bool → CompValue             -- boolean constant
  | prodValue   : List CompValue → CompValue   -- (u₁, ..., uₙ)
  | arrValue    : List CompValue → CompValue   -- array value
  | closure     : String → Expr → (String → CompValue) → CompValue -- Closure(λx : τ. e, σ)
  | r1csVar     : Nat → CompValue              -- R1CS variable r
  | binOp       : CompValue → CompValue → CompValue -- Irreducible expression (u₁ ⊗ u₂)
  | unit        : CompValue                    -- unit value

/-- Symbolic environment mapping variables to compilation values. -/
def CompEnv := String → CompValue

/-- Set a variable in the symbolic environment. -/
def setCompValue (σ: CompEnv) (x: String) (v: CompValue) : CompEnv :=
  fun y => if y = x then v else σ y

/-- R1CS constraint in the form A * B + C = 0. -/
structure R1CSConstraint where
  A : CompValue
  B : CompValue
  C : CompValue

/-- Compilation state tracking fresh variables and constraints. -/
structure CompState where
  nextVar : Nat                     -- Counter for fresh variables
  constraints : List R1CSConstraint -- Generated constraints
deriving Nonempty

/-- Empty compilation state. -/
def emptyState : CompState := { nextVar := 0, constraints := [] }

/-- Generate a fresh R1CS variable. -/
def freshVar (s: CompState) : (CompState × CompValue) :=
  let varId := s.nextVar
  let var := CompValue.r1csVar varId
  let s' := { s with nextVar := varId + 1 }
  (s', var)

/-- Add a constraint to the compilation state. -/
def addConstraint (s: CompState) (c: R1CSConstraint) : CompState :=
  { s with constraints := c :: s.constraints }

/-- Check if a CompValue is a field constant. -/
def isField : CompValue → Bool
  | CompValue.constF _ _ => true
  | _ => false

/-- Evaluate a binary field operation if both operands are constants. -/
def evalFieldBinOp (u₁: CompValue) (u₂: CompValue) : Option CompValue :=
  match u₁, u₂ with
  | CompValue.constF p v₁, CompValue.constF _ v₂ => some (CompValue.constF p (v₁.val * v₂.val % p))
  | _, _ => none

/-- Create an equality constraint (u₁ = u₂) as an R1CS constraint. -/
def mkEqualityConstraint (u₁: CompValue) (u₂: CompValue) : R1CSConstraint :=
  -- Equality u₁ = u₂ becomes u₁ - u₂ = 0, or 1*u₁ + (-1)*u₂ + 0 = 0
  {
    A := CompValue.constInt 1,
    B := u₁,
    C := CompValue.binOp (CompValue.constInt (-1)) u₂
  }

/-- Compile an expression to R1CS constraints and a compilation value. -/
unsafe def compile (σ: CompEnv) (s: CompState) (e: Expr) : (CompState × CompValue) :=
  match e with
  -- C-VALUE (constants) just return the value with no constraints
  | Expr.constF p v => (s, CompValue.constF p v)
  | Expr.constInt i => (s, CompValue.constInt i)
  | Expr.constBool b => (s, CompValue.constBool b)

  -- C-VAR (variables) lookup in the environment
  | Expr.var x => (s, σ x)

  -- C-NONDET (wildcard) generates a fresh R1CS variable
  | Expr.wildcard => freshVar s

  -- C-ASSERT (assert e₁ = e₂) adds an equality constraint
  | Expr.assertE e₁ e₂ =>
      let (s₁, u₁) := compile σ s e₁
      let (s₂, u₂) := compile σ s₁ e₂
      let constraint := mkEqualityConstraint u₁ u₂
      let s₃ := addConstraint s₂ constraint
      (s₃, CompValue.unit)

  -- C-RED and C-IRRED for binary operations
  | Expr.binRel e₁ _ e₂ =>
      let (s₁, u₁) := compile σ s e₁
      let (s₂, u₂) := compile σ s₁ e₂

      -- C-RED: If both operands are field constants, try to reduce
      if isField u₁ && isField u₂ then
        match evalFieldBinOp u₁ u₂ with
        | some result => (s₂, result)
        | none => (s₂, CompValue.binOp u₁ u₂)
      -- C-IRRED: Otherwise, create an irreducible expression
      else
        (s₂, CompValue.binOp u₁ u₂)

  -- Lambda abstraction
  | Expr.lam x τ body =>
      (s, CompValue.closure x body σ)

  -- Function application
  | Expr.app e₁ e₂ =>
      let (s₁, u₁) := compile σ s e₁
      let (s₂, u₂) := compile σ s₁ e₂
      match u₁ with
      | CompValue.closure x body σ' =>
          let σ'' := setCompValue σ' x u₂
          compile σ'' s₂ body
      | _ => (s₂, CompValue.unit) -- Error case

  -- Let binding
  | Expr.letIn x e₁ e₂ =>
      let (s₁, u₁) := compile σ s e₁
      let σ' := setCompValue σ x u₁
      compile σ' s₁ e₂

  -- Product construction
  | Expr.prodCons es =>
      let folder := fun (acc : CompState × List CompValue) e =>
        let (s', vs) := acc
        let (s'', v) := compile σ s' e
        (s'', vs ++ [v])
      let (s', vs) := List.foldl folder (s, []) es
      (s', CompValue.prodValue vs)

  -- Array construction
  | Expr.arrCons h t =>
      let (s₁, u₁) := compile σ s h
      let (s₂, u₂) := compile σ s₁ t
      match u₂ with
      | CompValue.arrValue vs => (s₂, CompValue.arrValue (u₁ :: vs))
      | _ => (s₂, CompValue.arrValue [u₁]) -- Assume empty array if not an array

  -- Iterator (would need to be unrolled during compilation)
  | Expr.iter idx start ed step acc =>
      -- Simplified implementation - in practice, we'd unroll the loop
      -- during compilation based on concrete values of start and end
      (s, CompValue.unit)

  -- Circuit reference
  | Expr.circRef name args =>
      -- Simplified implementation - would need to handle circuit instantiation
      (s, CompValue.unit)

  -- Default for other expressions
  | _ => (s, CompValue.unit)
