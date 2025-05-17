import Loda.Ast

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
  -- TE-VAR
  | TE_Var {σ: Env} {δ: CircuitEnv} {Γ: TyEnv} {x : String} {v: Value} {T: Ty} {φ: Prop}:
      Γ x = (Ty.refin v T φ) →
    TypeJudgment σ δ Γ (Expr.var x) (Ty.refin v T (v = eval σ δ (Expr.var x)))
  -- TE-VAR-FUNC
  | T_VarFunc {σ: Env} {δ: CircuitEnv} {Γ: TyEnv} {f x : String} {τ₁ τ₂: Ty}:
      Γ f = (Ty.func x τ₁ τ₂) →
      TypeJudgment σ δ Γ (Expr.var f) (Ty.func x τ₁ τ₂)
  -- TE-NONDET
  | T_Nondet {σ: Env} {δ: CircuitEnv} {Γ: TyEnv} {p: ℕ} {v: Value}:
    TypeJudgment σ δ Γ Expr.wildcard (Ty.refin v (Ty.field p) True)
  -- TE-CONSTF
  | T_ConstF {σ: Env} {δ: CircuitEnv} {Γ: TyEnv} {p: ℕ} {v: Value} {f: F p} :
    TypeJudgment σ δ Γ (Expr.constF p f) (Ty.refin v (Ty.field p) (v = Value.vF p f))
  -- TE-ASSERT
  | T_Assert {σ: Env} {δ: CircuitEnv} {Γ: TyEnv} {e₁ e₂: Expr} {p: ℕ} {v: Value} :
    TypeJudgment σ δ Γ e₁ (Ty.field p) →
    TypeJudgment σ δ Γ e₂ (Ty.field p) →
    TypeJudgment σ δ Γ (Expr.assertE e₁ e₂) (Ty.refin v Ty.unit (eval σ δ e₁ = eval σ δ e₂))

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
