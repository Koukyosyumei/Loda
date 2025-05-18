import Loda.Ast

/-- Type Environment. -/
def TyEnv := String -> Ast.Ty

def setTy (Γ : TyEnv) (x : String) (v: Ast.Ty) : TyEnv :=
  fun y => if y = x then v else Γ y

/-- Subtyping judgment for CODA types -/
inductive SubtypeJudgment : Ast.Env -> TyEnv → Option Ast.Ty → Option Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {σ : Ast.Env} {Γ : TyEnv} {τ : Ast.Ty} :
      SubtypeJudgment σ Γ (pure τ) (pure τ)

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {σ : Ast.Env} {Γ : TyEnv} {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment σ Γ (pure τ₁) (pure τ₂) →
      SubtypeJudgment σ Γ (pure τ₂) (pure τ₃) →
      SubtypeJudgment σ Γ (pure τ₁) (pure τ₃)

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {σ : Ast.Env} {Γ : TyEnv} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Prop} :
      SubtypeJudgment σ Γ (pure T₁) (pure T₂) →
      (φ₁ → φ₂) →
      SubtypeJudgment σ Γ (pure (Ast.Ty.refin T₁ φ₁)) (pure (Ast.Ty.refin T₂ φ₂))

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {σ : Ast.Env} {Γ : TyEnv} {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment σ Γ (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      -- SubtypeJudgment (set (set σ x z) y z) Γ τr τs →
      SubtypeJudgment σ Γ (pure τr) (pure τs) →
      SubtypeJudgment σ Γ (pure (Ast.Ty.func x τx τr)) (pure (Ast.Ty.func y τy τs))

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {σ : Ast.Env} {Γ : TyEnv} {T₁ T₂ : Ast.Ty} :
      SubtypeJudgment σ Γ (pure T₁) (pure T₂) →
      SubtypeJudgment σ Γ (pure (Ast.Ty.arr T₁)) (pure (Ast.Ty.arr T₂))

  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {σ : Ast.Env} {Γ : TyEnv} {Ts₁ Ts₂ : List Ast.Ty} :
      Ts₁.length = Ts₂.length →
      --PairwiseProd (SubtypeJudgment σ Γ) (List.zip Ts₁ Ts₂) →
      (∀ i, i < Ts₁.length → SubtypeJudgment σ Γ Ts₁[i]? Ts₂[i]?) →
      SubtypeJudgment σ Γ (pure (Ast.Ty.prod Ts₁)) (pure (Ast.Ty.prod Ts₂))

inductive TypeJudgment: Ast.Env -> Ast.CircuitEnv -> TyEnv -> ℕ -> Ast.Expr -> (Ast.Ty × Ast.Env) -> Prop where
  -- TE-VAR
  | TE_Var {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {x : String} {v: Ast.Value} {T: Ast.Ty}:
    (∀ φ: Prop, φ → Γ x = (Ast.Ty.refin T φ)) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.var x) ((Ast.Ty.refin T (v = σ x)), σ)

  -- TE-VAR-FUNC
  | T_VarFunc {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {f x : String} {τ₁ τ₂: Ast.Ty}:
      Γ f = (Ast.Ty.func x τ₁ τ₂) →
      TypeJudgment σ δ Γ ctr (Ast.Expr.var f) ((Ast.Ty.func x τ₁ τ₂), σ)

  -- TE-NONDET
  | T_Nondet {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {p: ℕ}:
    TypeJudgment σ δ Γ ctr Ast.Expr.wildcard ((Ast.Ty.refin (Ast.Ty.field p) True), σ)

  -- TE-CONSTF
  | T_ConstF {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {p: ℕ} {v: Ast.Value} {f: F p} :
    TypeJudgment σ δ Γ ctr (Ast.Expr.constF p f) ((Ast.Ty.refin (Ast.Ty.field p) (v = Ast.Value.vF p f)), σ)

  -- TE-ASSERT
  | T_Assert {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {e₁ e₂: Ast.Expr} {p: ℕ}:
    TypeJudgment σ δ Γ ctr e₁ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr e₂ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.assertE e₁ e₂) ((Ast.Ty.refin Ast.Ty.unit (Ast.eval σ δ ctr e₁ = Ast.eval σ δ ctr e₂)), σ)

  -- TE-BINOPFIELD
  | T_BinOpField {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {e₁ e₂: Ast.Expr} {op: Ast.FieldOp} {p: ℕ} {v: Ast.Value}:
    TypeJudgment σ δ Γ ctr e₁ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr e₂ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field p) (v = Ast.eval σ δ ctr (Ast.Expr.fieldExpr e₁ op e₂))), σ)

  -- TE-ABS (function abstraction)
  | T_Abs {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment σ δ (setTy Γ x τ₁) ctr e (τ₂, σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂), σ)

  -- TE-APP
  | T_App {σ: Ast.Env} {δ: Ast.CircuitEnv} {Γ: TyEnv} {ctr: ℕ} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment σ δ Γ ctr x₁ ((Ast.Ty.func s τ₁ τ₂), σ) →
    Ast.eval σ δ ctr x₂ = some v →
    TypeJudgment σ δ Γ ctr x₂ (τ₁, σ) → TypeJudgment σ δ Γ ctr (Ast.Expr.app x₁ x₂) (τ₂, (Ast.set σ s v))
