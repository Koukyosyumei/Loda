import Loda.Ast
import Loda.Circuit
import Loda.Env
import Loda.Eval
import Loda.PropSemantics

namespace Ty

/-- Subtyping judgment for CODA types -/
inductive SubtypeJudgment : Env.ValEnv -> Env.CircuitEnv -> Env.TyEnv -> ℕ → Option Ast.Ty → Option Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {τ : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure τ) (pure τ)

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₂) →
      SubtypeJudgment σ δ Γ ctr (pure τ₂) (pure τ₃) →
      SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₃)

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Expr} :
      SubtypeJudgment σ δ Γ ctr (pure T₁) (pure T₂) →
      (PropSemantics.expr2prop σ δ ctr φ₁ → PropSemantics.expr2prop σ δ ctr φ₂) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.refin T₁ φ₁)) (pure (Ast.Ty.refin T₂ φ₂))

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      -- SubtypeJudgment (set (set σ x z) y z) Γ τr τs →
      SubtypeJudgment σ δ Γ ctr (pure τr) (pure τs) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.func x τx τr)) (pure (Ast.Ty.func y τy τs))

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {T₁ T₂ : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure T₁) (pure T₂) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.arr T₁)) (pure (Ast.Ty.arr T₂))

  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {Ts₁ Ts₂ : List Ast.Ty} :
      Ts₁.length = Ts₂.length →
      --PairwiseProd (SubtypeJudgment σ Γ) (List.zip Ts₁ Ts₂) →
      (∀ i, i < Ts₁.length → SubtypeJudgment σ δ Γ ctr Ts₁[i]? Ts₂[i]?) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.prod Ts₁)) (pure (Ast.Ty.prod Ts₂))

inductive TypeJudgment: Env.ValEnv -> Env.CircuitEnv -> Env.TyEnv -> ℕ -> Ast.Expr -> (Ast.Ty × Env.ValEnv) -> Prop where
  -- TE-VAR
  | TE_Var {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Expr, Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.var x) ((Ast.Ty.refin T (Ast.eeq Ast.v (Ast.Expr.var x))), σ)

  -- TE-VAR-FUNC
  | T_VarFunc {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {f x : String} {τ₁ τ₂: Ast.Ty}:
      Γ f = (Ast.Ty.func x τ₁ τ₂) →
      TypeJudgment σ δ Γ ctr (Ast.Expr.var f) ((Ast.Ty.func x τ₁ τ₂), σ)

  -- TE-NONDET
  | T_Nondet {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {p: ℕ}:
    TypeJudgment σ δ Γ ctr Ast.Expr.wildcard ((Ast.Ty.refin (Ast.Ty.field p) (Ast.Expr.constBool true)), σ)

  -- TE-CONSTF
  | T_ConstF {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {p: ℕ} {f: F p} :
    TypeJudgment σ δ Γ ctr (Ast.Expr.constF p f) ((Ast.Ty.refin (Ast.Ty.field p) (Ast.eeq Ast.v (Ast.Expr.constF p f))), σ)

  -- TE-ASSERT
  | T_Assert {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {e₁ e₂: Ast.Expr} {p: ℕ}:
    TypeJudgment σ δ Γ ctr e₁ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr e₂ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.assertE e₁ e₂) ((Ast.Ty.refin Ast.Ty.unit (Ast.eeq e₁ e₂)), σ)

  -- TE-BINOPFIELD
  | T_BinOpField {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {e₁ e₂: Ast.Expr} {op: Ast.FieldOp} {p: ℕ}:
    TypeJudgment σ δ Γ ctr e₁ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr e₂ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field p) (Ast.eeq Ast.v (Ast.Expr.fieldExpr e₁ op e₂))), σ)

  -- TE-ABS (function abstraction)
  | T_Abs {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment σ δ (Env.setTy Γ x τ₁) ctr e (τ₂, σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂), σ)

  -- TE-APP
  | T_App {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment σ δ Γ ctr x₁ ((Ast.Ty.func s τ₁ τ₂), σ) →
    Eval.eval σ δ ctr x₂ = some v →
    TypeJudgment σ δ Γ ctr x₂ (τ₁, σ) → TypeJudgment σ δ Γ ctr (Ast.Expr.app x₁ x₂) (τ₂, (Env.setVal σ s v))

  -- TE_SUB
  | T_SUB {σ σ': Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}:
    SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₂) →
    TypeJudgment σ δ Γ ctr e (τ₁, σ') →
    TypeJudgment σ δ Γ ctr e (τ₂, σ')

axiom IntExprEqImpliesIntVal :
  ∀ (a b : Ast.Expr) (op : Ast.IntegerOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ),
  PropSemantics.expr2prop σ δ ctr (Ast.eeq Ast.v (Ast.Expr.intExpr a op b)) →
  ∃ vv, Eval.eval σ δ ctr Ast.v = some (Ast.Value.vInt vv)

axiom FieldExprEqImpliesFieldVal {p : ℕ} :
  ∀ (a b : Ast.Expr) (op : Ast.FieldOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ),
  PropSemantics.expr2prop σ δ ctr (Ast.eeq Ast.v (Ast.Expr.fieldExpr a op b)) →
  ∃ vv, Eval.eval σ δ ctr Ast.v = some (Ast.Value.vF p vv)

end Ty
