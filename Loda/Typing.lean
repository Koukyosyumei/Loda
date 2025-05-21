import Loda.Ast
import Loda.Circuit
import Loda.Env
import Loda.Eval
import Loda.PropSemantics

namespace Ty

/-- Subtyping judgment for CODA types -/
inductive SubtypeJudgment {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} :
  Option Ast.Ty → Option Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {τ : Ast.Ty} :
      SubtypeJudgment (pure τ) (pure τ)

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment (pure τ₁) (pure τ₂) →
      SubtypeJudgment (pure τ₂) (pure τ₃) →
      SubtypeJudgment (pure τ₁) (pure τ₃)

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Expr} :
      SubtypeJudgment (pure T₁) (pure T₂) →
      (PropSemantics.expr2prop σ δ ctr φ₁ → PropSemantics.expr2prop σ δ ctr φ₂) →
      SubtypeJudgment (pure (Ast.Ty.refin T₁ φ₁)) (pure (Ast.Ty.refin T₂ φ₂))

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      -- SubtypeJudgment (set (set σ x z) y z) Γ τr τs →
      SubtypeJudgment (pure τr) (pure τs) →
      SubtypeJudgment (pure (Ast.Ty.func x τx τr)) (pure (Ast.Ty.func y τy τs))

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {T₁ T₂ : Ast.Ty} :
      SubtypeJudgment (pure T₁) (pure T₂) →
      SubtypeJudgment (pure (Ast.Ty.arr T₁)) (pure (Ast.Ty.arr T₂))

  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {Ts₁ Ts₂ : List Ast.Ty} :
      Ts₁.length = Ts₂.length →
      --PairwiseProd (SubtypeJudgment σ Γ) (List.zip Ts₁ Ts₂) →
      (∀ i, i < Ts₁.length → SubtypeJudgment Ts₁[i]? Ts₂[i]?) →
      SubtypeJudgment (pure (Ast.Ty.prod Ts₁)) (pure (Ast.Ty.prod Ts₂))

inductive TypeJudgment {σ: Env.ValEnv} {δ: Env.CircuitEnv} {ctr: ℕ}:
  Env.TyEnv → Ast.Expr → Ast.Ty → Prop where
  -- TE-VAR
  | TE_Var {Γ: Env.TyEnv} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Expr, Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ (Ast.Expr.var x) (Ast.Ty.refin T (Ast.expr_eq Ast.v (Ast.Expr.var x)))

  -- TE-VAR-FUNC
  | T_VarFunc {Γ: Env.TyEnv} {f x : String} {τ₁ τ₂: Ast.Ty}:
      Γ f = (Ast.Ty.func x τ₁ τ₂) →
      TypeJudgment Γ (Ast.Expr.var f) (Ast.Ty.func x τ₁ τ₂)

  -- TE-NONDET
  | T_Nondet {Γ: Env.TyEnv} {p: ℕ}:
    TypeJudgment Γ Ast.Expr.wildcard (Ast.Ty.refin (Ast.Ty.field p) (Ast.Expr.constBool true))

  -- TE-CONSTF
  | T_ConstF {Γ: Env.TyEnv} {p: ℕ} {f: F p} :
    TypeJudgment Γ (Ast.Expr.constF p f) (Ast.Ty.refin (Ast.Ty.field p) (Ast.expr_eq Ast.v (Ast.Expr.constF p f)))

  -- TE-ASSERT
  | T_Assert {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {p: ℕ}:
    TypeJudgment Γ e₁ (Ast.Ty.field p) →
    TypeJudgment Γ e₂ (Ast.Ty.field p) →
    TypeJudgment Γ (Ast.Expr.assertE e₁ e₂) (Ast.Ty.refin Ast.Ty.unit (Ast.expr_eq e₁ e₂))

  -- TE-BINOPFIELD
  | T_BinOpField {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {op: Ast.FieldOp} {p: ℕ}:
    TypeJudgment Γ e₁ (Ast.Ty.field p) →
    TypeJudgment Γ e₂ (Ast.Ty.field p) →
    TypeJudgment Γ (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field p) (Ast.expr_eq Ast.v (Ast.Expr.fieldExpr e₁ op e₂))))

  -- TE-BINOPINT
  | T_BinOpInt {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {op: Ast.IntegerOp} {p: ℕ}:
    TypeJudgment Γ e₁ (Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)) →
    TypeJudgment Γ e₂ (Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)) →
    TypeJudgment Γ (Ast.Expr.intExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.int) (Ast.expr_eq Ast.v (Ast.Expr.intExpr e₁ op e₂))))

  -- TE-ABS (function abstraction)
  | T_Abs {Γ: Env.TyEnv} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment (Env.setTy Γ x τ₁) e (τ₂) →
    TypeJudgment Γ (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂))

  -- TE-APP
  | T_App {Γ: Env.TyEnv} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment Γ x₁ (Ast.Ty.func s τ₁ τ₂) →
    Eval.eval σ δ ctr x₂ = some v →
    TypeJudgment Γ x₂ τ₁ →
    TypeJudgment Γ (Ast.Expr.app x₁ x₂) τ₂

  -- TE_SUB
  | T_SUB {Γ: Env.TyEnv} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}:
    @SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₂) →
    TypeJudgment Γ e τ₁ →
    TypeJudgment Γ e τ₂

  -- TE-LETIN
  | T_LetIn {Γ: Env.TyEnv} {x : String} {e₁ e₂ : Ast.Expr} {τ₁ τ₂ : Ast.Ty} {v : Ast.Value}:
      TypeJudgment Γ e₁ τ₁ →
      Eval.eval σ δ ctr e₁ = some v →
      --TypeJudgment (Env.setVal σ x v) δ (Env.setTy Γ x τ₁) ctr e₂ (τ₂, σ) →
      TypeJudgment (Env.setTy Γ x τ₁) e₂ τ₂ →
      TypeJudgment Γ (Ast.Expr.letIn x e₁ e₂) τ₂

lemma TE_Var_env {σ : Env.ValEnv} {δ : Env.CircuitEnv} {Γ : Env.TyEnv} {ctr : ℕ} {x : String} {T : Ast.Ty} {φ : Ast.Expr}
  (hp: PropSemantics.expr2prop σ δ ctr φ) (hΓ : Γ x = Ast.Ty.refin T φ) :
  @TypeJudgment σ δ ctr Γ (Ast.Expr.var x) (Γ x) := by
  -- 1) まず TE_Var で {v : T | v = x}
  have H0 : @TypeJudgment σ δ ctr Γ (Ast.Expr.var x)
                (Ast.Ty.refin T (Ast.expr_eq Ast.v (Ast.Expr.var x)))
    := TypeJudgment.TE_Var _ hΓ
  rw[hΓ]
  -- 2) 次にサブタイピングで expr_eq v x ⇒ φ を使って貼り替え
  apply TypeJudgment.T_SUB
    (SubtypeJudgment.TSub_Refine
      SubtypeJudgment.TSub_Refl
      (by intro _; exact hp))
    H0

axiom IntExprEqImpliesIntVal :
  ∀ (a b : Ast.Expr) (op : Ast.IntegerOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ),
  PropSemantics.expr2prop σ δ ctr (Ast.expr_eq Ast.v (Ast.Expr.intExpr a op b)) →
  ∃ vv, Eval.eval σ δ ctr Ast.v = some (Ast.Value.vInt vv)

axiom BoolExprEqImpliesBoolVal :
  ∀ (a b : Ast.Expr) (op : Ast.BooleanOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ),
  PropSemantics.expr2prop σ δ ctr (Ast.expr_eq Ast.v (Ast.Expr.boolExpr a op b)) →
  ∃ vv, Eval.eval σ δ ctr Ast.v = some (Ast.Value.vBool vv)

axiom FieldExprEqImpliesFieldVal {p : ℕ} :
  ∀ (a b : Ast.Expr) (op : Ast.FieldOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ),
  PropSemantics.expr2prop σ δ ctr (Ast.expr_eq Ast.v (Ast.Expr.fieldExpr a op b)) →
  ∃ vv, Eval.eval σ δ ctr Ast.v = some (Ast.Value.vF p vv)

/-- Given a circuit `c`, produce the Prop that says
1. for any choice of inputs of the correct field type,
2. evaluating `c.body` yields a value `v`,
3. and `v` satisfies the refinement predicate in `c.output`. -/
def circuit2prop (p : ℕ) (δ : Env.CircuitEnv) (c : Circuit.Circuit) : Prop :=
  ∀ (xs : List (ZMod p)),
  let σ : Env.ValEnv :=
    (c.inputs.zip xs).foldl (fun σ (xy : (String × Ast.Ty) × ZMod p) =>
      let ((name, _), x) := xy; Env.setVal σ name (Ast.Value.vF p x)) (fun _ => Ast.Value.vStar)
  let Γ : Env.TyEnv :=
    (c.inputs.zip xs).foldl (fun Γ (xy : (String × Ast.Ty) × ZMod p) =>
      let ((name, τ), _) := xy; Env.setTy Γ name τ) (fun _ => Ast.Ty.unit)
  -- require that the argument list `xs` matches `c.inputs` in length
  xs.length = c.inputs.length →
  -- require that the inputs satisfy the assumed types
  ∀ p ∈ (List.zip c.inputs xs), (PropSemantics.tyenv2prop σ δ 1000 Γ p.fst.fst) →
  -- check the type of the output is valid
  match Eval.eval σ δ 1000 c.body with
  | some _ => @TypeJudgment σ δ 1000 Γ (Ast.Expr.var c.output.fst) (c.output.snd)
  | none   => False

end Ty
