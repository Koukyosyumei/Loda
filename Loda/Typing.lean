import Loda.Ast
import Loda.Env
import Loda.Eval
import Loda.PropSemantics

/-!
  # Subtyping and Typing Judgments for Loda

  This module defines:
  1. A **subtyping** relation `SubtypeJudgment`
     between (optional) Loda types under environments.
  2. A **typing** relation `TypeJudgment`
     assigning types to Loda expressions.
  3. A conversion of a `Circuit` into a `Prop`
     expressing its correctness w.r.t. its input/output refinements.
-/

namespace Ty

/--
  Subtyping judgment between two optional types `τ₁ → τ₂`
  under valuation `σ`, circuits `δ`, type env `Γ`, and fuel.
-/
inductive SubtypeJudgment {fuel: ℕ} {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} :
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
      (PropSemantics.exprToProp fuel σ δ φ₁ → PropSemantics.exprToProp fuel σ δ φ₂) →
      SubtypeJudgment (pure (Ast.Ty.refin T₁ φ₁)) (pure (Ast.Ty.refin T₂ φ₂))

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      -- SubtypeJudgment (update (update σ x z) y z) Γ τr τs →
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

/--
  Typing judgment `Γ ⊢ e : τ`: expression `e` has type `τ`
  under type environment `Γ`, valuation `σ`, circuits `δ`, and fuel.
-/
inductive TypeJudgment {fuel: ℕ} {σ: Env.ValEnv} {δ: Env.CircuitEnv}:
  Env.TyEnv → Ast.Expr → Ast.Ty → Prop where
  -- TE-VAR
  | TE_Var {Γ: Env.TyEnv} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Expr, Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ (Ast.Expr.var x) (Ast.Ty.refin T (Ast.exprEq Ast.v (Ast.Expr.var x)))

  -- TE-VAR-FUNC
  | TE_VarFunc {Γ: Env.TyEnv} {f x : String} {τ₁ τ₂: Ast.Ty}:
      Γ f = (Ast.Ty.func x τ₁ τ₂) →
      TypeJudgment Γ (Ast.Expr.var f) (Ast.Ty.func x τ₁ τ₂)

  -- TE-NONDET
  | TE_Nondet {Γ: Env.TyEnv} {p: ℕ}:
    TypeJudgment Γ Ast.Expr.wildcard (Ast.Ty.refin (Ast.Ty.field p) (Ast.Expr.constBool true))

  -- TE-CONSTF
  | TE_ConstF {Γ: Env.TyEnv} {p: ℕ} {f: F p} :
    TypeJudgment Γ (Ast.Expr.constF p f) (Ast.Ty.refin (Ast.Ty.field p) (Ast.exprEq Ast.v (Ast.Expr.constF p f)))

  -- TE-ASSERT
  | TE_Assert {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {p: ℕ}:
    TypeJudgment Γ e₁ (Ast.Ty.field p) →
    TypeJudgment Γ e₂ (Ast.Ty.field p) →
    TypeJudgment Γ (Ast.Expr.assertE e₁ e₂) (Ast.Ty.refin Ast.Ty.unit (Ast.exprEq e₁ e₂))

  -- TE-BINOPFIELD
  | TE_BinOpField {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {op: Ast.FieldOp} {p: ℕ}:
    TypeJudgment Γ e₁ (Ast.Ty.field p) →
    TypeJudgment Γ e₂ (Ast.Ty.field p) →
    TypeJudgment Γ (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field p) (Ast.exprEq Ast.v (Ast.Expr.fieldExpr e₁ op e₂))))

  -- TE-BINOPINT
  | TE_BinOpInt {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {op: Ast.IntegerOp}:
    TypeJudgment Γ e₁ (Ast.Ty.refin Ast.Ty.int _) →
    TypeJudgment Γ e₂ (Ast.Ty.refin Ast.Ty.int _) →
    TypeJudgment Γ (Ast.Expr.intExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.int) (Ast.exprEq Ast.v (Ast.Expr.intExpr e₁ op e₂))))

  -- TE-ABS (function abstraction)
  | TE_Abs {Γ: Env.TyEnv} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment (Env.updateTy Γ x τ₁) e (τ₂) →
    TypeJudgment Γ (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂))

  -- TE-APP
  | TE_App {Γ: Env.TyEnv} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment Γ x₁ (Ast.Ty.func s τ₁ τ₂) →
    Eval.eval fuel σ δ x₂ = some v →
    TypeJudgment Γ x₂ τ₁ →
    TypeJudgment Γ (Ast.Expr.app x₁ x₂) τ₂

  -- TE_SUB
  | TE_SUB {Γ: Env.TyEnv} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}
    (h₀ : @SubtypeJudgment fuel σ δ Γ (some τ₁) (some τ₂))
    (ht : @TypeJudgment fuel σ δ Γ e τ₁) :
    TypeJudgment Γ e τ₂

  -- TE-LETIN
  | TE_LetIn {Γ: Env.TyEnv} {x : String} {e₁ e₂ : Ast.Expr} {τ₁ τ₂ : Ast.Ty}
    (h₁: @TypeJudgment fuel σ δ Γ e₁ τ₁)
    (h₂: @TypeJudgment fuel σ δ (Env.updateTy Γ x τ₁) e₂ τ₂):
    TypeJudgment Γ (Ast.Expr.letIn x e₁ e₂) τ₂


/--
Specialized soundness theorem for a variable identifier `ident`:
if `Γ ident = {v : T // φ}` and `φ` holds, then the typing rule for
`ident` followed by subsumption yields the same refinement, and hence
`φ` holds by `typeJudgmentRefinementSound`.
-/
theorem varRefineSound
  {fuel : ℕ} {σ : Env.ValEnv} {δ : Env.CircuitEnv}
  {Γ : Env.TyEnv} {ident : String} {T : Ast.Ty} {φ : Ast.Expr}
  (hφ: PropSemantics.exprToProp fuel σ δ φ) (hΓ : Γ ident = Ast.Ty.refin T φ) :
  @TypeJudgment fuel σ δ Γ (Ast.Expr.var ident) (Γ ident) := by
  have H0 : @TypeJudgment fuel σ δ Γ (Ast.Expr.var ident)
                (Ast.Ty.refin T (Ast.exprEq Ast.v (Ast.Expr.var ident)))
    := TypeJudgment.TE_Var _ hΓ
  rw[hΓ]
  apply TypeJudgment.TE_SUB
    (SubtypeJudgment.TSub_Refine
      SubtypeJudgment.TSub_Refl
      (by intro _; exact hφ))
    H0

axiom exprIntVSound :
  ∀ (a b : Ast.Expr) (op : Ast.IntegerOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (fuel : ℕ),
  PropSemantics.exprToProp fuel σ δ (Ast.exprEq Ast.v (Ast.Expr.intExpr a op b)) →
  ∃ vv, Eval.eval fuel σ δ Ast.v = some (Ast.Value.vInt vv)

axiom exprBoolVSound :
  ∀ (a b : Ast.Expr) (op : Ast.BooleanOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (fuel : ℕ),
  PropSemantics.exprToProp fuel σ δ (Ast.exprEq Ast.v (Ast.Expr.boolExpr a op b)) →
  ∃ vv, Eval.eval fuel σ δ Ast.v = some (Ast.Value.vBool vv)

axiom exprFielVdSound {p : ℕ} :
  ∀ (a b : Ast.Expr) (op : Ast.FieldOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (fuel : ℕ),
  PropSemantics.exprToProp fuel σ δ (Ast.exprEq Ast.v (Ast.Expr.fieldExpr a op b)) →
  ∃ vv, Eval.eval fuel σ δ Ast.v = some (Ast.Value.vF p vv)

/--
If an expression `e` is typed as the refinement `{ v : τ // φ }`,
then the predicate `φ` holds under `exprToProp`.
(TODO: this is the soundness theorem that we can prove)
-/
axiom typeJudgmentRefinementSound {fuel : ℕ} {σ : Env.ValEnv} {δ : Env.CircuitEnv}
 (Γ : Env.TyEnv) (τ : Ast.Ty) (e φ : Ast.Expr) :
  @Ty.TypeJudgment fuel σ δ Γ e (Ast.Ty.refin τ φ) → PropSemantics.exprToProp fuel σ δ φ

/--
  Correctness of a circuit `c`:
  if the input satisfies its refinement, then evaluating `c.body`
  yields a value satisfying the output refinement.
-/
def circuitCorrect (fuel : ℕ) (δ : Env.CircuitEnv) (c : Ast.Circuit) : Prop :=
  ∀ (x : Ast.Value),
    x != Ast.Value.vStar →
    -- (2) σ, Γ の構築をローカル定義
    let σ: Env.ValEnv := Env.updateVal (fun _ => Ast.Value.vStar) c.inputs.fst x
    let Γ: Env.TyEnv := Env.updateTy (fun _ => Ast.Ty.unit) c.inputs.fst c.inputs.snd
    -- (3) 全入力が型を満たす仮定
    PropSemantics.tyenvToProp fuel σ δ Γ c.inputs.fst →
    -- (4) 型付けを保証する
    @TypeJudgment fuel σ δ Γ c.body c.output.snd

end Ty

notation:50 Γ " ⊨[" σ ", " Δ ", " fuel "] " τ₁ "<:" τ₂ =>
  @Ty.SubtypeJudgment fuel σ Δ Γ (some τ₁) (some τ₂)

notation:25 Δ " ; " Γ " ⊢[" σ ", " fuel "] " e " : " τ =>
  @Ty.TypeJudgment fuel σ Δ Γ e τ
