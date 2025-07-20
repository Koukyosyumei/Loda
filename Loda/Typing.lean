import Init.Data.List.Basic

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
inductive SubtypeJudgment {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} :
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
  | TSub_Refine {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Predicate} :
      SubtypeJudgment (pure T₁) (pure T₂) →
      PropSemantics.tyenvToProp σ δ Γ →
      (∀ v: Ast.Expr, (PropSemantics.predToProp σ δ φ₁ v → PropSemantics.predToProp σ δ φ₂ v)) →
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

  /-
  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {Ts₁ Ts₂ : List Ast.Ty} :
      Ts₁.length = Ts₂.length →
      --PairwiseProd (SubtypeJudgment σ Γ) (List.zip Ts₁ Ts₂) →
      (∀ i, i < Ts₁.length → SubtypeJudgment Ts₁[i]? Ts₂[i]?) →
      SubtypeJudgment (pure (Ast.Ty.prod Ts₁)) (pure (Ast.Ty.prod Ts₂))
  -/

/--
  Typing judgment `Γ ⊢ e : τ`: expression `e` has type `τ`
  under type environment `Γ`, valuation `σ`, circuits `δ`, and fuel.
-/
inductive TypeJudgment {σ: Env.ValEnv} {δ: Env.CircuitEnv}:
  Env.TyEnv → Ast.Expr → Ast.Ty → Prop where
  -- TE-VAR
  | TE_Var {Γ: Env.TyEnv} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Predicate, Env.lookupTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ (Ast.Expr.var x) (Ast.Ty.refin T (Ast.Predicate.eq (Ast.Expr.var x)))

  | TE_VarEnv {Γ: Env.TyEnv} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Predicate, Env.lookupTy Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment Γ (Ast.Expr.var x) (Ast.Ty.refin T φ)

  -- TE-VAR-FUNC
  | TE_VarFunc {Γ: Env.TyEnv} {f x : String} {τ₁ τ₂: Ast.Ty}:
      Env.lookupTy Γ f = (Ast.Ty.func x τ₁ τ₂) →
      TypeJudgment Γ (Ast.Expr.var f) (Ast.Ty.func x τ₁ τ₂)

  -- TE-NONDET
  | TE_Nondet {Γ: Env.TyEnv}:
    TypeJudgment Γ Ast.Expr.wildcard (Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.const (Ast.Expr.constBool true)))

  -- TE-CONSTI
  --| TE_ConstI {Γ: Env.TyEnv} {n: ℕ}:
  --  TypeJudgment Γ (Ast.Expr.constInt n) (Ast.Ty.refin (Ast.Ty.int) (Ast.Predicate.eq (Ast.Expr.constInt n)))

  -- TE-CONSTF
  | TE_ConstF {Γ: Env.TyEnv} {f: F} :
    TypeJudgment Γ (Ast.Expr.constF f) (Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.constF f)))

  -- TE-ASSERT
  | TE_Assert {Γ: Env.TyEnv} {e₁ e₂ φ₁ φ₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate}:
    TypeJudgment Γ e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
    TypeJudgment Γ (Ast.Expr.assertE e₁ e₂) (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.const (Ast.exprEq e₁ e₂)))

  -- TE-BINOPFIELD
  | TE_BinOpField {Γ: Env.TyEnv} {e₁ e₂: Ast.Expr} {φ₁ φ₂: Ast.Predicate} {op: Ast.FieldOp}:
    TypeJudgment Γ e₁ (Ast.Ty.refin (Ast.Ty.field) φ₁) →
    TypeJudgment Γ e₂ (Ast.Ty.refin (Ast.Ty.field) φ₂) →
    TypeJudgment Γ (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.fieldExpr e₁ op e₂))))

  -- TE-ABS (function abstraction)
  | TE_Abs {Γ: Env.TyEnv} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment (Env.updateTy Γ x τ₁) e (τ₂) →
    TypeJudgment Γ (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂))

  -- TE-APP
  | TE_App {Γ: Env.TyEnv} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment Γ x₁ (Ast.Ty.func s τ₁ τ₂) →
    Eval.EvalProp σ δ x₂ v →
    TypeJudgment Γ x₂ τ₁ →
    TypeJudgment Γ (Ast.Expr.app x₁ x₂) τ₂

  -- TE_SUB
  | TE_SUB {Γ: Env.TyEnv} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}
    (h₀ : @SubtypeJudgment σ δ Γ (some τ₁) (some τ₂))
    (ht : @TypeJudgment σ δ Γ e τ₁) :
    TypeJudgment Γ e τ₂

  -- TE-LETIN
  | TE_LetIn {Γ: Env.TyEnv} {x : String} {e₁ e₂ : Ast.Expr} {τ₁ τ₂ : Ast.Ty}
    (h₁: @TypeJudgment σ δ Γ e₁ τ₁)
    (h₂: @TypeJudgment σ δ (Env.updateTy Γ x τ₁) e₂ τ₂):
    TypeJudgment Γ (Ast.Expr.letIn x e₁ e₂) τ₂

/--
If an expression `e` is typed as the refinement `{ v : τ | φ }`,
then the predicate `φ` holds under `exprToProp`.
(TODO: this is the soundness theorem that we can prove)
-/
axiom typeJudgmentRefinementSound {σ : Env.ValEnv} {δ : Env.CircuitEnv}
 (Γ : Env.TyEnv) (τ : Ast.Ty) (e: Ast.Expr) (φ: Ast.Predicate):
  @Ty.TypeJudgment σ δ Γ e (Ast.Ty.refin τ φ) → PropSemantics.predToProp σ δ φ e

def makeEnvs (c : Ast.Circuit) (x : Ast.Value) : Env.ValEnv × Env.TyEnv :=
  let σ: Env.ValEnv := Env.updateVal [] c.inputs.fst x
  let Γ: Env.TyEnv := Env.updateTy [] c.inputs.fst c.inputs.snd
  (σ, Γ)

/--
  Correctness of a circuit `c`:
  if the input satisfies its refinement, then evaluating `c.body`
  yields a value satisfying the output refinement.
-/
def circuitCorrect (δ : Env.CircuitEnv) (c : Ast.Circuit) : Prop :=
  ∀ (x : Ast.Value),
    x != Ast.Value.vStar →
    let (σ, Γ) := makeEnvs c x
    PropSemantics.tyenvToProp σ δ Γ →
    @TypeJudgment σ δ Γ c.body c.output.snd

lemma lookupTy_mem (Γ: Env.TyEnv) (x: String) (τ :Ast.Ty) (φ: Ast.Predicate)
  (h : Env.lookupTy Γ x = Ast.Ty.refin τ φ) :
  (x, Ast.Ty.refin τ φ) ∈ Γ := by
  by_contra hn
  dsimp [Env.lookupTy] at h
  cases h₁ : Γ.find? (·.1 = x) with
  | none => {
    simp_all
  }
  | some p  => {
    simp_all
    sorry
  }

lemma tyenvToProp_implies_varToProp
  (σ : Env.ValEnv) (Δ : Env.CircuitEnv) (Γ : Env.TyEnv)
  (x : String) (τ : Ast.Ty) (φ : Ast.Predicate)
  (hΓx : Env.lookupTy Γ x = Ast.Ty.refin τ φ)
  (hmt : PropSemantics.tyenvToProp σ Δ Γ) :
  PropSemantics.varToProp σ Δ Γ x := by
  dsimp [PropSemantics.tyenvToProp] at hmt
  have hmem : (x, Ast.Ty.refin τ φ) ∈ Γ := lookupTy_mem Γ x τ φ hΓx
  apply hmt at hmem
  simp at hmem
  exact hmem

end Ty

notation:50 Γ " ⊨[" σ ", " Δ ", " "] " τ₁ "<:" τ₂ =>
  @Ty.SubtypeJudgment σ Δ Γ (some τ₁) (some τ₂)

notation:25 Δ " ; " Γ " ⊢[" σ ", " "] " e " : " τ =>
  @Ty.TypeJudgment σ Δ Γ e τ
