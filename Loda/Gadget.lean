import Loda.Typing
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Bool.Basic

open Ast

theorem evalprop_var_deterministic
  {σ : Env.ValEnv} {Δ : Env.CircuitEnv} {x : String} :
  ∀ {v₁ v₂}, Eval.EvalProp σ Δ (Expr.var x) v₁ → Eval.EvalProp σ Δ (Expr.var x) v₂ → v₁ = v₂ := by {
    intro v₁ v₂ h₁ h₂
    cases h₁
    cases h₂
    simp_all
  }

axiom evalprop_var_deterministic_axiom
  {σ : Env.ValEnv} {Δ : Env.CircuitEnv} {e : Expr} :
  ∀ {v₁ v₂}, Eval.EvalProp σ Δ e v₁ → Eval.EvalProp σ Δ e v₂ → v₁ = v₂

lemma bool_lookup_and
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (x y: String) (xv yv: Bool) (v: Value)
  (hσx: Env.lookupVal σ x = Value.vBool xv)  (hσy: Env.lookupVal σ y = Value.vBool yv)
  (hee: Eval.EvalProp σ Δ (Expr.boolExpr (Expr.var x) BooleanOp.and (Expr.var y)) v):
  v = Value.vBool (xv && yv) := by
  cases hee with
  | @BoolOp _ _ _ _ _ i₁ i₂ hi₁ hi₂ hi₃ r₂ => {
    apply Eval.EvalProp.Var at hσx
    apply Eval.EvalProp.Var at hσy
    have ieq₁ := @evalprop_var_deterministic σ Δ x (Value.vBool i₁) (Value.vBool xv) hi₂ hσx
    have ieq₂ := @evalprop_var_deterministic σ Δ y (Value.vBool i₂) (Value.vBool yv) hi₃ hσy
    rw[ieq₁, ieq₂] at r₂
    unfold Eval.evalBoolOp at r₂
    simp_all
  }

lemma field_lookup_add
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (x y: String) (xv yv: F) (v: Value)
  (hσx: Env.lookupVal σ x = Value.vF xv)  (hσy: Env.lookupVal σ y = Value.vF yv)
  (hee: Eval.EvalProp σ Δ (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)) v):
  v = Value.vF (xv + yv) := by
  cases hee with
  | @FBinOp _ _ _ _ _ i₁ i₂ hi₁ hi₂ hi₃ r₂ => {
    apply Eval.EvalProp.Var at hσx
    apply Eval.EvalProp.Var at hσy
    have ieq₁ := @evalprop_var_deterministic σ Δ x (Value.vF i₁) (Value.vF xv) hi₂ hσx
    have ieq₂ := @evalprop_var_deterministic σ Δ y (Value.vF i₂) (Value.vF yv) hi₃ hσy
    rw[ieq₁, ieq₂] at r₂
    unfold Eval.evalFieldOp at r₂
    simp_all
  }

lemma field_lookup_mul
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (x y: String) (xv yv: F) (v: Value)
  (hσx: Env.lookupVal σ x = Value.vF xv)  (hσy: Env.lookupVal σ y = Value.vF yv)
  (hee: Eval.EvalProp σ Δ (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.var y)) v):
  v = Value.vF (xv * yv) := by
  cases hee with
  | @FBinOp _ _ _ _ _ i₁ i₂ hi₁ hi₂ hi₃ r₂ => {
    apply Eval.EvalProp.Var at hσx
    apply Eval.EvalProp.Var at hσy
    have ieq₁ := @evalprop_var_deterministic σ Δ x (Value.vF i₁) (Value.vF xv) hi₂ hσx
    have ieq₂ := @evalprop_var_deterministic σ Δ y (Value.vF i₂) (Value.vF yv) hi₃ hσy
    rw[ieq₁, ieq₂] at r₂
    unfold Eval.evalFieldOp at r₂
    simp_all
  }

lemma two_mul_field
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: F)
  (hσx : Env.lookupVal σ x = Value.vF xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.constF 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  intro v hmt h
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have hv2 : v₂ = Value.vF (xv + xv) := @field_lookup_add σ Δ x x xv xv v₂ hσx hσx ih₂
    rw[← two_mul] at hv2
    apply Eval.EvalProp.Rel
    . exact ih₁
    . apply Eval.EvalProp.FBinOp Eval.EvalProp.ConstF
      . apply Eval.EvalProp.Var
        exact hσx
      unfold Eval.evalFieldOp; rfl
    simp_all
  }

lemma add_comm_field
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv yv: ℕ)
  (hσx : Env.lookupVal σ x = Value.vF xv) (hσy : Env.lookupVal σ y = Value.vF yv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  intro v hmt h
  dsimp [PropSemantics.predToProp, PropSemantics.exprToProp] at h ⊢
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have hv2 : v₂ = Value.vF (xv + yv) := @field_lookup_add σ Δ x y xv yv v₂ hσx hσy ih₂
    rw [← add_comm] at hv2
    unfold exprEq
    apply Eval.EvalProp.Rel
    . exact ih₁
    . apply Eval.EvalProp.FBinOp
      apply Eval.EvalProp.Var
      exact hσy
      apply Eval.EvalProp.Var
      exact hσx
      simp_all
      rw[← hv2]
    exact r₁
  }

lemma bool_and_comm
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x y: String) (xv yv: Bool)
  (hσx : Env.lookupVal σ x = Value.vBool xv)
  (hσy : Env.lookupVal σ y = Value.vBool yv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.bool (Predicate.eq (Expr.boolExpr (Expr.var x) BooleanOp.and (Expr.var y)))))
      (pure (Ty.refin Ty.bool (Predicate.eq (Expr.boolExpr (Expr.var y) BooleanOp.and (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  intro v hmt h
  dsimp [PropSemantics.predToProp, PropSemantics.exprToProp] at h ⊢
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have hv2 : v₂ = Value.vBool (xv && yv) := @bool_lookup_and σ Δ x y xv yv v₂ hσx hσy ih₂
    rw [← Bool.and_comm] at hv2
    unfold exprEq
    apply Eval.EvalProp.Rel
    . exact ih₁
    . apply Eval.EvalProp.BoolOp
      apply Eval.EvalProp.Var
      exact hσy
      apply Eval.EvalProp.Var
      exact hσx
      simp_all
      exact xv
    simp_all
  }

lemma mul_comm_field
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv yv: ℕ)
  (hσx : Env.lookupVal σ x = Value.vF xv) (hσy : Env.lookupVal σ y = Value.vF yv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.var y)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  intro v hmt h
  dsimp [PropSemantics.predToProp, PropSemantics.exprToProp] at h ⊢
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have hv2 : v₂ = Value.vF (xv * yv) := @field_lookup_mul σ Δ x y xv yv v₂ hσx hσy ih₂
    rw [← mul_comm] at hv2
    unfold exprEq
    apply Eval.EvalProp.Rel
    . exact ih₁
    . apply Eval.EvalProp.FBinOp
      apply Eval.EvalProp.Var
      exact hσy
      apply Eval.EvalProp.Var
      exact hσx
      simp_all
      rw[← hv2]
    exact r₁
  }

/-
lemma mul_one_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.constF p 1)))))
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.var x))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, Eval.maximumRecursion] at ⊢

lemma add_zero_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.constF p 0)))))
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.var x))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, Eval.maximumRecursion] at ⊢
-/

lemma isUnit_non_zero (x: F) : x ≠ 0 ↔ IsUnit x := by {
  simp_all
}

/-
lemma mul_inv_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  (hp: Fact p.Prime) (hxv_ne_zero: (xv: F p) ≠ 0)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.fieldExpr (Expr.constF p 1) FieldOp.div (Expr.var x))))))
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.constF p 1))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at ⊢
  simp[PropSemantics.exprToProp, hσx, Eval.maximumRecursion] at ⊢
  unfold Eval.eval_with_fuel
  simp_all
  rw[← ZMod.mul_inv_of_unit]
  simp_all
  set tmp := isUnit_non_zero p (xv : ZMod p) hp
  rw [← tmp]
  exact hxv_ne_zero
-/

lemma typed_field_expr_from_refined_vars
  (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (op: Ast.FieldOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Env.lookupTy Γ x = Ast.Ty.refin (Ast.Ty.field) φ₁) (hΓy: Env.lookupTy Γ y = Ast.Ty.refin (Ast.Ty.field) φ₂)
  : @Ty.TypeJudgment σ Δ Γ (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) op (Expr.var y)))) := by
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_Var φ₁
  simp [hΓx]
  apply Ty.TypeJudgment.TE_Var φ₂
  simp [hΓy]

lemma let_binding_field_op_type_preservation
  (x y z: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (op: Ast.FieldOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Env.lookupTy Γ x = Ast.Ty.refin (Ast.Ty.field) φ₁) (hΓy: Env.lookupTy Γ y = Ast.Ty.refin (Ast.Ty.field) φ₂) :
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn z (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y)) (Ast.Expr.var z))
    (Ty.refin (Ty.field) (Ast.Predicate.eq (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y)))) :=
by
  set e1 := Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y)
  set e1_ty := Ty.refin (Ty.field) (Ast.Predicate.eq e1)
  apply Ty.TypeJudgment.TE_LetIn
  · apply typed_field_expr_from_refined_vars <;> try assumption
  · set Γ' := Env.updateTy Γ z e1_ty
    have h_e1_has_type_e1_ty : @Ty.TypeJudgment σ Δ Γ e1 e1_ty := by
      apply typed_field_expr_from_refined_vars <;> try assumption
    have h_refinement_prop_holds :=
      Ty.typeJudgmentRefinementSound Γ (Ast.Ty.field) e1 (Ast.Predicate.eq e1) h_e1_has_type_e1_ty
    have hΓ'_z_eq_e1_ty : Env.lookupTy Γ' z = e1_ty := by
      simp [Γ', Env.updateTy, Env.lookupTy]
    apply Ty.TypeJudgment.TE_VarEnv
    exact hΓ'_z_eq_e1_ty

lemma let_binding_identity
  (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (τ : Ast.Ty) (φ: Ast.Predicate)
  (hΓx: Env.lookupTy Γ x = Ast.Ty.refin τ φ) :
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn y (Ast.Expr.var x) (Ast.Expr.var y))
    (Ty.refin τ (Ast.Predicate.eq (Ast.Expr.var x))) := by
  apply Ty.TypeJudgment.TE_LetIn
  apply Ty.TypeJudgment.TE_Var
  exact hΓx
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.updateTy
  unfold Env.lookupTy
  simp_all

lemma lookupTy_updateTy_of_ne {Γ : Env.TyEnv} {x y : String} {τ₁ τ₂ : Ast.Ty}
  (h : Env.lookupTy Γ x = τ₁) (hxy : y ≠ x) :
  Env.lookupTy (Env.updateTy Γ y τ₂) x = τ₁ := by
  dsimp [Env.updateTy, Env.lookupTy]
  simp [hxy]
  exact h

lemma evalRel_eq_trans1 {v₁ v₂ v₃: Ast.Value}
  (h₁ : Eval.evalRelOp RelOp.eq v₁ v₂ = some true)
  (h₂ : Eval.evalRelOp RelOp.eq v₁ v₃ = some true) :
  Eval.evalRelOp RelOp.eq v₂ v₃ = some true := by {
    unfold Eval.evalRelOp at h₁ h₂ ⊢
    simp_all
    cases v₁ with
    | vF x₁ => {
      cases v₂ with
      | vF x₂ => {
        cases v₃ with
        | vF x₃ => simp_all
        | _ => simp_all
      }
      | _ => simp_all
    }
    | _ => simp_all
  }

lemma evalRel_eq_trans2 {v₁ v₂ v₃: Ast.Value}
  (h₁ : Eval.evalRelOp RelOp.eq v₁ v₂ = some true)
  (h₂ : Eval.evalRelOp RelOp.eq v₂ v₃ = some true) :
  Eval.evalRelOp RelOp.eq v₁ v₃ = some true := by {
    unfold Eval.evalRelOp at h₁ h₂ ⊢
    simp_all
    cases v₁ with
    | vF x₁ => {
      cases v₂ with
      | vF x₂ => {
        cases v₃ with
        | vF x₃ => simp_all
        | _ => simp_all
      }
      | _ => simp_all
    }
    | _ => simp_all
  }


lemma evalProp_exprEq_trans1 {σ :Env.ValEnv} {Δ: Env.CircuitEnv} {e₁ e₂ e₃: Ast.Expr}
  (h₁ : Eval.EvalProp σ Δ (exprEq e₁ e₂) (Ast.Value.vBool True))
  (h₂ : Eval.EvalProp σ Δ (exprEq e₁ e₃) (Ast.Value.vBool True)):
  Eval.EvalProp σ Δ (exprEq e₂ e₃) (Ast.Value.vBool True) := by
  unfold exprEq at h₁ h₂ ⊢
  cases h₁ with
  | Rel hv₁ hv₂ hv₃ => {
    cases h₂ with
    | Rel hu₁ hu₂ hu₃ => {
      rename_i v₁ v₂ u₁ u₂
      apply Eval.EvalProp.Rel
      exact hv₂
      exact hu₂
      have heq₁ := evalprop_var_deterministic_axiom hv₁ hu₁
      rw[← heq₁] at hu₃
      exact evalRel_eq_trans1 hv₃ hu₃
    }
  }

lemma evalProp_exprEq_trans2 {σ :Env.ValEnv} {Δ: Env.CircuitEnv} {e₁ e₂ e₃: Ast.Expr}
  (h₁ : Eval.EvalProp σ Δ (exprEq e₁ e₂) (Ast.Value.vBool True))
  (h₂ : Eval.EvalProp σ Δ (exprEq e₂ e₃) (Ast.Value.vBool True)):
  Eval.EvalProp σ Δ (exprEq e₁ e₃) (Ast.Value.vBool True) := by
  unfold exprEq at h₁ h₂ ⊢
  cases h₁ with
  | Rel hv₁ hv₂ hv₃ => {
    cases h₂ with
    | Rel hu₁ hu₂ hu₃ => {
      rename_i v₁ v₂ u₁ u₂
      apply Eval.EvalProp.Rel
      exact hv₁
      exact hu₂
      have heq₁ := evalprop_var_deterministic_axiom hv₂ hu₁
      rw[← heq₁] at hu₃
      exact evalRel_eq_trans2 hv₃ hu₃
    }
  }


lemma let_binding_assert_const
  (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (φ: Ast.Predicate) (n: F)
  (hΓx: Env.lookupTy Γ x = Ast.Ty.refin Ast.Ty.field φ)
  (hxy : y ≠ x):
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn y (Ast.Expr.assertE (Ast.Expr.var x) (Ast.Expr.constF n)) (Ast.Expr.var x))
    (Ty.refin Ast.Ty.field (Ast.Predicate.eq (Ast.Expr.constF n))) := by
    apply Ty.TypeJudgment.TE_LetIn
    apply Ty.TypeJudgment.TE_Assert
    apply Ty.TypeJudgment.TE_Var
    exact hΓx
    apply Ty.TypeJudgment.TE_ConstF
    have h_sub : @Ty.SubtypeJudgment σ Δ (Env.updateTy Γ y (Ty.bool.refin (Predicate.const (exprEq (Expr.var x) (Expr.constF n)))))
      (some (.refin Ast.Ty.field (.eq (.var x)))) (some (.refin Ast.Ty.field (.eq (.constF n)))) := by {
      apply Ty.SubtypeJudgment.TSub_Refine
      apply Ty.SubtypeJudgment.TSub_Refl
      intro v h
      unfold PropSemantics.tyenvToProp at h
      unfold PropSemantics.predToProp at ⊢
      simp_all
      unfold PropSemantics.exprToProp at ⊢
      have h_mem : (y, (Ty.bool.refin (Predicate.const (exprEq (Expr.var x) (Expr.constF n))))) ∈ Env.updateTy Γ y (Ty.bool.refin (Predicate.const (exprEq (Expr.var x) (Expr.constF n)))) := by {
        unfold Env.updateTy
        simp_all
      }
      apply h at h_mem
      unfold PropSemantics.varToProp at h_mem
      unfold Env.lookupTy at h_mem
      unfold Env.updateTy at h_mem
      simp_all
      have hp : PropSemantics.predToProp σ Δ (Predicate.const (exprEq (Expr.var x) (Expr.constF n))) (Expr.var y) := by {
        simp_all
      }
      unfold PropSemantics.predToProp at hp
      simp at hp
      unfold PropSemantics.exprToProp at hp
      intro hq
      exact evalProp_exprEq_trans2 hq hp
    }
    apply Ty.TypeJudgment.TE_SUB
    exact h_sub
    apply Ty.TypeJudgment.TE_Var
    exact @lookupTy_updateTy_of_ne Γ x y (Ty.field.refin φ) (Ty.bool.refin (Predicate.const (exprEq (Expr.var x) (Expr.constF n)))) hΓx hxy

lemma left_ne_zero_of_mul_eq_zero {x y : F}
  (h₁ : x ≠ 0)
  (h₂ : x * y = 0) :
  y = 0 := by {
    by_contra h₄
    set y_inv := y.inv
    have h₅: y * y_inv = 1 := by {
      apply ZMod.mul_inv_of_unit
      have : IsUnit y := by {
        have h₆ : y ≠ 0 := by simp_all
        rw[isUnit_non_zero] at h₆
        exact h₆
      }
      exact this
    }
    have h₆: x * (y * y_inv) = x := by {
      simp_all
    }
    have h₇: x * y * y_inv = x := by {
      rw[mul_assoc]
      exact h₆
    }
    rw[h₂] at h₇
    simp at h₇
    simp_all
}

/-
ih₁₃ : Eval.EvalProp σ Δ (Expr.var x) (Value.vF x_val)
h₁ : i₆ = x_val
y_val : F := i₁₂
ih₁₄ : Eval.EvalProp σ Δ (Expr.var y) (Value.vF y_val)
ih₁ : Eval.EvalProp σ Δ v (Value.vF y_val)
r₁ : xv₁ = y_val
r₅ : xv₃ = y_val
h₂ : xv₂ = y_val
h₃ : xv₄ = y_val
r₇ : x_val = 0 ∨ y_val = 0
inv_val : F := i₄
r₂ : -x_val * inv_val + 1 = y_val
ih₆ : Eval.EvalProp σ Δ (Expr.var inv) (Value.vF inv_val)
r₃ : -x_val * inv_val = i₁
⊢ Eval.EvalProp σ Δ (exprEq v (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)))
  (Value.vBool true)
-/

lemma iszero_field {x y inv: F}
  (h₁: y = -x * inv + 1)
  (h₂: x * y = 0):
  if x = 0 then y = 1 else y = 0 := by {
    by_cases hc : x = 0
    . simp_all
    . simp_all
}

lemma iszero_evalprop {x y inv: String} {v: Ast.Expr} {σ: Env.ValEnv} {Δ: Env.CircuitEnv}
  (h₁: Eval.EvalProp σ Δ (exprEq v ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr
                  FieldOp.add (Expr.constF 1))) (Value.vBool true))
  (h₂: Eval.EvalProp σ Δ (exprEq v (Expr.var y)) (Value.vBool true))
  (h₃: Eval.EvalProp σ Δ (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)) (Value.vBool true)) :
  Eval.EvalProp σ Δ (exprEq v (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0))) (Value.vBool true) := by {
    cases h₁ with
    | Rel ih₁ ih₂ r₁ => {
      rename_i v₁ v₂
      cases ih₂ with
      | FBinOp ih₃ ih₄ r₂ => {
        rename_i i₁ i₂
        cases ih₃ with
        | FBinOp ih₅ ih₆ r₃ => {
          rename_i i₃ i₄
          cases ih₅ with
          | FBinOp ih₇ ih₈ r₄ => {
            rename_i i₅ i₆
            cases h₂ with
            | Rel ih₉ ih₁₀ r₅ => {
              rename_i i₇ i₈
              cases h₃ with
              | Rel ih₁₁ ih₁₂ r₆ => {
                rename_i i₉ i₁₀
                cases ih₄
                cases ih₇
                cases ih₁₂
                cases ih₁₁ with
                | FBinOp ih₁₃ ih₁₄ r₇ => {
                  rename_i i₁₁ i₁₂
                  unfold Eval.evalFieldOp at r₂ r₃ r₄ r₇
                  simp_all
                  cases v₁ with
                  | vF xv₁ => {
                    cases v₂ with
                    | vF xv₂ => {
                      cases i₇ with
                      | vF xv₃ => {
                        cases i₈ with
                        | vF xv₄ => {
                          cases i₉ with
                          | vF xv₅ => {
                            simp_all
                            have h₁ := evalprop_var_deterministic_axiom ih₈ ih₁₃
                            have h₂ := evalprop_var_deterministic_axiom ih₁ ih₉
                            have h₃ := evalprop_var_deterministic_axiom ih₁₀ ih₁₄
                            simp_all
                            set x_val := i₁₁
                            set y_val := i₁₂
                            set inv_val := i₄
                            rw[← r₄] at r₃
                            rw[← r₃] at r₂
                            unfold Ast.exprEq
                            apply Eval.EvalProp.Rel
                            exact ih₁

                            sorry
                            sorry
                            sorry
                          }
                          | _ => simp_all
                          }
                        | _ => simp_all
                       }
                      | _ => simp_all
                    }
                    | _ => simp_all
                  }
                  | _ => simp_all
                }
              }
            }
          }
        }
      }
    }
  }

-- y := ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr
--                  FieldOp.add (Expr.constF 1))

/-
Eval.EvalProp σ Δ (exprEq v (Expr.var y)) (Value.vBool true) →
  Eval.EvalProp σ Δ (exprEq v (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)))
    (Value.vBool true)
-/

lemma iszero (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (φ₁ φ₂: Ast.Predicate)
  (x y inv u: String)
  (yv: F)
  (hxy: y ≠ x)
  (hxu: x ≠ u)
  (hyu: y ≠ u)
  (hx: Env.lookupTy Γ x = (Ast.Ty.refin Ty.field φ₁))
  (hinv: Env.lookupTy Γ inv = (Ast.Ty.refin Ty.field φ₁))
  :
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn y (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var x)) .mul (.var inv)) (.add) (.constF 1)) (Ast.Expr.letIn u (.assertE (.fieldExpr (.var x) .mul (.var y)) (.constF 0)) (.var y)))
    (Ty.refin Ast.Ty.field (Ast.Predicate.eq (.branch (.binRel (.var x) (.eq) (.constF 0)) (.constF 1) (.constF 0)))) := by {
  apply Ty.TypeJudgment.TE_LetIn
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_Var
  exact hx
  apply Ty.TypeJudgment.TE_Var
  exact hinv
  apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_LetIn
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_Var
  apply lookupTy_updateTy_of_ne
  exact hx
  exact hxy
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.lookupTy
  unfold Env.updateTy
  simp_all
  rfl
  apply Ty.TypeJudgment.TE_ConstF
  have h_sub : @Ty.SubtypeJudgment σ Δ (Env.updateTy
    (Env.updateTy Γ y
      (Ty.field.refin
        (Predicate.eq
          ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr
            FieldOp.add (Expr.constF 1)))))
    u (Ty.bool.refin (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))))
    (some (.refin Ast.Ty.field (.eq (.var y)))) (Ty.field.refin
    (Predicate.eq (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)))) := by {
      apply Ty.SubtypeJudgment.TSub_Refine
      apply Ty.SubtypeJudgment.TSub_Refl
      intro v h
      unfold PropSemantics.tyenvToProp at h
      unfold PropSemantics.predToProp at ⊢
      simp_all
      unfold PropSemantics.exprToProp at ⊢
      have h_mem₁ : (y, (Ty.field.refin
        (Predicate.eq
          ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr
            FieldOp.add (Expr.constF 1))))) ∈ Env.updateTy
        (Env.updateTy Γ y
          (Ty.field.refin
            (Predicate.eq
              ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr
                FieldOp.add (Expr.constF 1)))))
        u (Ty.bool.refin (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))) := by {
          unfold Env.updateTy
          simp_all
        }
      have h_mem₂ : (u, (Ty.bool.refin (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0))))) ∈ Env.updateTy
        (Env.updateTy Γ y
          (Ty.field.refin
            (Predicate.eq
              ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr
                FieldOp.add (Expr.constF 1)))))
        u (Ty.bool.refin (Predicate.const (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))) := by {
          unfold Env.updateTy
          simp_all
        }
      apply h at h_mem₁
      apply h at h_mem₂
      unfold PropSemantics.varToProp at h_mem₁ h_mem₂
      unfold Env.lookupTy at h_mem₁ h_mem₂
      unfold Env.updateTy at h_mem₁ h_mem₂
      simp_all
      sorry
    }
  apply Ty.TypeJudgment.TE_SUB
  exact h_sub
  apply Ty.TypeJudgment.TE_Var
  sorry
  exact φ₁
}

lemma eval_eq_vals (v₁ v₂: Ast.Value)
  : Eval.evalRelOp RelOp.eq v₁ v₂ = some true → v₁ = v₂ := by
  intro h
  cases v₁ <;> cases v₂ <;> simp [Eval.evalRelOp] at h ; try contradiction
  simp_all

lemma var_prop_implies_lookup (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (x: String) (ex: Expr)
  (h: PropSemantics.exprToProp σ Δ (Ast.exprEq (Expr.var x) ex))
  : Eval.EvalProp σ Δ ex (Env.lookupVal σ x) := by {
  unfold PropSemantics.exprToProp Ast.exprEq at h
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have veq: v₁ = v₂ := eval_eq_vals v₁ v₂ r₁
    cases ih₁ with
    | Var vx => {
      rw[← vx] at veq
      rw[← veq] at ih₂
      exact ih₂
    }
  }
}

lemma rw_eq_of_eval_prop
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (e₁ e₂: Expr) (v: Value)
  (h₁: Eval.EvalProp σ Δ (exprEq e₁ e₂) (.vBool true))
  (h₂: Eval.EvalProp σ Δ e₁ v)
  : Eval.EvalProp σ Δ e₂ v
  := by
  unfold exprEq at h₁
  cases h₁ with
  | Rel hs₁ hs₂ es₁ => {
    rename_i v₁ v₂
    have heq₁ := eval_eq_vals v₁ v₂ es₁
    rw[← heq₁] at hs₂
    have heq₂ := @evalprop_var_deterministic_axiom σ Δ e₁ v v₁ h₂ hs₁
    rw[← heq₂] at hs₂
    exact hs₂
  }

lemma rw_bop_int_add_left
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (e₁ e₂ e₃: Expr) (v: Value)
  (h₁: Eval.EvalProp σ Δ (exprEq e₁ e₃) (.vBool true))
  (h₂: Eval.EvalProp σ Δ (.fieldExpr e₁ FieldOp.add e₂) v)
  : Eval.EvalProp σ Δ (.fieldExpr e₃ FieldOp.add e₂) v
  := by
  unfold exprEq at h₁
  cases h₁ with
  | Rel hs₁ hs₂ es₁ => {
    rename_i v₁ v₂
    have heq₁ := eval_eq_vals v₁ v₂ es₁
    rw[← heq₁] at hs₂
    cases h₂ with
    | FBinOp ha₁ ha₂ ha₃ => {
      rename_i i₁ i₂
      have hv₁ := @evalprop_var_deterministic_axiom σ Δ e₁ v₁ (Value.vF i₁) hs₁ ha₁
      apply Eval.EvalProp.FBinOp
      rw[hv₁] at hs₂
      exact hs₂
      exact ha₂
      exact ha₃
    }
  }

lemma rw_bop_int_add_right
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (e₁ e₂ e₃: Expr) (v: Value)
  (h₁: Eval.EvalProp σ Δ (exprEq e₂ e₃) (.vBool true))
  (h₂: Eval.EvalProp σ Δ (.fieldExpr e₁ FieldOp.add e₂) v)
  : Eval.EvalProp σ Δ (.fieldExpr e₁ FieldOp.add e₃) v
  := by
  unfold exprEq at h₁
  cases h₁ with
  | Rel hs₂ hs₃ es => {
    rename_i v₂ v₃
    have heq₁ := eval_eq_vals v₂ v₃ es
    rw[← heq₁] at hs₃
    cases h₂ with
    | FBinOp ha₁ ha₂ ha₃ => {
      rename_i i₁ i₂
      have hv₂ := @evalprop_var_deterministic_axiom σ Δ e₂ v₂ (Value.vF i₂) hs₂ ha₂
      apply Eval.EvalProp.FBinOp
      rw[hv₂] at hs₃
      exact ha₁
      rw[hv₂] at hs₃
      exact hs₃
      exact ha₃
    }
  }

lemma rw_bop_int_add
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (e₁ e₂ e₃ e₄: Expr) (v: Value)
  (h₁: Eval.EvalProp σ Δ (exprEq e₁ e₃) (.vBool true))
  (h₂: Eval.EvalProp σ Δ (exprEq e₂ e₄) (.vBool true))
  (h₃: Eval.EvalProp σ Δ (.fieldExpr e₁ FieldOp.add e₂) v)
  : Eval.EvalProp σ Δ (.fieldExpr e₃ FieldOp.add e₄) v
  := by
  have htmp₁ := @rw_bop_int_add_left σ Δ e₁ e₂ e₃ v h₁ h₃
  have htmp₂ := @rw_bop_int_add_right σ Δ e₃ e₂ e₄ v h₂ htmp₁
  exact htmp₂

lemma rw_var_sub_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (ex: Expr)
  (hΓx : Env.lookupTy Γ x = Ty.refin Ty.field (Predicate.eq ex))
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.field (Predicate.eq (Expr.var x))))
      (pure (Ty.refin Ty.field (Predicate.eq (ex))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  intro v hmt
  have htyenv := Ty.tyenvToProp_implies_varToProp σ Δ Γ x Ast.Ty.field (Predicate.eq ex) hΓx hmt
  unfold PropSemantics.predToProp PropSemantics.exprToProp exprEq
  unfold PropSemantics.varToProp at htyenv
  unfold PropSemantics.predToProp at htyenv
  unfold PropSemantics.exprToProp at htyenv
  simp_all
  intro h
  cases h with
  | Rel h₁ h₂ e₁ => {
    apply Eval.EvalProp.Rel
    exact h₁
    rename_i v₁ v₂
    have h₃ := @rw_eq_of_eval_prop σ Δ (.var x) ex v₂ htyenv h₂
    exact h₃
    exact e₁
  }

lemma rw_var_sub_int_add
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x y: String) (ex ey: Expr)
  (hΓx : Env.lookupTy Γ x = Ty.refin Ty.field (Predicate.eq ex))
  (hΓy : Env.lookupTy Γ y = Ty.refin Ty.field (Predicate.eq ey))
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.field (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin Ty.field (Predicate.eq (Expr.fieldExpr ex FieldOp.add ey))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  intro v hmt
  unfold PropSemantics.predToProp PropSemantics.exprToProp
  simp_all
  have ht₁ := Ty.tyenvToProp_implies_varToProp σ Δ Γ x Ast.Ty.field (Predicate.eq ex) hΓx hmt
  have ht₂ := Ty.tyenvToProp_implies_varToProp σ Δ Γ y Ast.Ty.field (Predicate.eq ey) hΓy hmt
  unfold PropSemantics.varToProp at ht₁ ht₂
  unfold PropSemantics.predToProp at ht₁ ht₂
  unfold PropSemantics.exprToProp at ht₁ ht₂
  simp_all
  intro h
  cases h with
  | Rel h₁ h₂ e₁ => {
    rename_i v₁ v₂
    have heq₁ := eval_eq_vals v₁ v₂ e₁
    rw[← heq₁] at h₂
    have htmp₁ := @rw_bop_int_add σ Δ (.var x) (.var y) ex ey v₁ ht₁ ht₂ h₂
    apply Eval.EvalProp.Rel
    exact h₁
    exact htmp₁
    unfold Eval.evalRelOp
    simp_all
  }

lemma rw_const_add
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (n₁ n₂ n₃: F) (v: Value)
  (hn: n₁ + n₂ = n₃)
  (h: Eval.EvalProp σ Δ (.fieldExpr (.constF n₁) .add (.constF n₂)) v)
  : Eval.EvalProp σ Δ (.constF n₃) v
  := by
  cases h with
  | FBinOp ih₁ ih₂ r => {
    rename_i i₁ i₂
    unfold Eval.evalFieldOp at r
    simp_all
    cases ih₁
    cases ih₂
    rw[hn] at r
    rw[← r]
    apply Eval.EvalProp.ConstF
  }

lemma subtype_const_add_rw
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (n₁ n₂ n₃: F)
  (hn: n₁ + n₂ = n₃)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.field (Predicate.eq (.fieldExpr (.constF n₁) .add (.constF n₂)))))
      (pure (Ty.refin Ty.field (Predicate.eq (.constF (n₃)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  intro v hmt
  unfold PropSemantics.predToProp PropSemantics.exprToProp exprEq
  simp_all
  intro h
  cases h with
  | Rel ih₁ ih₂ r => {
    rename_i v₁ v₂
    apply Eval.EvalProp.Rel
    exact ih₁
    apply Eval.EvalProp.ConstF
    have hn₃ := @rw_const_add σ Δ n₁ n₂ n₃ v₂ hn ih₂
    cases hn₃
    exact r
  }
