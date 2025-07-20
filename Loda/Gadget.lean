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
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.constF 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v h
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
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v h
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
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.bool (Predicate.eq (Expr.boolExpr (Expr.var x) BooleanOp.and (Expr.var y)))))
      (pure (Ty.refin Ty.bool (Predicate.eq (Expr.boolExpr (Expr.var y) BooleanOp.and (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v h
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
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.var y)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v h
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

lemma add_assoc_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x y z: String) (xv yv zv: ℤ)
  (hσx : Env.lookupVal σ x = Value.vInt xv)
  (hσy : Env.lookupVal σ y = Value.vInt yv)
  (hσz : Env.lookupVal σ z = Value.vInt zv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)) IntegerOp.mul (Expr.var z)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.intExpr (Expr.var x) IntegerOp.mul (Expr.var z)) IntegerOp.add (Expr.intExpr (Expr.var y) IntegerOp.mul (Expr.var z))))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, hσy, hσz, Eval.maximumRecursion, add_mul]

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

lemma isUnit_non_zero (p: ℕ) (x : ZMod p) (hp : Fact p.Prime) : x ≠ 0 ↔ IsUnit x := by
  simp_all

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

lemma field_refintype_implies_exists_field_value' (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (e: Predicate)
  : (Env.lookupTy Γ x = Ty.field.refin e) → PropSemantics.varToProp σ Δ Γ x → ∃ (a: F), Env.lookupVal σ x = Ast.Value.vF a := by
  intro hx
  unfold PropSemantics.varToProp
  simp_all
  set val := Env.lookupVal σ x
  cases val with
  | vF n => simp_all
  | _ => intro hσ; simp_all

lemma field_refintype_implies_exists_field_value (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (e: Predicate)
  : (Env.lookupTy Γ x = Ty.field.refin e) → PropSemantics.tyenvToProp σ Δ Γ → ∃ (a: F), Env.lookupVal σ x = Ast.Value.vF a := by
  intro hx hy
  have hv := Ty.tyenvToProp_implies_varToProp σ Δ Γ x Ast.Ty.field e hx hy
  exact field_refintype_implies_exists_field_value' σ Δ Γ x e hx hv

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
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.field (Predicate.eq (Expr.var x))))
      (pure (Ty.refin Ty.field (Predicate.eq (ex))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v
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
    obtain ⟨ht₁, ht₂⟩ := htyenv
    rename_i v₁ v₂
    have h₃ := @rw_eq_of_eval_prop σ Δ (.var x) ex v₂ ht₂ h₂
    exact h₃
    exact e₁
  }

lemma rw_var_sub_int_add
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x y: String) (ex ey: Expr)
  (hΓx : Env.lookupTy Γ x = Ty.refin Ty.field (Predicate.eq ex))
  (hΓy : Env.lookupTy Γ y = Ty.refin Ty.field (Predicate.eq ey))
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.field (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin Ty.field (Predicate.eq (Expr.fieldExpr ex FieldOp.add ey))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v
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
    obtain ⟨hto₁, htp₁⟩ := ht₁
    obtain ⟨hto₂, htp₂⟩ := ht₂
    apply Eval.EvalProp.Rel
    exact h₁
    have htmp₁ := @rw_bop_int_add σ Δ (.var x) (.var y) ex ey v₁ htp₁ htp₂ h₂
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
  (hmt : PropSemantics.tyenvToProp σ Δ Γ)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.field (Predicate.eq (.fieldExpr (.constF n₁) .add (.constF n₂)))))
      (pure (Ty.refin Ty.field (Predicate.eq (.constF (n₃)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  exact hmt
  intro v
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
