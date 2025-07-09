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

lemma int_lookup_add
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (x y: String) (xv yv: ℤ) (v: Value)
  (hσx: Env.lookupVal σ x = Value.vInt xv)  (hσy: Env.lookupVal σ y = Value.vInt yv)
  (hee: Eval.EvalProp σ Δ (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)) v):
  v = Value.vInt (xv + yv) := by
  cases hee with
  | @IntOp _ _ _ _ _ i₁ i₂ hi₁ hi₂ hi₃ r₂ => {
    apply Eval.EvalProp.Var at hσx
    apply Eval.EvalProp.Var at hσy
    have ieq₁ := @evalprop_var_deterministic σ Δ x (Value.vInt i₁) (Value.vInt xv) hi₂ hσx
    have ieq₂ := @evalprop_var_deterministic σ Δ y (Value.vInt i₂) (Value.vInt yv) hi₃ hσy
    rw[ieq₁, ieq₂] at r₂
    unfold Eval.evalIntegerOp at r₂
    simp_all
  }

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
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (x y: String) (xv yv: ℤ) (v: Value)
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


lemma two_mul_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  intro v h
  dsimp [PropSemantics.predToProp, PropSemantics.exprToProp] at h ⊢
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have hv2 : v₂ = Value.vInt (xv + xv) := @int_lookup_add σ Δ x x xv xv v₂ hσx hσx ih₂
    rw[← two_mul] at hv2
    apply Eval.EvalProp.Rel
    . exact ih₁
    . apply Eval.EvalProp.IntOp Eval.EvalProp.ConstInt
      . apply Eval.EvalProp.Var
        exact hσx
      unfold Eval.evalIntegerOp; rfl
    simp_all
  }

lemma two_mul_field
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.constF 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
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

lemma add_comm_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv yv: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv) (hσy : Env.lookupVal σ y = Value.vInt yv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var y) IntegerOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
  intro v h
  dsimp [PropSemantics.predToProp, PropSemantics.exprToProp] at h ⊢
  cases h with
  | @Rel σ Δ v _ RelOp.eq v₁ v₂ _ ih₁ ih₂ r₁ => {
    have hv2 : v₂ = Value.vInt (xv + yv) := @int_lookup_add σ Δ x y xv yv v₂ hσx hσy ih₂
    rw [← Int.add_comm] at hv2
    unfold exprEq
    apply Eval.EvalProp.Rel
    . exact ih₁
    . apply Eval.EvalProp.IntOp
      apply Eval.EvalProp.Var
      exact hσy
      apply Eval.EvalProp.Var
      exact hσx
      simp_all
      rw[← hv2]
    simp_all
  }

lemma add_comm_field
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv yv: ℕ) (hσx : Env.lookupVal σ x = Value.vF xv) (hσy : Env.lookupVal σ y = Value.vF yv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine Ty.SubtypeJudgment.TSub_Refl
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
    simp_all
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

/-
lemma mul_comm_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv) (hσy : Env.lookupVal σ y = Value.vInt xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) IntegerOp.mul (Expr.var y)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var y) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, hσy, Eval.evalIntegerOp, Int.mul_comm]

lemma mul_comm_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv) (hσy : Env.lookupVal σ y = Value.vF p xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.var y)))))
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, hσy, mul_comm]

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

lemma eval_const_int_refin (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (e: Ast.Expr) (n: ℕ)
  : @Ty.TypeJudgment σ Δ Γ e (Ty.refin Ty.int (Predicate.eq (Expr.constInt n))) →
      Eval.EvalProp σ Δ e (Ast.Value.vInt n) := by {
  intro h
  cases h with
  | TE_ConstI => apply Eval.EvalProp.ConstInt
  | TE_VarEnv x a => {
      apply Eval.EvalProp.Var
      sorry
  }
  | TE_App a b c => sorry
  | TE_SUB h₀ ht => sorry
  | TE_LetIn h₁ h₂ => sorry
  }

lemma eval_const_field_refin (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (e: Ast.Expr) (p n: ℕ)
  : @Ty.TypeJudgment σ Δ Γ e (Ty.refin (Ty.field) (Predicate.eq (Expr.constF n))) →
      Eval.eval σ Δ e = (some (Ast.Value.vF n)) := by {
  intro h
  cases h with
  | TE_ConstF => simp_all
  | TE_VarEnv => sorry
  | TE_App a b c => sorry
  | TE_SUB h₀ ht => sorry
  | TE_LetIn h₁ h₂ => sorry
  }

lemma typed_int_expr_from_refined_vars
  (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (op: Ast.IntegerOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int φ₁) (hΓy: Γ y = Ast.Ty.refin Ast.Ty.int φ₂)
  : @Ty.TypeJudgment σ Δ Γ (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) op (Expr.var y)))) := by
  apply Ty.TypeJudgment.TE_BinOpInt
  apply Ty.TypeJudgment.TE_Var φ₁
  simp [hΓx]
  apply Ty.TypeJudgment.TE_Var φ₂
  simp [hΓy]

lemma typed_field_expr_from_refined_vars
  (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (op: Ast.FieldOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Γ x = Ast.Ty.refin (Ast.Ty.field) φ₁) (hΓy: Γ y = Ast.Ty.refin (Ast.Ty.field) φ₂)
  : @Ty.TypeJudgment σ Δ Γ (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ty.refin (Ty.field) (Predicate.eq (Expr.fieldExpr (Expr.var x) op (Expr.var y)))) := by
  apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_Var φ₁
  simp [hΓx]
  apply Ty.TypeJudgment.TE_Var φ₂
  simp [hΓy]

lemma let_binding_int_op_type_preservation
  (x y z: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (op: Ast.IntegerOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int φ₁) (hΓy: Γ y = Ast.Ty.refin Ast.Ty.int φ₂) :
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn z (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)) (Ast.Expr.var z))
    (Ty.refin Ty.int (Ast.Predicate.eq (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)))) :=
by
  set e1 := Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)
  set e1_ty := Ty.refin Ty.int (Ast.Predicate.eq e1)
  apply Ty.TypeJudgment.TE_LetIn
  · apply typed_int_expr_from_refined_vars <;> try assumption
  · set Γ' := Env.updateTy Γ z e1_ty
    have h_e1_has_type_e1_ty : @Ty.TypeJudgment σ Δ Γ e1 e1_ty := by
      apply typed_int_expr_from_refined_vars <;> try assumption
    have h_refinement_prop_holds :=
      Ty.typeJudgmentRefinementSound Γ Ast.Ty.int e1 (Ast.Predicate.eq e1) h_e1_has_type_e1_ty
    have hΓ'_z_eq_e1_ty : Γ' z = e1_ty := by
      simp [Γ', Env.updateTy]
    apply Ty.TypeJudgment.TE_VarEnv
    exact hΓ'_z_eq_e1_ty

lemma let_binding_field_op_type_preservation
  (x y z: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (op: Ast.FieldOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Γ x = Ast.Ty.refin (Ast.Ty.field) φ₁) (hΓy: Γ y = Ast.Ty.refin (Ast.Ty.field) φ₂) :
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
    have hΓ'_z_eq_e1_ty : Γ' z = e1_ty := by
      simp [Γ', Env.updateTy]
    apply Ty.TypeJudgment.TE_VarEnv
    exact hΓ'_z_eq_e1_ty

lemma int_refintype_implies_exists_int_value (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (e: Predicate)
  : (Γ x = Ty.int.refin e) → PropSemantics.tyenvToProp σ Δ Γ x → ∃ (a: ℤ), Env.lookupVal σ x = Ast.Value.vInt a := by
  intro hx
  unfold PropSemantics.tyenvToProp
  simp_all
  set val := Env.lookupVal σ x
  cases val with
  | vInt n => simp_all
  | _ => intro hσ; simp_all

lemma eval_eq_vals (v₁ v₂: Ast.Value)
  : Eval.evalRelOp RelOp.eq v₁ v₂ = some true → v₁ = v₂ := by
  intro h
  cases v₁ <;> cases v₂ <;> simp [Eval.evalRelOp] at h <;> try contradiction
  simp_all
  congr


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

lemma rw_var
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (ex: Expr)
  (hΓx : Γ x = Ty.refin Ty.int (Predicate.eq ex))
  (htyenv: PropSemantics.tyenvToProp σ Δ Γ x)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.var x))))
      (pure (Ty.refin Ty.int (Predicate.eq (ex))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  intro v
  unfold PropSemantics.predToProp PropSemantics.exprToProp exprEq
  unfold PropSemantics.tyenvToProp at htyenv
  simp_all
  unfold PropSemantics.predToProp at htyenv
  unfold PropSemantics.exprToProp at htyenv
  simp_all
  intro h
  cases h with
  | Rel h₁ h₂ e₁ => {
    apply Eval.EvalProp.Rel
    exact h₁
    obtain ⟨ht₁, ht₂⟩ := htyenv
    sorry
    exact e₁
  }



/-
lemma rw_var_sub_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x y: String) (ex ey: Expr)
  (hΓx : Γ x = Ty.refin Ty.int (Predicate.eq ex))
  (hΓy : Γ y = Ty.refin Ty.int (Predicate.eq ey))
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr ex IntegerOp.add ey))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  . apply Ty.SubtypeJudgment.TSub_Refl
  intro v
  unfold PropSemantics.predToProp PropSemantics.exprToProp exprEq
  simp_all
  sorry
-/
