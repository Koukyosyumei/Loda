import Loda.Typing
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Bool.Basic

open Ast

lemma two_mul_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro v
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at v ⊢
  simp [PropSemantics.exprToProp, hσx, Eval.evalIntegerOp, two_mul]

lemma two_mul_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.constF p 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro v
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at v ⊢
  simp[PropSemantics.exprToProp, hσx, Eval.evalIntegerOp, two_mul]

lemma add_comm_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv) (hσy : Env.lookupVal σ y = Value.vInt xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)))))
      (pure (Ty.refin Ty.int (Predicate.eq (Expr.intExpr (Expr.var y) IntegerOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, hσy, Eval.evalIntegerOp, Int.add_comm]

lemma add_comm_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv) (hσy : Env.lookupVal σ y = Value.vF p xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var y) FieldOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, hσy, Eval.evalIntegerOp, add_comm]

#check Bool.and_comm

lemma bool_and_comm
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x y: String) (xv yv: Bool)
  (hσx : Env.lookupVal σ x = Value.vBool xv)
  (hσy : Env.lookupVal σ y = Value.vBool yv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.bool (Predicate.eq (Expr.boolExpr (Expr.var x) BooleanOp.and (Expr.var y)))))
      (pure (Ty.refin Ty.bool (Predicate.eq (Expr.boolExpr (Expr.var y) BooleanOp.and (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  dsimp [PropSemantics.predToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[PropSemantics.exprToProp, hσx, hσy, Eval.evalBoolOp, Bool.and_comm]

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
      Eval.eval σ Δ e = (some (Ast.Value.vInt n)) := by {
  intro h
  cases h with
  | TE_ConstI => simp_all
  | TE_VarEnv => sorry
  | TE_App a b c => sorry
  | TE_SUB h₀ ht => sorry
  | TE_LetIn h₁ h₂ => sorry
  }

lemma eval_const_field_refin (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (e: Ast.Expr) (p n: ℕ)
  : @Ty.TypeJudgment σ Δ Γ e (Ty.refin (Ty.field p) (Predicate.eq (Expr.constF p n))) →
      Eval.eval σ Δ e = (some (Ast.Value.vF p n)) := by {
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
  (p: ℕ) (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (op: Ast.FieldOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Γ x = Ast.Ty.refin (Ast.Ty.field p) φ₁) (hΓy: Γ y = Ast.Ty.refin (Ast.Ty.field p) φ₂)
  : @Ty.TypeJudgment σ Δ Γ (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ty.refin (Ty.field p) (Predicate.eq (Expr.fieldExpr (Expr.var x) op (Expr.var y)))) := by
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
  (p : ℕ) (x y z: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (op: Ast.FieldOp) (φ₁ φ₂: Ast.Predicate)
  (hΓx: Γ x = Ast.Ty.refin (Ast.Ty.field p) φ₁) (hΓy: Γ y = Ast.Ty.refin (Ast.Ty.field p) φ₂) :
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn z (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y)) (Ast.Expr.var z))
    (Ty.refin (Ty.field p) (Ast.Predicate.eq (Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y)))) :=
by
  set e1 := Ast.Expr.fieldExpr (Ast.Expr.var x) op (Ast.Expr.var y)
  set e1_ty := Ty.refin (Ty.field p) (Ast.Predicate.eq e1)
  apply Ty.TypeJudgment.TE_LetIn
  · apply typed_field_expr_from_refined_vars <;> try assumption
  · set Γ' := Env.updateTy Γ z e1_ty
    have h_e1_has_type_e1_ty : @Ty.TypeJudgment σ Δ Γ e1 e1_ty := by
      apply typed_field_expr_from_refined_vars <;> try assumption
    have h_refinement_prop_holds :=
      Ty.typeJudgmentRefinementSound Γ (Ast.Ty.field p) e1 (Ast.Predicate.eq e1) h_e1_has_type_e1_ty
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

lemma field_refintype_implies_exists_field_value (p: ℕ) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (e: Predicate)
  : (Γ x = (Ty.field p).refin e) → PropSemantics.tyenvToProp σ Δ Γ x → ∃ (a: ℤ), Env.lookupVal σ x = Ast.Value.vF p a := by
  intro hx
  unfold PropSemantics.tyenvToProp
  simp_all
  set val := Env.lookupVal σ x
  cases val with
  | vF p' n => {
    simp_all
    intro hp
    rw[← hp]
    simp_all
    intro hq
    sorry
  }
  | _ => intro hσ; simp_all
