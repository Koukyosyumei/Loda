import Loda.Typing

open Ast

lemma two_mul_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vInt vv) := by
    apply Ty.exprIntVSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, Eval.evalIntegerOp, hv_eq, two_mul]
  simp_all

lemma two_mul_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.constF p 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vF p vv) := by
    apply Ty.exprFielVdSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, Eval.evalIntegerOp, hv_eq, two_mul]
  simp_all

lemma add_comm_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv) (hσy : Env.lookupVal σ y = Value.vInt xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var y) IntegerOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vInt vv) := by
    apply Ty.exprIntVSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, hσy, Eval.evalIntegerOp, hv_eq]
  simp[Int.add_comm]
  simp_all

lemma add_comm_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv) (hσy : Env.lookupVal σ y = Value.vF p xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var y)))))
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var y) FieldOp.add (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vF p vv) := by
    apply Ty.exprFielVdSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, hσy, Eval.evalIntegerOp, hv_eq]
  simp[add_comm]
  simp_all

lemma mul_comm_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℤ) (hσx : Env.lookupVal σ x = Value.vInt xv) (hσy : Env.lookupVal σ y = Value.vInt xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.mul (Expr.var y)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var y) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vInt vv) := by
    apply Ty.exprIntVSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, hσy, Eval.evalIntegerOp, hv_eq]
  simp[Int.mul_comm]
  simp_all

lemma mul_comm_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x y: String) (xv xu: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv) (hσy : Env.lookupVal σ y = Value.vF p xu)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.var y)))))
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var y) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vF p vv) := by
    apply Ty.exprFielVdSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, hσy, hv_eq]
  simp[mul_comm]
  simp_all

lemma add_assoc_int
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x y z: String) (xv yv zv: ℤ)
  (hσx : Env.lookupVal σ x = Value.vInt xv)
  (hσy : Env.lookupVal σ y = Value.vInt yv)
  (hσz : Env.lookupVal σ z = Value.vInt zv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var y)) IntegerOp.mul (Expr.var z)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.intExpr (Expr.var x) IntegerOp.mul (Expr.var z)) IntegerOp.add (Expr.intExpr (Expr.var y) IntegerOp.mul (Expr.var z))))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vInt vv) := by
    apply Ty.exprIntVSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, hσy, hσz, Eval.evalIntegerOp, hv_eq] at  h ⊢
  unfold Eval.maximumRecursion at h ⊢
  simp_all
  unfold Eval.maximumRecursion at hv_eq
  rw[hv_eq] at h ⊢
  simp_all
  simp[add_mul]

lemma mul_one_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.constF p 1)))))
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.var x))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  obtain ⟨vv, hv_eq⟩ : ∃ vv, Eval.eval σ Δ v = some (Value.vF p vv) := by
    apply Ty.exprFielVdSound at h; exact h
  dsimp [PropSemantics.exprToProp, Eval.eval, exprEq, decide_eq_true] at h ⊢
  simp[hσx, hv_eq] at h ⊢
  unfold Eval.maximumRecursion at h ⊢
  simp_all

lemma add_zero_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.constF p 0)))))
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.var x))))
  := by sorry

lemma mul_inv_field {p: ℕ}
  (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (x: String) (xv: ℕ) (hσx : Env.lookupVal σ x = Value.vF p xv) (hxv_ne_zero: xv ≠ 0)
  : @Ty.SubtypeJudgment σ Δ Γ
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.mul (Expr.fieldExpr (Expr.constF p 1) FieldOp.div (Expr.var x))))))
      (pure (Ty.refin (Ty.field p) (exprEq v (Expr.constF p 1))))
  := by sorry

lemma typed_int_expr_from_refined_vars
  (x y: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (op: Ast.IntegerOp) (φ₁ φ₂: Ast.Expr)
  (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int φ₁) (hΓy: Γ y = Ast.Ty.refin Ast.Ty.int φ₂)
  : @Ty.TypeJudgment σ Δ Γ (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) op (Expr.var y)))) := by
  apply Ty.TypeJudgment.TE_BinOpInt
  apply Ty.TypeJudgment.TE_Var φ₁
  simp [hΓx]
  apply Ty.TypeJudgment.TE_Var φ₂
  simp [hΓy]

lemma let_binding_int_op_type_preservation
  (x y z: String) (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (op: Ast.IntegerOp) (φ₁ φ₂: Ast.Expr)
  (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int φ₁) (hΓy: Γ y = Ast.Ty.refin Ast.Ty.int φ₂) :
  @Ty.TypeJudgment σ Δ Γ
    (Ast.Expr.letIn z (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)) (Ast.Expr.var z))
    (Ty.refin Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)))) :=
by
  set e1 := Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)
  set e1_ty := Ty.refin Ty.int (Ast.exprEq Ast.v e1)
  apply Ty.TypeJudgment.TE_LetIn
  · apply typed_int_expr_from_refined_vars <;> try assumption
  · set Γ' := Env.updateTy Γ z e1_ty
    have h_e1_has_type_e1_ty : @Ty.TypeJudgment σ Δ Γ e1 e1_ty := by
      apply typed_int_expr_from_refined_vars <;> try assumption
    have h_refinement_prop_holds : PropSemantics.exprToProp σ Δ (Ast.exprEq Ast.v e1) :=
      Ty.typeJudgmentRefinementSound Γ Ast.Ty.int e1 (Ast.exprEq Ast.v e1) h_e1_has_type_e1_ty
    have hΓ'_z_eq_e1_ty : Γ' z = e1_ty := by
      simp [Γ', Env.updateTy]
    rw[← hΓ'_z_eq_e1_ty]
    apply @Ty.varRefineSound σ Δ Γ' z Ast.Ty.int (Ast.exprEq Ast.v e1)
    exact h_refinement_prop_holds
    exact hΓ'_z_eq_e1_ty

lemma int_refintype_implies_exists_int_value (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (e: Expr)
  : (Γ x = Ty.int.refin e) → PropSemantics.tyenvToProp σ Δ Γ x → ∃ (a: ℤ), Env.lookupVal σ x = Ast.Value.vInt a := by
  intro hx
  unfold PropSemantics.tyenvToProp
  simp_all
  set val := Env.lookupVal σ x
  cases val with
  | vInt n => simp_all
  | _ => intro hσ; simp_all
