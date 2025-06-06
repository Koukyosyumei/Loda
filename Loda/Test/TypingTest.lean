import Loda.Typing

open Ast

-- refinement subtyping: {v:int | y + y} <: {v:int | 2 * y}
-- (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var "y"))
lemma two_mul_I
  (fuel: ℕ) (σ: Env.ValEnv) (δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℤ) (hσx : σ x = Value.vInt xv)
  : @Ty.SubtypeJudgment fuel σ δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  have hv : ∃ vv, Eval.eval fuel σ δ v = some (Value.vInt vv) := by {
    apply Ty.exprIntVSound at h
    exact h
  }
  obtain ⟨vv, hv_eq⟩ := hv
  dsimp [PropSemantics.exprToProp, Eval.eval] at h ⊢
  unfold exprEq
  unfold exprEq at h
  simp [decide_eq_true] at h ⊢
  rw[hσx]
  simp[Eval.evalIntegerOp]
  rw[hv_eq]
  rw[two_mul]
  simp_all

lemma two_mul_F {p: ℕ}
  (fuel: ℕ) (σ: Env.ValEnv) (δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment fuel σ δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.fieldExpr (Expr.constF p 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  have hv : ∃ vv, Eval.eval fuel σ δ v = some (Value.vF p vv) := by {
    apply Ty.exprFielVdSound at h
    exact h
  }
  obtain ⟨vv, hv_eq⟩ := hv
  dsimp [PropSemantics.exprToProp, Eval.eval] at h ⊢
  unfold exprEq
  unfold exprEq at h
  simp [decide_eq_true] at h ⊢
  rw[hσx]
  simp[Eval.evalIntegerOp]
  rw[hv_eq]
  rw[two_mul]
  simp_all

lemma typed_int_expr_from_refined_vars
  (fuel: ℕ) (x y: String) (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ: Env.TyEnv)
  (op: Ast.IntegerOp)
  (φ₁ φ₂: Ast.Expr)
  (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int φ₁)
  (hΓy: Γ y = Ast.Ty.refin Ast.Ty.int φ₂)
  : @Ty.TypeJudgment fuel σ δ Γ (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) op (Expr.var y)))) := by
  apply Ty.TypeJudgment.TE_BinOpInt
  apply Ty.TypeJudgment.TE_Var φ₁
  simp [hΓx]
  apply Ty.TypeJudgment.TE_Var φ₂
  simp [hΓy]

lemma let_binding_int_op_type_preservation
  (fuel: ℕ) (x y z: String) (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (op: Ast.IntegerOp)
  (φ₁ φ₂: Ast.Expr)
  (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int φ₁) (hΓy: Γ y = Ast.Ty.refin Ast.Ty.int φ₂) :
  @Ty.TypeJudgment fuel σ δ Γ
    (Ast.Expr.letIn z
      (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y))
      (Ast.Expr.var z))
    (Ty.refin Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)))) :=
by
  set e1 := Ast.Expr.intExpr (Ast.Expr.var x) op (Ast.Expr.var y)
  set e1_ty := Ty.refin Ty.int (Ast.exprEq Ast.v e1)
  apply Ty.TypeJudgment.TE_LetIn
  · apply typed_int_expr_from_refined_vars <;> try assumption
  · set Γ' := Env.updateTy Γ z e1_ty
    have h_e1_has_type_e1_ty : @Ty.TypeJudgment fuel σ δ Γ e1 e1_ty := by
      apply typed_int_expr_from_refined_vars <;> try assumption
    have h_refinement_prop_holds : PropSemantics.exprToProp fuel σ δ (Ast.exprEq Ast.v e1) :=
      Ty.typeJudgmentRefinementSound Γ Ast.Ty.int e1 (Ast.exprEq Ast.v e1) h_e1_has_type_e1_ty
    have hΓ'_z_eq_e1_ty : Γ' z = e1_ty := by
      simp [Γ', Env.updateTy]
    rw[← hΓ'_z_eq_e1_ty]
    apply @Ty.varRefineSound fuel σ δ Γ' z Ast.Ty.int (Ast.exprEq Ast.v e1)
    exact h_refinement_prop_holds
    exact hΓ'_z_eq_e1_ty

@[simp]
def mulCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}
def Δ : Env.CircuitEnv := fun nm => if nm = "mul" then mulCircuit else mulCircuit

#eval Value.vStar != Value.vStar

theorem mulCircuit_correct : (Ty.circuitCorrect 1000 Δ mulCircuit) := by
  unfold Ty.circuitCorrect
  unfold mulCircuit
  simp_all
  intro x hs hσ
  set σ := (Env.updateVal (fun x ↦ Value.vStar) "x" x)
  set Γ := (Env.updateTy (fun x ↦ Ty.unit) "x" (Ty.int.refin (Expr.constBool true)))
  have h_body :
    Ty.TypeJudgment
      (Env.updateTy (fun _ => Ast.Ty.unit) "x" (Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)))
      (Ast.Expr.letIn "out"
         (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x"))
         (Ast.Expr.var "out"))
      (Ast.Ty.refin Ast.Ty.int
         (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))) := by {
          apply @let_binding_int_op_type_preservation 1000 "x" "x" "out" σ Δ Γ
          simp [Γ]
          rfl
          simp [Γ]
          rfl
         }
  unfold PropSemantics.tyenvToProp at hσ
  simp [Γ] at hσ
  have hσ₁ : σ "x" = x := by {
    simp [σ]
    rfl
  }
  have h : ∃ (a : ℤ), σ "x" = Ast.Value.vInt a := by
    cases x with
    | vInt n =>
      use n
    | _ =>
      simp [hσ₁] at hσ
      simp_all
      cases hσ with
      | intro left right => {
        contradiction
      }
  obtain ⟨vv, hv_eq⟩ := h
  have h_sub :
    @Ty.SubtypeJudgment 1000 σ Δ Γ
      (pure (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))))
      (pure (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x"))))) := by {
        apply two_mul_I 1000 σ Δ Γ "x" vv
        simp [σ]
        simp_all
        rfl
      }
  exact Ty.TypeJudgment.TE_SUB h_sub h_body


def σ : Env.ValEnv := fun x =>
  if x = "x" then Ast.Value.vInt 5 else Ast.Value.vStar
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)
#eval Eval.eval 1000 σ Δ mulCircuit.body
