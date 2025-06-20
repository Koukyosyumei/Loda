import Loda.Typing
import Loda.Gadget

@[simp]
def mulCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (fun _ => Ast.Expr.constBool true)),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (fun v => Ast.exprEq (Ast.Expr.var v) (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}

@[simp]
def assertCircuit : Ast.Circuit := {
  name   := "assert1",
  inputs := ("x", Ast.Ty.refin (Ast.Ty.field 5) (fun v => Ast.exprEq (Ast.Expr.var v) (Ast.Expr.constF 5 1))),
  output := ("out", Ast.Ty.refin (Ast.Ty.field 5) (fun v => Ast.exprEq (Ast.Expr.var v) ((Ast.Expr.constF 5 2)))),
  body   := (Ast.Expr.letIn "b" (Ast.Expr.assertE (Ast.Expr.var "x") (Ast.Expr.constF 5 1))
                (Ast.Expr.letIn "out" (Ast.Expr.fieldExpr (Ast.Expr.var "x") Ast.FieldOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out")))
}

def Δ : Env.CircuitEnv := [("mul", mulCircuit), ("assert1", assertCircuit)]

theorem mulCircuit_correct : (Ty.circuitCorrect Δ mulCircuit) := by
  unfold Ty.circuitCorrect
  unfold mulCircuit
  simp_all
  intro x hs hσ
  set envs := Ty.makeEnvs mulCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Γ "x" = (Ast.Ty.int.refin (fun _ => Ast.Expr.constBool true)) := rfl
  have h_body := @let_binding_int_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.IntegerOp.add (fun _ => Ast.Expr.constBool true) (fun _ => Ast.Expr.constBool true) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := int_refintype_implies_exists_int_value σ Δ Γ "x" (fun _ => Ast.Expr.constBool true) hΓ hσ
  have h_sub := two_mul_int σ Δ Γ "x" vv hv_eq
  exact Ty.TypeJudgment.TE_SUB h_sub h_body

theorem assertCircuit_correct : (Ty.circuitCorrect Δ assertCircuit) := by
  unfold Ty.circuitCorrect
  unfold assertCircuit
  simp_all
  intro x hs hσ
  set envs := Ty.makeEnvs assertCircuit x
  set σ := envs.1
  set Γ := envs.2
  unfold Ty.makeEnvs
  simp_all
  have hΓ : Γ "x" = Ast.Ty.refin (Ast.Ty.field 5) (fun v => Ast.exprEq (Ast.Expr.var v) (.constF 5 1)) := by rfl
  have hx₁ : @Ty.TypeJudgment σ Δ Γ (.var "x") ((Ast.Ty.field 5).refin (fun v => Ast.exprEq (Ast.Expr.var v) (.var "x"))) := by {
    apply Ty.TypeJudgment.TE_Var
    exact hΓ
  }
  have he₂: PropSemantics.exprToProp σ Δ (Ast.exprEq (Ast.Expr.var "x") (Ast.Expr.constF 5 1)) := by {
    unfold PropSemantics.tyenvToProp at hσ
    cases hσ with
    | intro hl hr
    exact hr
  }
  have hx₂ : @Ty.TypeJudgment σ Δ Γ (.var "x") ((Ast.Ty.field 5).refin (fun v => Ast.exprEq (Ast.Expr.var v) (.constF 5 1))) := by {
    apply @Ty.varRefineSound σ Δ Γ "x" (Ast.Ty.field 5)
    set φ₂ := fun s => (Ast.exprEq (Ast.Expr.var s) (Ast.Expr.constF 5 1))
    have φ₂' : φ₂ "x" = Ast.exprEq (Ast.Expr.var "x") (Ast.Expr.constF 5 1) := rfl
    rw[← φ₂'] at he₂
    exact he₂
    exact hΓ
  }
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ 5 Ast.FieldOp.add
                  (fun v => Ast.exprEq (Ast.Expr.var v) (Ast.Expr.constF 5 1))
                  (fun v => Ast.exprEq (Ast.Expr.var v) (Ast.Expr.constF 5 1)) hΓ hΓ
  set Γ' := (Env.updateTy
      (Env.updateTy (fun x ↦ Ast.Ty.unit) "x"
        ((Ast.Ty.field 5).refin fun v ↦ Ast.exprEq (Ast.Expr.var v) (Ast.Expr.constF 5 1)))
      "b" (Ast.Ty.unit.refin fun x ↦ Ast.exprEq (Ast.Expr.var "x") (Ast.Expr.constF 5 1)))
  have hx₃ : @Ty.TypeJudgment σ Δ Γ' (.var "x") ((Ast.Ty.field 5).refin (fun v => Ast.exprEq (Ast.Expr.var v) (.constF 5 1))) := by {
    apply @Ty.varRefineSound σ Δ Γ' "x" (Ast.Ty.field 5)
    set φ₂ := fun s => (Ast.exprEq (Ast.Expr.var s) (Ast.Expr.constF 5 1))
    have φ₂' : φ₂ "x" = Ast.exprEq (Ast.Expr.var "x") (Ast.Expr.constF 5 1) := rfl
    rw[← φ₂'] at he₂
    exact he₂
    exact hΓ
  }
  apply Ty.TypeJudgment.TE_LetIn
  . apply Ty.TypeJudgment.TE_Assert
    exact hx₂
    apply Ty.TypeJudgment.TE_ConstF
  . apply Ty.TypeJudgment.TE_LetIn
    apply Ty.TypeJudgment.TE_BinOpField
    exact hx₃
    exact hx₃
    sorry

def σ : Env.ValEnv := [("x", Ast.Value.vInt 5)]
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (fun _ => Ast.Expr.constBool true)
#eval Eval.eval σ Δ mulCircuit.body
