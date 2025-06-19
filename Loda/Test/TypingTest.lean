import Loda.Typing
import Loda.Gadget

@[simp]
def mulCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}

@[simp]
def assertCircuit : Ast.Circuit := {
  name   := "assert1",
  inputs := ("x", Ast.Ty.refin (Ast.Ty.field 5) (Ast.exprEq Ast.v (Ast.Expr.constF 5 1))),
  output := ("out", Ast.Ty.refin (Ast.Ty.field 5) (Ast.exprEq Ast.v (Ast.Expr.fieldExpr (Ast.Expr.constF 5 1) Ast.FieldOp.add (Ast.Expr.constF 5 1)))),
  body   := (Ast.Expr.letIn "b" (Ast.Expr.assertE (Ast.Expr.var "x") (Ast.Expr.constF 5 1))
                (Ast.Expr.fieldExpr (Ast.Expr.var "x") Ast.FieldOp.add (Ast.Expr.var "x")) )
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
  have hΓ : Γ "x" = (Ast.Ty.int.refin (Ast.Expr.constBool true)) := rfl
  have h_body := @let_binding_int_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.IntegerOp.add (Ast.Expr.constBool true) (Ast.Expr.constBool true) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := int_refintype_implies_exists_int_value σ Δ Γ "x" (Ast.Expr.constBool true) hΓ hσ
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
  have hΓ : Γ "x" = Ast.Ty.refin (Ast.Ty.field 5) (Ast.exprEq Ast.v (.constF 5 1)) := by rfl
  have hx₁ : @Ty.TypeJudgment σ Δ Γ (.var "x") ((Ast.Ty.field 5).refin (Ast.exprEq Ast.v (.var "x"))) := by {
    apply Ty.TypeJudgment.TE_Var
    exact hΓ
  }
  have he₂: PropSemantics.exprToProp σ Δ (Ast.exprEq Ast.v (Ast.Expr.constF 5 1)) := by {
    unfold PropSemantics.tyenvToProp at hσ
    cases hσ with
    | intro hl hr
    exact hr
  }
  have hx₂ : @Ty.TypeJudgment σ Δ Γ (.var "x") ((Ast.Ty.field 5).refin (Ast.exprEq Ast.v (.constF 5 1))) := by {
    apply @Ty.varRefineSound σ Δ Γ "x" (Ast.Ty.field 5)
    exact he₂
    exact hΓ
  }
  set Γ' := (Env.updateTy
    (Env.updateTy (fun x ↦ Ast.Ty.unit) "x" ((Ast.Ty.field 5).refin (Ast.exprEq Ast.v (Ast.Expr.constF 5 1)))) "b"
    (Ast.Ty.unit.refin (Ast.exprEq (Ast.Expr.var "x") (Ast.Expr.constF 5 1))))
  have hs₂: @Ty.SubtypeJudgment σ Δ Γ'
              (pure ((Ast.Ty.field 5).refin (Ast.exprEq Ast.v ((Ast.Expr.var "x").fieldExpr Ast.FieldOp.add (Ast.Expr.var "x")))))
              (pure ((Ast.Ty.field 5).refin (Ast.exprEq Ast.v ((Ast.Expr.constF 5 1).fieldExpr Ast.FieldOp.add (Ast.Expr.constF 5 1))))) := by {
    apply Ty.SubtypeJudgment.TSub_Refine
    . apply Ty.SubtypeJudgment.TSub_Refl
    intro h
    unfold PropSemantics.exprToProp at h
    sorry
  }
  apply Ty.TypeJudgment.TE_LetIn
  . apply Ty.TypeJudgment.TE_Assert
    exact hx₂
    apply Ty.TypeJudgment.TE_ConstF
  . apply Ty.TypeJudgment.TE_SUB
    exact hs₂
    apply Ty.TypeJudgment.TE_BinOpField
    . apply Ty.TypeJudgment.TE_Var
      unfold Env.updateTy
      simp_all
      rfl
    . apply Ty.TypeJudgment.TE_Var
      unfold Env.updateTy
      simp_all
      rfl

def σ : Env.ValEnv := [("x", Ast.Value.vInt 5)]
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)
#eval Eval.eval σ Δ mulCircuit.body
