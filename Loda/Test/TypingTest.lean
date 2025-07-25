import Loda.Typing
import Loda.Gadget

@[simp]
def adderCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.field (Ast.Predicate.const (Ast.Expr.constBool true))),
  output := ("out", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.fieldExpr (Ast.Expr.constF 2) Ast.FieldOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.fieldExpr (Ast.Expr.var "x") Ast.FieldOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}

@[simp]
def addOneCircuit : Ast.Circuit := {
  name   := "assert1",
  inputs := ("x", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.constF 1))),
  output := ("out", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.fieldExpr (Ast.Expr.constF 1) Ast.FieldOp.add (Ast.Expr.constF 1)))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.fieldExpr (Ast.Expr.var "x") Ast.FieldOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}

@[simp]
def identityCircuit : Ast.Circuit := {
  name   := "identity",
  inputs := ("x", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.const (Ast.Expr.constBool true))),
  output := ("out", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.var "x"))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.var "x") (Ast.Expr.var "out"))
}

@[simp]
def assertCircuit : Ast.Circuit := {
  name   := "identity",
  inputs := ("x", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.const (Ast.Expr.constBool true))),
  output := ("x", Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.constF 1))),
  body   := (Ast.Expr.letIn "u" (Ast.Expr.assertE (Ast.Expr.var "x") (Ast.Expr.constF 1)) (Ast.Expr.var "x"))
}

def Δ : Env.CircuitEnv := [("mul", adderCircuit), ("addOne", addOneCircuit),
                           ("identity", identityCircuit), ("assert", assertCircuit)]

theorem adderCircuit_correct : (Ty.circuitCorrect Δ adderCircuit) := by
  unfold Ty.circuitCorrect
  unfold adderCircuit
  simp_all
  intro x hs hi hσ
  set envs := Ty.makeEnvs adderCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Env.lookupTy Γ "x" = (Ast.Ty.field.refin (Ast.Predicate.const (Ast.Expr.constBool true))) := rfl
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.const (Ast.Expr.constBool true))
                                (Ast.Predicate.const (Ast.Expr.constBool true)) hΓ hΓ
  have hv : ∃ v: F, Env.lookupVal σ "x" = Ast.Value.vF v := by {
    unfold Ty.checkInputsTypes at hi
    simp at hi
    cases x with
    | vF xv => {
      simp_all
      unfold σ
      unfold envs
      unfold Ty.makeEnvs
      unfold Env.updateVal
      simp_all
      unfold Env.lookupVal
      simp_all
    }
    | _ => {
      simp_all
    }
  }
  obtain ⟨vv, hv_eq⟩ := hv
  have h_sub := two_mul_field σ Δ Γ "x" vv hv_eq
  exact Ty.TypeJudgment.TE_SUB h_sub h_body

theorem addOneCircuit_correct : (Ty.circuitCorrect Δ addOneCircuit) := by
  unfold Ty.circuitCorrect
  unfold addOneCircuit
  simp_all
  intro x hs himp_compl_comm hσ
  set envs := Ty.makeEnvs addOneCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Env.lookupTy Γ "x" = Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.constF 1)) := rfl
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.eq (Ast.Expr.constF 1))
                                (Ast.Predicate.eq (Ast.Expr.constF 1)) hΓ hΓ
  have h_sub := @rw_var_sub_int_add σ Δ Γ "x" "x" (.constF 1) (.constF 1) hΓ hΓ
  exact Ty.TypeJudgment.TE_SUB h_sub h_body

theorem identityCircuit_correct : (Ty.circuitCorrect Δ identityCircuit) := by
  unfold Ty.circuitCorrect
  unfold identityCircuit
  simp_all
  intro x hs hi hσ
  set envs := Ty.makeEnvs identityCircuit x
  set σ := envs.1
  set Γ := envs.2
  apply let_binding_identity
  unfold Ty.makeEnvs
  simp_all
  unfold Env.updateTy
  unfold Env.lookupTy
  simp_all
  rfl

theorem assertCircuit_correct : (Ty.circuitCorrect Δ assertCircuit) := by
  unfold Ty.circuitCorrect
  unfold assertCircuit
  simp_all
  intro x hs hi hσ
  set envs := Ty.makeEnvs identityCircuit x
  set σ := envs.1
  set Γ := envs.2
  apply let_binding_assert_const
  unfold Ty.makeEnvs
  unfold Env.updateTy
  unfold Env.lookupTy
  simp_all
  rfl
  simp_all
