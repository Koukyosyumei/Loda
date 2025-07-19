import Loda.Typing
import Loda.Gadget

@[simp]
def mulCircuit : Ast.Circuit := {
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

def Δ : Env.CircuitEnv := [("mul", mulCircuit), ("addOne", addOneCircuit)]

theorem mulCircuit_correct : (Ty.circuitCorrect Δ mulCircuit) := by
  unfold Ty.circuitCorrect
  unfold mulCircuit
  simp_all
  intro x hs hσ
  set envs := Ty.makeEnvs mulCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Γ "x" = (Ast.Ty.field.refin (Ast.Predicate.const (Ast.Expr.constBool true))) := rfl
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.const (Ast.Expr.constBool true))
                                (Ast.Predicate.const (Ast.Expr.constBool true)) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := field_refintype_implies_exists_field_value σ Δ Γ "x" (Ast.Predicate.const (Ast.Expr.constBool true)) hΓ hσ
  have h_sub := two_mul_field σ Δ Γ "x" vv hv_eq
  exact Ty.TypeJudgment.TE_SUB h_sub h_body

def σ : Env.ValEnv := [("x", Ast.Value.vF 5)]
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.field (Ast.Predicate.eq (Ast.Expr.constBool true))

theorem addOneCircuit_correct : (Ty.circuitCorrect Δ addOneCircuit) := by
  unfold Ty.circuitCorrect
  unfold addOneCircuit
  simp_all
  intro x hs hσ
  set envs := Ty.makeEnvs addOneCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Γ "x" = Ast.Ty.refin (Ast.Ty.field) (Ast.Predicate.eq (Ast.Expr.constF 1)) := rfl
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.eq (Ast.Expr.constF 1))
                                (Ast.Predicate.eq (Ast.Expr.constF 1)) hΓ hΓ
  have h_sub := @rw_var_sub_int_add σ Δ Γ "x" "x" (.constF 1) (.constF 1) hΓ hΓ hσ hσ
  exact Ty.TypeJudgment.TE_SUB h_sub h_body
