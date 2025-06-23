import Loda.Typing
import Loda.Gadget

@[simp]
def mulCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (Ast.Predicate.const (Ast.Expr.constBool true))),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.Predicate.eq (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}

@[simp]
def addOneCircuit : Ast.Circuit := {
  name   := "assert1",
  inputs := ("x", Ast.Ty.refin (Ast.Ty.field 5) (Ast.Predicate.eq (Ast.Expr.constF 5 1))),
  output := ("out", Ast.Ty.refin (Ast.Ty.field 5) (Ast.Predicate.eq (Ast.Expr.fieldExpr (Ast.Expr.constF 5 1) Ast.FieldOp.add (Ast.Expr.constF 5 1)))),
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
  have hΓ : Γ "x" = (Ast.Ty.int.refin (Ast.Predicate.const (Ast.Expr.constBool true))) := rfl
  have h_body := @let_binding_int_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.IntegerOp.add (Ast.Predicate.const (Ast.Expr.constBool true))
                                (Ast.Predicate.const (Ast.Expr.constBool true)) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := int_refintype_implies_exists_int_value σ Δ Γ "x" (Ast.Predicate.const (Ast.Expr.constBool true)) hΓ hσ
  have h_sub := two_mul_int σ Δ Γ "x" vv hv_eq
  exact Ty.TypeJudgment.TE_SUB h_sub h_body

def σ : Env.ValEnv := [("x", Ast.Value.vInt 5)]
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Predicate.eq (Ast.Expr.constBool true))
#eval Eval.eval σ Δ mulCircuit.body

theorem addOneCircuit_correct : (Ty.circuitCorrect Δ addOneCircuit) := by
  unfold Ty.circuitCorrect
  unfold addOneCircuit
  simp_all
  intro x hs hσ
  set envs := Ty.makeEnvs addOneCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Γ "x" = Ast.Ty.refin (Ast.Ty.field 5) (Ast.Predicate.eq (Ast.Expr.constF 5 1)) := rfl
  have h_body := @let_binding_field_op_type_preservation 5 "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.eq (Ast.Expr.constF 5 1))
                                (Ast.Predicate.eq (Ast.Expr.constF 5 1)) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := field_refintype_implies_exists_field_value 5 σ Δ Γ "x" (Ast.Predicate.eq (Ast.Expr.constF 5 1)) hΓ hσ

  sorry
