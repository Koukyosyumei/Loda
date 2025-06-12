import Loda.Typing
import Loda.Gadget

@[simp]
def mulCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}
def Δ : Env.CircuitEnv := [("mul", mulCircuit)]

theorem mulCircuit_correct : (Ty.circuitCorrect 1000 Δ mulCircuit) := by
  unfold Ty.circuitCorrect
  unfold mulCircuit
  simp_all
  intro x hs hσ
  set envs := Ty.makeEnvs mulCircuit x
  set σ := envs.1
  set Γ := envs.2
  have hΓ : Γ "x" = (Ast.Ty.int.refin (Ast.Expr.constBool true)) := rfl
  have h_body := @let_binding_int_op_type_preservation 1000 "x" "x" "out" σ Δ Γ
              Ast.IntegerOp.add (Ast.Expr.constBool true) (Ast.Expr.constBool true) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := int_refintype_implies_exists_int_value 1000 σ Δ Γ "x" (Ast.Expr.constBool true) hΓ hσ
  have h_sub := two_mul_I 1000 σ Δ Γ "x" vv hv_eq
  exact Ty.TypeJudgment.TE_SUB h_sub h_body

def σ : Env.ValEnv := [("x", Ast.Value.vInt 5)]
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)
#eval Eval.eval 1000 σ Δ mulCircuit.body
