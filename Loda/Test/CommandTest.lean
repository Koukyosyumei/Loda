import Loda.Ast
import Loda.Command
import Loda.Env
import Loda.Test.TypingTest

open Ast
open Env

#loda_register circuit Adder(x : Int) -> {Int | 2*x} {let out = x + x in out}
#loda_check Adder
#loda_eval Adder x=2

#loda_prove Adder := by {
  rename_i Δ h_delta
  unfold Ty.circuitCorrect
  simp_all
  intro x hs hσ
  set σ := (Env.updateVal [] "x" x)
  set Γ := (Env.updateTy (fun x ↦ Ty.unit) "x" (Ty.int.refin (Expr.constBool True)))
  have h_body :
    Ty.TypeJudgment
      Γ
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
  have hσ₁ : Env.lookupVal σ "x" = x := by {
    simp [σ]
    rfl
  }
  have h : ∃ (a : ℤ), Env.lookupVal σ "x" = Ast.Value.vInt a := by
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
      (some (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))))
      (some (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x"))))) := by {
        apply two_mul_I 1000 σ Δ Γ "x" vv
        simp [σ]
        simp_all
        rfl
      }
  unfold Ast.exprEq at h_sub
  simp [h_delta, Γ, Ast.v] at h_sub
  simp [h_delta, Ast.v] at h_body
  exact Ty.TypeJudgment.TE_SUB h_sub h_body
}

#print Adder_correct
