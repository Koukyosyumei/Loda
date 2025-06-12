import Loda.Ast
import Loda.Command
import Loda.Env
import Loda.Gadget
import Loda.Test.TypingTest

open Ast
open Env

#loda_register circuit Adder(x : Int) -> {Int | 2*x} {let out = x + x in out}
#loda_check Adder
#loda_eval Adder x=2

#loda_prove Adder := by {
  rename_i Δ h_delta x hs envs σ Γ hσ
  have hΓ : Γ "x" = (Ty.int.refin (Expr.constBool True)) := rfl
  have h_body := @let_binding_int_op_type_preservation 1000 "x" "x" "out" σ Δ Γ
              Ast.IntegerOp.add (Ast.Expr.constBool True) (Ast.Expr.constBool True) hΓ hΓ
  obtain ⟨vv, hv_eq⟩ := int_refintype_implies_exists_int_value 1000 σ Δ Γ "x" (Expr.constBool True) hΓ hσ
  have h_sub := two_mul_I 1000 σ Δ Γ "x" vv hv_eq
  simp [h_delta, Γ, Ast.v] at h_sub h_body
  exact Ty.TypeJudgment.TE_SUB h_sub h_body
}

#print Adder_correct
