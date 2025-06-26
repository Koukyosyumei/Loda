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
  have hΓ : Γ "x" = (Ty.int.refin (Ast.Predicate.const (Expr.constBool True))) := rfl
  have h_body := @let_binding_int_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.IntegerOp.add (Ast.Predicate.const (Ast.Expr.constBool True))
                                (Ast.Predicate.const (Ast.Expr.constBool True)) hΓ hΓ
  rw[← h_delta] at hσ
  obtain ⟨vv, hv_eq⟩ := int_refintype_implies_exists_int_value σ Δ Γ "x" (Ast.Predicate.const (Ast.Expr.constBool True))  hΓ hσ
  have h_sub := two_mul_int σ Δ Γ "x" vv hv_eq
  simp [h_delta, Γ, Ast.v] at h_sub h_body
  exact Ty.TypeJudgment.TE_SUB h_sub h_body
}
#print Adder_correct

#loda_register circuit ArrayLen(x : [Int]) -> {Int | True} {let out = length 0::x in out}
#loda_check ArrayLen
#loda_eval ArrayLen x=12::3::2

#loda_register circuit ArrayIdx(x : [Int]) -> {Int | True} {let out = x[1] in out}
#loda_check ArrayIdx
#loda_eval ArrayIdx x=12::3::2
