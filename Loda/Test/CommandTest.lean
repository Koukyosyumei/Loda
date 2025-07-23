import Loda.Ast
import Loda.Command
import Loda.Env
import Loda.Gadget
import Loda.Test.TypingTest

open Ast
open Env

#loda_register circuit Adder(x : Field) -> {Field | 2*x} {let out = x + x in out}
#loda_check Adder

#loda_prove Adder := by {
  rename_i Δ h_delta x hs hi envs σ Γ hσ
  have hΓ : Env.lookupTy Γ "x" = (Ast.Ty.field.refin (Ast.Predicate.const (Ast.Expr.constBool True))) := rfl
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.const (Ast.Expr.constBool True))
                                (Ast.Predicate.const (Ast.Expr.constBool True)) hΓ hΓ
  rw[← h_delta] at hσ
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
  simp [h_delta, Γ, Ast.v] at h_sub h_body
  exact Ty.TypeJudgment.TE_SUB h_sub h_body
}
#print Adder_correct
