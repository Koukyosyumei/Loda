# Loda

> [!IMPORTANT]
> This tool is under active development. Usage patterns and features may change over time.

<p align="center">
    <img src="./img/logo-wide.png" alt="Loda Logo" height="126">
</p>

## Install

TBD

## Usage

```lean
#loda_register circuit Adder(x : Field) -> {Field | 2*x} {let out = x + x in out}
#loda_check Adder

#loda_prove Adder := by {
  rename_i Δ h_delta x hs envs σ Γ hσ
  have hΓ : Γ "x" = (Ast.Ty.field.refin (Ast.Predicate.const (Ast.Expr.constBool True))) := rfl
  have h_body := @let_binding_field_op_type_preservation "x" "x" "out" σ Δ Γ
              Ast.FieldOp.add (Ast.Predicate.const (Ast.Expr.constBool True))
                                (Ast.Predicate.const (Ast.Expr.constBool True)) hΓ hΓ
  rw[← h_delta] at hσ
  obtain ⟨vv, hv_eq⟩ := field_refintype_implies_exists_field_value σ Δ Γ "x" (Ast.Predicate.const (Ast.Expr.constBool True))  hΓ hσ
  have h_sub := two_mul_field σ Δ Γ "x" vv hv_eq
  simp [h_delta, Γ, Ast.v] at h_sub h_body
  exact Ty.TypeJudgment.TE_SUB h_sub h_body
}
```
