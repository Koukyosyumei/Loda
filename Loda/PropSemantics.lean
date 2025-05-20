import Loda.Ast
import Loda.Circuit
import Loda.Env
import Loda.Eval

namespace PropSemantics

def expr2prop (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ) : Ast.Expr → Prop
/-
| Ast.Expr.boolExpr e₁ op e₂ =>
  match expr2prop σ δ ctr e₁, op, expr2prop σ δ ctr e₂ with
  | p₁, Ast.BooleanOp.and, p₂ => p₁ ∧ p₂
  | p₁, Ast.BooleanOp.or, p₂ => p₁ ∨ p₂
-/
| Ast.Expr.binRel e₁ op e₂ =>
  match Eval.eval σ δ ctr e₁, Eval.eval σ δ ctr e₂ with
  | some v₁, some v₂ =>
    match Eval.evalRelOp op v₁ v₂ with
    | some b => b
    | none   => False
  | _, _ => False
| Ast.Expr.constBool true => True
| _ => False

def tyenv2prop (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ) (Γ: Env.TyEnv) (x : String): Prop :=
  match Γ x with
  | Ast.Ty.refin _ e => expr2prop σ δ ctr e
  | _ => True

end PropSemantics
