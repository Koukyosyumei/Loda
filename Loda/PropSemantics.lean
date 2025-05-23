import Loda.Ast
import Loda.Env
import Loda.Eval

/-!
  # Predicate Semantics for Loda

  This module interprets certain Loda expressions as Lean `Prop`s,
  by evaluating them under a valuation environment `σ`, a circuit
  environment `δ`, and a fuel bound `fuel`.
-/

namespace PropSemantics

/--
  Interpret a boolean or relational expression `e` as a `Prop`.

  Returns `true` exactly when
  1. `e` is a boolean operation `e₁ ∧/∨ e₂` that evaluates to `some b`
     with `b = true`, or
  2. `e` is a relational operation `e₁ =/</≤ e₂` that evaluates to
     `some b` with `b = true`, or
  3. `e` is the literal `true`.

  In all other cases, the result is `False`.
-/
def exprToProp (fuel : ℕ) (σ : Env.ValEnv) (δ : Env.CircuitEnv) : Ast.Expr → Prop
| Ast.Expr.boolExpr e₁ op e₂ =>
  match Eval.eval fuel σ δ e₁, Eval.eval fuel σ δ e₂ with
  | some v₁, some v₂ =>
    match Eval.evalBoolOp op v₁ v₂ with
    | some b => b
    | none   => False
  | _, _ => False
| Ast.Expr.binRel e₁ op e₂ =>
  match Eval.eval fuel σ δ e₁, Eval.eval fuel σ δ e₂ with
  | some v₁, some v₂ =>
    match Eval.evalRelOp op v₁ v₂ with
    | some b => b
    | none   => False
  | _, _ => False
| Ast.Expr.constBool true => True
| _ => False

/--
  For a type environment `Γ` and variable identifier `ident`, if `Γ ident` is a refinement
  type `{ν : T // φ}`, then `tyenvToProp fuel σ δ Γ ident` asserts that the
  predicate `φ` holds (via `exprToProp`) under the current environments.
  Otherwise, it is always `True`.
-/
def tyenvToProp (fuel : ℕ) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (Γ: Env.TyEnv) (ident : String): Prop :=
  match Γ ident with
  | Ast.Ty.refin _ e => exprToProp fuel σ δ e
  | _ => True

end PropSemantics
