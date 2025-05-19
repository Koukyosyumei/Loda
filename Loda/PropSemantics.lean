import Loda.Ast
import Loda.Circuit
import Loda.Env
import Loda.Eval

namespace PropSemantics

def expr2prop (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ) : Ast.Expr → Prop
| Ast.Expr.binRel e₁ op e₂ =>
  match Eval.eval σ δ ctr e₁, Eval.eval σ δ ctr e₂ with
  | some v₁, some v₂ =>
    match Eval.evalRelOp op v₁ v₂ with
    | some b => b
    | none   => False
  | _, _ => False
| _ => False

def tyenv2prop (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ) (Γ: Env.TyEnv) (x : String): Prop :=
  match Γ x with
  | Ast.Ty.refin _ e => expr2prop σ δ ctr e
  | _ => True

/-- Given a circuit `c`, produce the Prop that says
1. for any choice of inputs of the correct field type,
2. evaluating `c.body` yields a value `v`,
3. and `v` satisfies the refinement predicate in `c.output`. -/
def circuit2prop (p : ℕ) (δ : Env.CircuitEnv) (c : Circuit.Circuit) : Prop :=
  ∀ (xs : List (ZMod p)),
    -- require that the argument list `xs` matches `c.inputs` in length
    xs.length = c.inputs.length →
  let σ : Env.ValEnv :=
    (c.inputs.zip xs).foldl (fun σ (xy : (String × Ast.Ty) × ZMod p) =>
      let ((name, _), x) := xy; Env.setVal σ name (Ast.Value.vF p x)) (fun _ => Ast.Value.vStar)
  let Γ : Env.TyEnv :=
    (c.inputs.zip xs).foldl (fun Γ (xy : (String × Ast.Ty) × ZMod p) =>
      let ((name, τ), _) := xy; Env.setTy Γ name τ) (fun _ => Ast.Ty.unit)
  ∀ p ∈ (List.zip c.inputs xs), (tyenv2prop σ δ 1000 Γ p.fst.fst) →
  match Eval.eval σ δ 1000 c.body with
  | some _ =>
    -- extract the refinement predicate φ from `c.output`
    match c.output with
    | (n, Ast.Ty.refin _ φ) => expr2prop σ δ 1000 φ
    | _            => True
  | none   => False

end PropSemantics
