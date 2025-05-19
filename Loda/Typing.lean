import Loda.Ast
import Loda.Circuit
import Loda.Env
import Loda.Eval
import Loda.PropSemantics

/-- Subtyping judgment for CODA types -/
inductive SubtypeJudgment : Env.ValEnv -> Env.CircuitEnv -> Env.TyEnv -> ℕ → Option Ast.Ty → Option Ast.Ty → Prop where
  /-- TSUB-REFL: Reflexivity -/
  | TSub_Refl {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {τ : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure τ) (pure τ)

  /-- TSUB-TRANS: Transitivity -/
  | TSub_Trans {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {τ₁ τ₂ τ₃ : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₂) →
      SubtypeJudgment σ δ Γ ctr (pure τ₂) (pure τ₃) →
      SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₃)

  /-- TSUB-REFINE: Refinement subtyping -/
  | TSub_Refine {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {T₁ T₂ : Ast.Ty} {φ₁ φ₂ : Ast.Expr} :
      SubtypeJudgment σ δ Γ ctr (pure T₁) (pure T₂) →
      (PropSemantics.expr2prop σ δ ctr φ₁ → PropSemantics.expr2prop σ δ ctr φ₂) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.refin T₁ φ₁)) (pure (Ast.Ty.refin T₂ φ₂))

  /-- TSUB-FUN: Function subtyping -/
  | TSub_Fun {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {x y : String} {z : Ast.Value} {τx τy τr τs : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure τy) (pure τx) →
      -- Using a fresh variable z to avoid capture
      -- SubtypeJudgment (set (set σ x z) y z) Γ τr τs →
      SubtypeJudgment σ δ Γ ctr (pure τr) (pure τs) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.func x τx τr)) (pure (Ast.Ty.func y τy τs))

  /-- TSUB-ARR: Array subtyping -/
  | TSub_Arr {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {T₁ T₂ : Ast.Ty} :
      SubtypeJudgment σ δ Γ ctr (pure T₁) (pure T₂) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.arr T₁)) (pure (Ast.Ty.arr T₂))

  /-- TSUB-PRODUCT: Product subtyping -/
  | TSub_Product {σ : Env.ValEnv} {δ: Env.CircuitEnv} {Γ : Env.TyEnv} {ctr: ℕ} {Ts₁ Ts₂ : List Ast.Ty} :
      Ts₁.length = Ts₂.length →
      --PairwiseProd (SubtypeJudgment σ Γ) (List.zip Ts₁ Ts₂) →
      (∀ i, i < Ts₁.length → SubtypeJudgment σ δ Γ ctr Ts₁[i]? Ts₂[i]?) →
      SubtypeJudgment σ δ Γ ctr (pure (Ast.Ty.prod Ts₁)) (pure (Ast.Ty.prod Ts₂))

def eeq (e₁ e₂: Ast.Expr): Ast.Expr :=
  Ast.Expr.binRel e₁ Ast.RelOp.eq e₂
def v: Ast.Expr := Ast.Expr.var ".v"

axiom IntExprEqImpliesIntVal :
  ∀ (a b : Ast.Expr) (op : Ast.IntegerOp) (σ : Env.ValEnv) (δ : Env.CircuitEnv) (ctr : ℕ),
  PropSemantics.expr2prop σ δ ctr (eeq v (Ast.Expr.intExpr a op b)) →
  ∃ vv, Eval.eval σ δ ctr v = some (Ast.Value.vInt vv)

inductive TypeJudgment: Env.ValEnv -> Env.CircuitEnv -> Env.TyEnv -> ℕ -> Ast.Expr -> (Ast.Ty × Env.ValEnv) -> Prop where
  -- TE-VAR
  | TE_Var {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {x : String} {T: Ast.Ty}:
    ∀ φ: Ast.Expr, Γ x = (Ast.Ty.refin T φ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.var x) ((Ast.Ty.refin T (eeq v (Ast.Expr.var x))), σ)

  -- TE-VAR-FUNC
  | T_VarFunc {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {f x : String} {τ₁ τ₂: Ast.Ty}:
      Γ f = (Ast.Ty.func x τ₁ τ₂) →
      TypeJudgment σ δ Γ ctr (Ast.Expr.var f) ((Ast.Ty.func x τ₁ τ₂), σ)

  -- TE-NONDET
  | T_Nondet {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {p: ℕ}:
    TypeJudgment σ δ Γ ctr Ast.Expr.wildcard ((Ast.Ty.refin (Ast.Ty.field p) (Ast.Expr.constBool true)), σ)

  -- TE-CONSTF
  | T_ConstF {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {p: ℕ} {f: F p} :
    TypeJudgment σ δ Γ ctr (Ast.Expr.constF p f) ((Ast.Ty.refin (Ast.Ty.field p) (eeq v (Ast.Expr.constF p f))), σ)

  -- TE-ASSERT
  | T_Assert {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {e₁ e₂: Ast.Expr} {p: ℕ}:
    TypeJudgment σ δ Γ ctr e₁ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr e₂ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.assertE e₁ e₂) ((Ast.Ty.refin Ast.Ty.unit (eeq e₁ e₂)), σ)

  -- TE-BINOPFIELD
  | T_BinOpField {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {e₁ e₂: Ast.Expr} {op: Ast.FieldOp} {p: ℕ}:
    TypeJudgment σ δ Γ ctr e₁ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr e₂ ((Ast.Ty.field p), σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.fieldExpr e₁ op e₂) ((Ast.Ty.refin (Ast.Ty.field p) (eeq v (Ast.Expr.fieldExpr e₁ op e₂))), σ)

  -- TE-ABS (function abstraction)
  | T_Abs {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {x: String} {τ₁ τ₂: Ast.Ty} {e: Ast.Expr}:
    TypeJudgment σ δ (Env.setTy Γ x τ₁) ctr e (τ₂, σ) →
    TypeJudgment σ δ Γ ctr (Ast.Expr.lam x τ₁ e) ((Ast.Ty.func x τ₁ τ₂), σ)

  -- TE-APP
  | T_App {σ: Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {x₁ x₂: Ast.Expr} {s: String} {τ₁ τ₂: Ast.Ty} {v: Ast.Value}:
    TypeJudgment σ δ Γ ctr x₁ ((Ast.Ty.func s τ₁ τ₂), σ) →
    Eval.eval σ δ ctr x₂ = some v →
    TypeJudgment σ δ Γ ctr x₂ (τ₁, σ) → TypeJudgment σ δ Γ ctr (Ast.Expr.app x₁ x₂) (τ₂, (Env.setVal σ s v))

  -- TE_SUB
  | T_SUB {σ σ': Env.ValEnv} {δ: Env.CircuitEnv} {Γ: Env.TyEnv} {ctr: ℕ} {e: Ast.Expr} {τ₁ τ₂: Ast.Ty}:
    SubtypeJudgment σ δ Γ ctr (pure τ₁) (pure τ₂) →
    TypeJudgment σ δ Γ ctr e (τ₁, σ') →
    TypeJudgment σ δ Γ ctr e (τ₂, σ')

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
  ∀ p ∈ (List.zip c.inputs xs), (PropSemantics.tyenv2prop σ δ 1000 Γ p.fst.fst) →
  match Eval.eval σ δ 1000 c.body with
  | some _ =>
    -- extract the refinement predicate φ from `c.output`
    match c.output with
    | (n, Ast.Ty.refin _ φ) => PropSemantics.expr2prop σ δ 1000 φ
    | _            => True
  | none   => False
