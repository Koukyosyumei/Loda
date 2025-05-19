import Loda.Typing

open Ast

-- dummy environments
def σ0 : Env.ValEnv := fun x =>
  match x with
  | "x" => Value.vBool true
  | "b" => Value.vBool true
  | "y" => Value.vInt 123
  | _ => Value.vStar
def Γ0 : Env.TyEnv := fun x =>
  match x with
  | "x" => (Ty.refin Ty.bool (Ast.Expr.constBool true))
  | "b" => (Ty.refin Ty.bool (Ast.Expr.constBool true))
  | "y" => Ty.int
  | _ => Ty.unit
def Γ1 := Env.setTy Γ0 "x" Ty.bool
def δ0 : Env.CircuitEnv :=
  fun _ => { name := "idInt", inputs := [("x", Ast.Ty.int)], output := ("out", Ast.Ty.int),
                 body := Ast.Expr.var "x" }

example : Ty.SubtypeJudgment σ0 δ0 Γ0 123 (pure Ty.int) (pure Ty.int) :=
  Ty.SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | True} <: {v:int | True}
example : Ty.SubtypeJudgment σ0 δ0 Γ0 123
  (pure (Ty.refin Ty.int (Ast.Expr.constBool true)))
  (pure (Ty.refin Ty.int (Ast.Expr.constBool true))) :=
  Ty.SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | y + y} <: {v:int | 2 * y}
-- (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "y"))
example (y: ℕ) (hσy : σ0 "y" = Value.vInt y) : Ty.SubtypeJudgment σ0 δ0 Γ0 123
  (pure (Ty.refin Ty.int (expr_eq v (Ast.Expr.intExpr (Ast.Expr.var "y") Ast.IntegerOp.add (Ast.Expr.var "y")))))
  (pure (Ty.refin Ty.int (expr_eq v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "y")))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  have hv : ∃ vv, Eval.eval σ0 δ0 123 v = some (Value.vInt vv) := by {
    apply Ty.IntExprEqImpliesIntVal at h
    exact h
  }
  obtain ⟨vv, hv_eq⟩ := hv
  dsimp [PropSemantics.expr2prop, Eval.eval] at h ⊢
  unfold expr_eq
  unfold expr_eq at h
  simp [decide_eq_true] at h ⊢
  rw[hσy]
  rw[hσy] at h
  simp[Eval.evalIntegerOp]
  rw[hv_eq]
  rw[hv_eq] at h
  simp_all
  rw[two_mul]

-- TE_VAR: assume env maps "b" to {v | v = eval ...}
example : Ty.TypeJudgment σ0 δ0 Γ0 123 (Expr.var "b") ((Ty.refin Ty.bool (expr_eq v (Ast.Expr.var "b"))), σ0) := by
  apply Ty.TypeJudgment.TE_Var
  simp [Γ0]
  rfl
