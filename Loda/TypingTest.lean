import Loda.Ast
import Loda.Typing

open Ast

-- dummy environments
def σ0 : Env := fun x =>
  match x with
  | "x" => Value.vBool true
  | "b" => Value.vBool true
  | "y" => Value.vInt 123
  | _ => Value.vStar
def Γ0 : TyEnv := fun x =>
  match x with
  | "x" => (Ty.refin Ty.bool (Ast.Expr.constBool true))
  | "b" => (Ty.refin Ty.bool (Ast.Expr.constBool true))
  | "y" => Ty.int
  | _ => Ty.unit
def Γ1 := setTy Γ0 "x" Ty.bool
def δ0 : Ast.CircuitEnv :=
  fun _ => { name := "idInt", inputs := [("x", Ast.Ty.int)], output := ("out", Ast.Ty.int),
                 body := Ast.Expr.var "x" }

example : SubtypeJudgment σ0 δ0 Γ0 123 (pure Ty.int) (pure Ty.int) :=
  SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | True} <: {v:int | True}
example : SubtypeJudgment σ0 δ0 Γ0 123 (pure (Ty.refin Ty.int (Ast.Expr.constBool true))) (pure (Ty.refin Ty.int (Ast.Expr.constBool true))) := SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | y + y} <: {v:int | 2 * y}
-- (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "y"))
example : SubtypeJudgment σ0 δ0 Γ0 123
  (pure (Ty.refin Ty.int (Ast.Expr.intExpr (Ast.Expr.var "y") Ast.IntegerOp.add (Ast.Expr.var "y"))))
  (pure (Ty.refin Ty.int (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "y"))))
  := by
  apply SubtypeJudgment.TSub_Refine
  apply SubtypeJudgment.TSub_Refl
  unfold expr2prop
  simp_all

-- TE_VAR: assume env maps "b" to {v | v = eval ...}
example : TypeJudgment σ0 δ0 Γ0 123 (Expr.var "b") ((Ty.refin Ty.bool (eeq v (Ast.Expr.var "b"))), σ0) := by
  apply TypeJudgment.TE_Var
  simp [Γ0]
  rfl
