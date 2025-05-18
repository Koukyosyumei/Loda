import Loda.Ast
import Loda.Typing

open Ast

-- dummy environments
def σ0 : Env := fun _ => Value.vBool true
def Γ0 : TyEnv := fun _ => (Ty.refin Ty.bool (Ast.Expr.constBool true))
def Γ1 := setTy Γ0 "x" Ty.bool
def δ0 : Ast.CircuitEnv :=
  fun _ => { name := "idInt", inputs := [("x", Ast.Ty.int)], output := Ast.Ty.int,
                 body := Ast.Expr.var "x" }

example : SubtypeJudgment σ0 δ0 Γ0 123 (pure Ty.int) (pure Ty.int) :=
  SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | True} <: {v:int | True}
example : SubtypeJudgment σ0 δ0 Γ0 123 (pure (Ty.refin Ty.int (Ast.Expr.constBool true))) (pure (Ty.refin Ty.int (Ast.Expr.constBool true))) := by
  apply SubtypeJudgment.TSub_Refl

-- TE_VAR: assume env maps "b" to {v | v = eval ...}
example : TypeJudgment σ0 δ0 Γ0 123 (Expr.var "b") ((Ty.refin Ty.bool (eeq v (Ast.Expr.var "b"))), σ0) := by
  apply TypeJudgment.TE_Var
  simp [Γ0]
  rfl
