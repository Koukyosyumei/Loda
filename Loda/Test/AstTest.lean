import Mathlib.Tactic.NormNum.Core

import Loda.Ast
import Loda.Env
import Loda.Eval
import Loda.Typing
import Loda.PropSemantics

-- tests

def σ₀ : Env.ValEnv := []
def Δ₀ : Env.CircuitEnv := []

-- --------------------------------------------------
-- beq tests
-- --------------------------------------------------
example : (Ast.Value.vF 3) == (Ast.Value.vF 3) := rfl
example : (Ast.Value.vF 3) != (Ast.Value.vF 4) := rfl
example : (Ast.Value.vBool true) != (Ast.Value.vBool false) := rfl

-- --------------------------------------------------
-- evalRelOp tests
-- --------------------------------------------------
example : Eval.evalRelOp Ast.RelOp.eq (Ast.Value.vF 2) (Ast.Value.vF 2) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vF 2) (Ast.Value.vF 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.le (Ast.Value.vF 5) (Ast.Value.vF 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vBool true) (Ast.Value.vBool false) = none := rfl

-- --------------------------------------------------
-- eval on basic constants & var/let
-- --------------------------------------------------
example: Eval.EvalProp σ₀ Δ₀ (.constF 42) (.vF 42) := Eval.EvalProp.ConstF
example: Eval.EvalProp σ₀ Δ₀ (.constBool false) (.vBool false) := Eval.EvalProp.ConstBool

def σ₁ := Env.updateVal σ₀ "y" (Ast.Value.vF 99)
example: Eval.EvalProp σ₁ Δ₀ (.var "y") (.vF 99) := by
  apply Eval.EvalProp.Var
  simp [σ₁]
  unfold Env.updateVal Env.lookupVal
  simp_all

example: Eval.EvalProp σ₀ Δ₀
        (.letIn "z" (.constF 7) (.fieldExpr (Ast.Expr.var "z") .mul (.constF 3))) (.vF 21) := by
  apply Eval.EvalProp.Let
  apply Eval.EvalProp.ConstF
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.updateVal Env.lookupVal
  simp_all
  rfl
  apply Eval.EvalProp.ConstF
  unfold Eval.evalFieldOp
  simp_all
  rfl

example: Eval.EvalProp σ₀ Δ₀ (.binRel (.constF 3) .le (.constF 7)) (.vBool true) := by
  apply Eval.EvalProp.Rel
  apply Eval.EvalProp.ConstF
  apply Eval.EvalProp.ConstF
  unfold Eval.evalRelOp
  simp_all
  norm_cast

example: Eval.EvalProp σ₀ Δ₀ (.branch (.constBool true) (.constF 3) (.constF 7)) (.vF 3) := by
  apply Eval.EvalProp.IfTrue
  apply Eval.EvalProp.ConstBool
  apply Eval.EvalProp.ConstF

-- --------------------------------------------------
-- iter: sum from 0 to 4 with accumulator starting at 0
-- --------------------------------------------------
-- let f i = λacc, acc + i
def sumIter : Ast.Expr :=
  Ast.Expr.iter
    (Ast.Expr.constF 0)  -- start
    (Ast.Expr.constF 4)  -- end (exclusive)
    -- f = λi. λacc. acc + i
    (Ast.Expr.lam "i" Ast.Ty.field <|
      Ast.Expr.lam "acc" Ast.Ty.field <|
        Ast.Expr.fieldExpr (Ast.Expr.var "acc") Ast.FieldOp.add (Ast.Expr.var "i"))
    (Ast.Expr.constF 0)  -- initial accumulator

example: Eval.EvalProp σ₀ Δ₀ sumIter (.vF 6) := by
  rw[sumIter]
  apply Eval.EvalProp.Iter
  apply Eval.EvalProp.ConstF
  apply Eval.EvalProp.ConstF
  apply Eval.EvalProp.Lam
  apply Eval.EvalProp.ConstF
  apply Eval.EvalLoop.Step
  simp_all
  norm_cast
  rfl
  apply Eval.EvalProp.Lam
  rfl
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  unfold Eval.evalFieldOp
  simp_all
  rfl
  simp_all
  norm_cast
  apply Eval.EvalLoop.Step
  simp_all
  norm_cast
  rfl
  apply Eval.EvalProp.Lam
  rfl
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  unfold Eval.evalFieldOp
  simp_all
  rfl
  norm_cast
  simp_all
  apply Eval.EvalLoop.Step
  simp_all
  norm_cast
  rfl
  apply Eval.EvalProp.Lam
  rfl
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  unfold Eval.evalFieldOp
  simp_all
  rfl
  norm_cast
  simp_all
  apply Eval.EvalLoop.Step
  simp_all
  norm_cast
  rfl
  apply Eval.EvalProp.Lam
  rfl
  apply Eval.EvalProp.FBinOp
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  apply Eval.EvalProp.Var
  unfold Env.lookupVal Env.updateVal
  simp_all
  rfl
  unfold Eval.evalFieldOp
  simp_all
  rfl
  norm_cast
  simp_all
  apply Eval.EvalLoop.Done
  simp_all
  norm_cast
