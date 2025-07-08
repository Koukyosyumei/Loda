import Mathlib.Tactic.NormNum.Core

import Loda.Ast
import Loda.Env
import Loda.Eval
import Loda.Typing
import Loda.PropSemantics

-- tests

def σ₀ : Env.ValEnv := []
def δ₀ : Env.CircuitEnv := []

-- --------------------------------------------------
-- beq tests
-- --------------------------------------------------
example : (Ast.Value.vInt 3) == (Ast.Value.vInt 3) := rfl
example : (Ast.Value.vInt 3) != (Ast.Value.vInt 4) := rfl
example : (Ast.Value.vStar) == (Ast.Value.vF 5) := rfl
example : (Ast.Value.vF 4) == (Ast.Value.vStar) := rfl
example : (Ast.Value.vBool true) != (Ast.Value.vBool false) := rfl

-- --------------------------------------------------
-- evalRelOp tests
-- --------------------------------------------------
example : Eval.evalRelOp Ast.RelOp.eq (Ast.Value.vInt 2) (Ast.Value.vInt 2) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vInt 2) (Ast.Value.vInt 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.le (Ast.Value.vInt 5) (Ast.Value.vInt 5) = some true := rfl
example : Eval.evalRelOp Ast.RelOp.lt (Ast.Value.vBool true) (Ast.Value.vBool false) = none := rfl

-- --------------------------------------------------
-- eval on basic constants & var/let
-- --------------------------------------------------
example: Eval.EvalProp σ₀ δ₀ (.constInt 42) (.vInt 42) := Eval.EvalProp.ConstInt
example: Eval.EvalProp σ₀ δ₀ (.constBool false) (.vBool false) := Eval.EvalProp.ConstBool

def σ₁ := Env.updateVal σ₀ "y" (Ast.Value.vInt 99)
example: Eval.EvalProp σ₁ δ₀ (.var "y") (.vInt 99) := by
  apply Eval.EvalProp.Var
  simp [σ₁]
  unfold Env.updateVal Env.lookupVal
  simp_all

example: Eval.EvalProp σ₀ δ₀
        (.letIn "z" (.constInt 7) (.intExpr (Ast.Expr.var "z") .mul (.constInt 3))) (.vInt 21) := by
  apply Eval.EvalProp.Let
  apply Eval.EvalProp.ConstInt
  apply Eval.EvalProp.IntOp
  apply Eval.EvalProp.Var
  unfold Env.updateVal Env.lookupVal
  simp_all
  rfl
  apply Eval.EvalProp.ConstInt
  unfold Eval.evalIntegerOp
  simp_all

example: Eval.EvalProp σ₀ δ₀ (.binRel (.constInt 3) .le (.constInt 7)) (.vBool true) := by
  apply Eval.EvalProp.Rel
  apply Eval.EvalProp.ConstInt
  apply Eval.EvalProp.ConstInt
  unfold Eval.evalRelOp
  simp_all

def literalArr := Ast.Expr.arrCons (.constInt 5) (.constInt 0)
example: Eval.EvalProp σ₀ δ₀ (.arrLen literalArr) (.vInt 2) := by
  apply Eval.EvalProp.ArrLen
  rw[literalArr]
  apply Eval.EvalProp.ArrConsElem
  apply Eval.EvalProp.ConstInt
  apply Eval.EvalProp.ConstInt
  simp_all
  rfl

-- --------------------------------------------------
-- iter: sum from 0 to 4 with accumulator starting at 0
-- --------------------------------------------------
-- let f i = λacc, acc + i
def sumIter : Ast.Expr :=
  Ast.Expr.iter
    (Ast.Expr.constInt 0)  -- start
    (Ast.Expr.constInt 4)  -- end (exclusive)
    -- f = λi. λacc. acc + i
    (Ast.Expr.lam "i" Ast.Ty.int <|
      Ast.Expr.lam "acc" Ast.Ty.int <|
        Ast.Expr.intExpr (Ast.Expr.var "acc") Ast.IntegerOp.add (Ast.Expr.var "i"))
    (Ast.Expr.constInt 0)  -- initial accumulator

#eval Eval.eval σ₀ δ₀ sumIter

-- sum 0 + 1 + 2 + 3 = 6
example : Eval.eval σ₀ δ₀ sumIter = some (Ast.Value.vInt 6) := by
  unfold sumIter
  simp [Eval.eval]
  unfold Eval.maximumRecursion
  simp_all
  unfold Eval.eval_with_fuel.loop
  simp_all
  unfold Eval.eval_with_fuel.loop
  simp_all
  unfold Eval.eval_with_fuel.loop
  simp_all
  unfold Eval.eval_with_fuel.loop
  simp_all
  unfold Eval.eval_with_fuel.loop
  unfold Env.updateVal
  unfold Env.lookupVal
  simp_all
