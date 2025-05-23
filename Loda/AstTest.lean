import Mathlib.Tactic.NormNum.Core

import Loda.Ast
import Loda.Env
import Loda.Eval
import Loda.Typing
import Loda.PropSemantics

-- tests

def σ₀ : Env.ValEnv := fun _ => Ast.Value.vStar
def δ₀ : Env.CircuitEnv :=
  fun _ => { name := "idInt", inputs := ("x", Ast.Ty.int), output := ("x", Ast.Ty.int),
                 body := Ast.Expr.var "x" }

-- --------------------------------------------------
-- beq tests
-- --------------------------------------------------
example : (Ast.Value.vInt 3) == (Ast.Value.vInt 3) := rfl
example : (Ast.Value.vInt 3) != (Ast.Value.vInt 4) := rfl
example : (Ast.Value.vStar) == (Ast.Value.vF 7 5) := rfl
example : (Ast.Value.vF 7 4) == (Ast.Value.vStar) := rfl
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
example : Eval.eval 123 σ₀ δ₀ (Ast.Expr.constInt 42) = some (Ast.Value.vInt 42) := by simp [Eval.eval]
example : Eval.eval 123 σ₀ δ₀ (Ast.Expr.constBool false) = some (Ast.Value.vBool false) := by simp [Eval.eval]

def σ₁ := Env.updateVal σ₀ "y" (Ast.Value.vInt 99)
example : Eval.eval 123 σ₁ δ₀ (Ast.Expr.var "y") = some (Ast.Value.vInt 99) := by
   simp [Eval.eval]
   simp [σ₁]
   unfold Env.updateVal
   simp_all

example :
  Eval.eval 123 σ₀ δ₀ (Ast.Expr.letIn "z" (Ast.Expr.constInt 7) (Ast.Expr.intExpr (Ast.Expr.var "z") Ast.IntegerOp.mul (Ast.Expr.constInt 3)))
  = some (Ast.Value.vInt 21) := by
    simp [Eval.eval]
    unfold Env.updateVal
    simp_all

#eval Eval.eval 123 σ₀ δ₀ (Ast.Expr.letIn "z" (Ast.Expr.constF 5 7) (Ast.Expr.fieldExpr (Ast.Expr.var "z") Ast.FieldOp.mul (Ast.Expr.constF 5 3)))
#eval (HMul.hMul (7 : F 5) (3 : F 5))

example :
  Eval.eval 123 σ₀ δ₀ (Ast.Expr.letIn "z" (Ast.Expr.constF 5 7) (Ast.Expr.fieldExpr (Ast.Expr.var "z") Ast.FieldOp.mul (Ast.Expr.constF 5 3)))
  = some (Ast.Value.vF 5 1) := by
    simp [Eval.eval]
    unfold Env.updateVal
    simp_all
    decide

example :
  Eval.eval 123 σ₀ δ₀ (Ast.Expr.binRel (Ast.Expr.constInt 3) Ast.RelOp.le (Ast.Expr.constInt 7))
  = some (Ast.Value.vBool true) := by
    simp [Eval.eval]

def pair := Ast.Expr.prodCons [Ast.Expr.constInt 2, Ast.Expr.constBool true]
example :
  Eval.eval 123 σ₀ δ₀ pair
  = some (Ast.Value.vProd [Ast.Value.vInt 2, Ast.Value.vBool true]) := by
    unfold pair
    simp [Eval.eval]

def literalArr := Ast.Expr.arrCons (Ast.Expr.constInt 5) (Ast.Expr.constInt 0) -- yields [5,0]
example :
  Eval.eval 123 σ₀ δ₀ (Ast.Expr.arrLen literalArr) = some (Ast.Value.vInt 2) := by
    unfold literalArr
    simp [Eval.eval]

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

#eval Eval.eval 123 σ₀ δ₀ sumIter

-- sum 0 + 1 + 2 + 3 = 6
example : Eval.eval 123 σ₀ δ₀ sumIter = some (Ast.Value.vInt 6) := by
  unfold sumIter
  simp [Eval.eval]
  unfold Eval.eval.loop
  simp_all
  unfold Eval.eval.loop
  simp_all
  unfold Eval.eval.loop
  simp_all
  unfold Eval.eval.loop
  simp_all
  unfold Eval.eval.loop
  unfold Env.updateVal
  simp_all
