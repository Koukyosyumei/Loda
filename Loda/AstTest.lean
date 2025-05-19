import Mathlib.Tactic.NormNum.Core

import Loda.Ast
import Loda.Circuit
import Loda.Env
import Loda.Eval
import Loda.Typing
import Loda.PropSemantics

-- tests

def σ0 : Env.ValEnv := fun _ => Ast.Value.vStar

-- A helper circuit env with a single identity circuit
def δ0 : Env.CircuitEnv :=
  fun _ => { name := "idInt", inputs := [("x", Ast.Ty.int)], output := ("x", Ast.Ty.int),
                 body := Ast.Expr.var "x" }
-- --------------------------------------------------
-- beq tests
-- --------------------------------------------------
example : Ast.beq (Ast.Value.vInt 3) (Ast.Value.vInt 3) = true := rfl
example : Ast.beq (Ast.Value.vInt 3) (Ast.Value.vInt 4) = false := rfl
example : Ast.beq (Ast.Value.vStar) (Ast.Value.vF 7 5) = true := rfl
example : Ast.beq (Ast.Value.vF 7 4) (Ast.Value.vStar) = true := rfl
example : Ast.beq (Ast.Value.vBool true) (Ast.Value.vBool false) = false := rfl

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
example : Eval.eval σ0 δ0 123 (Ast.Expr.constInt 42) = some (Ast.Value.vInt 42) := by simp [Eval.eval]
example : Eval.eval σ0 δ0 123 (Ast.Expr.constBool false) = some (Ast.Value.vBool false) := by simp [Eval.eval]

def σ₁ := Env.setVal σ0 "y" (Ast.Value.vInt 99)
example : Eval.eval σ₁ δ0 123 (Ast.Expr.var "y") = some (Ast.Value.vInt 99) := by
   simp [Eval.eval]
   simp [σ₁]
   unfold Env.setVal
   simp_all

example :
  Eval.eval σ0 δ0 123 (Ast.Expr.letIn "z" (Ast.Expr.constInt 7) (Ast.Expr.intExpr (Ast.Expr.var "z") Ast.IntegerOp.mul (Ast.Expr.constInt 3)))
  = some (Ast.Value.vInt 21) := by
    simp [Eval.eval]
    unfold Env.setVal
    simp_all

#eval Eval.eval σ0 δ0 123 (Ast.Expr.letIn "z" (Ast.Expr.constF 5 7) (Ast.Expr.fieldExpr (Ast.Expr.var "z") Ast.FieldOp.mul (Ast.Expr.constF 5 3)))
#eval (HMul.hMul (7 : F 5) (3 : F 5))

example :
  Eval.eval σ0 δ0 123 (Ast.Expr.letIn "z" (Ast.Expr.constF 5 7) (Ast.Expr.fieldExpr (Ast.Expr.var "z") Ast.FieldOp.mul (Ast.Expr.constF 5 3)))
  = some (Ast.Value.vF 5 1) := by
    simp [Eval.eval]
    unfold Env.setVal
    simp_all
    decide

example :
  Eval.eval σ0 δ0 123 (Ast.Expr.binRel (Ast.Expr.constInt 3) Ast.RelOp.le (Ast.Expr.constInt 7))
  = some (Ast.Value.vBool true) := by
    simp [Eval.eval]

def pair := Ast.Expr.prodCons [Ast.Expr.constInt 2, Ast.Expr.constBool true]
example :
  Eval.eval σ0 δ0 123 pair
  = some (Ast.Value.vProd [Ast.Value.vInt 2, Ast.Value.vBool true]) := by
    unfold pair
    simp [Eval.eval]

def literalArr := Ast.Expr.arrCons (Ast.Expr.constInt 5) (Ast.Expr.constInt 0) -- yields [5,0]
example :
  Eval.eval σ0 δ0 123 (Ast.Expr.arrLen literalArr) = some (Ast.Value.vInt 2) := by
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

#eval Eval.eval σ0 δ0 123 sumIter

-- sum 0 + 1 + 2 + 3 = 6
example : Eval.eval σ0 δ0 123 sumIter = some (Ast.Value.vInt 6) := by
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
  unfold Env.setVal
  simp_all

def mulCircuit : Circuit.Circuit := {
  name   := "mul",
  inputs := [("x₁", Ast.Ty.field 7), ("x₂", Ast.Ty.field 7)],
  output := ("out", Ast.Ty.refin (Ast.Ty.field 7) (eeq v (Ast.Expr.fieldExpr (Ast.Expr.var "x₁") Ast.FieldOp.mul (Ast.Expr.var "x₂")))),
  body   := (Ast.Expr.fieldExpr (Ast.Expr.var "x₁") Ast.FieldOp.mul (Ast.Expr.var "x₂"))
}

def testEnv : Env.CircuitEnv := fun nm => if nm = "mul" then mulCircuit else mulCircuit
def env35 : Env.ValEnv := fun x =>
  if x = "x₁" then Ast.Value.vF 7 3 else if x = "x₂" then Ast.Value.vF 7 5 else Ast.Value.vStar
def Γ0 : Env.TyEnv := fun _ => Ast.Ty.field 7

#check circuit2prop 7 testEnv mulCircuit

theorem mulCircuit_correct : (circuit2prop 7 testEnv mulCircuit) := by
  unfold circuit2prop
  intros xs hlen
  cases xs
  case nil =>
    cases hlen
  case cons hmod hlist =>
    unfold PropSemantics.expr2prop
    unfold mulCircuit
    simp [Eval.eval]
    sorry
