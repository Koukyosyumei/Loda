import Loda.Ast

-- tests

def σ0 : Ast.Env := fun _ => Ast.Value.vStar

-- A helper circuit env with a single identity circuit
def δ0 : Ast.CircuitEnv :=
  fun _ => { name := "idInt", inputs := [("x", Ast.Ty.int)], output := Ast.Ty.int,
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
example : Ast.evalRelOp Ast.RelOp.eq (Ast.Value.vInt 2) (Ast.Value.vInt 2) = some true := rfl
example : Ast.evalRelOp Ast.RelOp.lt (Ast.Value.vInt 2) (Ast.Value.vInt 5) = some true := rfl
example : Ast.evalRelOp Ast.RelOp.le (Ast.Value.vInt 5) (Ast.Value.vInt 5) = some true := rfl
example : Ast.evalRelOp Ast.RelOp.lt (Ast.Value.vBool true) (Ast.Value.vBool false) = none := rfl

#print Ast.eval
#check Ast.eval

#eval Ast.eval σ0 δ0 123 (Ast.Expr.constInt 42)

-- --------------------------------------------------
-- eval on basic constants & var/let
-- --------------------------------------------------
example : Ast.eval σ0 δ0 123 (Ast.Expr.constInt 42) = some (Ast.Value.vInt 42) := by simp [Ast.eval]
example : Ast.eval σ0 δ0 123 (Ast.Expr.constBool false) = some (Ast.Value.vBool false) := by simp [Ast.eval]

def σ₁ := Ast.set σ0 "y" (Ast.Value.vInt 99)
example : Ast.eval σ₁ δ0 123 (Ast.Expr.var "y") = some (Ast.Value.vInt 99) := by
   simp [Ast.eval]
   simp [σ₁]
   unfold Ast.set
   simp_all

example :
  Ast.eval σ0 δ0 123 (Ast.Expr.letIn "z" (Ast.Expr.constInt 7) (Ast.Expr.intExpr (Ast.Expr.var "z") Ast.IntegerOp.mul (Ast.Expr.constInt 3)))
  = some (Ast.Value.vInt 21) := by
    simp [Ast.eval]
    simp [Ast.evalIntegerOp]
    unfold Ast.set
    simp_all

#eval Ast.eval σ0 δ0 123 (Ast.Expr.letIn "z" (Ast.Expr.constF 5 7) (Ast.Expr.fieldExpr (Ast.Expr.var "z") Ast.FieldOp.mul (Ast.Expr.constF 5 3)))

example :
  Ast.eval σ0 δ0 123 (Ast.Expr.binRel (Ast.Expr.constInt 3) Ast.RelOp.le (Ast.Expr.constInt 7))
  = some (Ast.Value.vBool true) := by
    simp [Ast.eval]
    simp [Ast.evalRelOp]

def pair := Ast.Expr.prodCons [Ast.Expr.constInt 2, Ast.Expr.constBool true]
example :
  Ast.eval σ0 δ0 123 pair
  = some (Ast.Value.vProd [Ast.Value.vInt 2, Ast.Value.vBool true]) := by
    unfold pair
    simp [Ast.eval]

def literalArr := Ast.Expr.arrCons (Ast.Expr.constInt 5) (Ast.Expr.constInt 0) -- yields [5,0]
example :
  Ast.eval σ0 δ0 123 (Ast.Expr.arrLen literalArr) = some (Ast.Value.vInt 2) := by
    unfold literalArr
    simp [Ast.eval]

-- --------------------------------------------------
-- iter: sum from 0 to 4 with accumulator starting at 0
-- --------------------------------------------------
-- let f i = λacc, acc + i
def sumIter : Ast.Expr :=
  Ast.Expr.iter "i"
    (Ast.Expr.constInt 0)  -- start
    (Ast.Expr.constInt 4)  -- end (exclusive)
    -- f = λi. λacc. acc + i
    (Ast.Expr.lam "i" Ast.Ty.int <|
      Ast.Expr.lam "acc" Ast.Ty.int <|
        Ast.Expr.intExpr (Ast.Expr.var "acc") Ast.IntegerOp.add (Ast.Expr.var "i"))
    (Ast.Expr.constInt 0)  -- initial accumulator

-- sum 0 + 1 + 2 + 3 = 6
example : Ast.eval σ0 δ0 123 sumIter = some (Ast.Value.vInt 6) := by
  unfold sumIter
  simp [Ast.eval]
  unfold Ast.eval.loop
  simp_all
  unfold Ast.eval.loop
  simp_all
  unfold Ast.eval.loop
  simp_all
  unfold Ast.eval.loop
  simp_all
  unfold Ast.eval.loop
  simp_all
  unfold Ast.set
  simp_all
  simp [Ast.evalIntegerOp]
