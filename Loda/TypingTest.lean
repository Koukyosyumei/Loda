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
  | "x" => (Ty.refin Ty.bool (Expr.constBool true))
  | "b" => (Ty.refin Ty.bool (Expr.constBool true))
  | "y" => Ty.int
  | _ => Ty.unit
def Γ1 := Env.setTy Γ0 "x" Ty.bool
def δ0 : Env.CircuitEnv :=
  fun _ => { name := "idInt", inputs := [("x", Ty.int)], output := ("out", Ty.int),
                 body := Expr.var "x" }

example : Ty.SubtypeJudgment σ0 δ0 Γ0 123 (pure Ty.int) (pure Ty.int) :=
  Ty.SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | True} <: {v:int | True}
example : Ty.SubtypeJudgment σ0 δ0 Γ0 123
  (pure (Ty.refin Ty.int (Expr.constBool true)))
  (pure (Ty.refin Ty.int (Expr.constBool true))) :=
  Ty.SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | y + y} <: {v:int | 2 * y}
-- (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var "y"))
example (y: ℕ) (hσy : σ0 "y" = Value.vInt y) : Ty.SubtypeJudgment σ0 δ0 Γ0 123
  (pure (Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.var "y") IntegerOp.add (Expr.var "y")))))
  (pure (Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var "y")))))
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
example : Ty.TypeJudgment σ0 δ0 Γ0 123 (Expr.var "b") ((Ty.refin Ty.bool (expr_eq v (Expr.var "b"))), σ0) := by
  apply Ty.TypeJudgment.TE_Var
  simp [Γ0]
  rfl

@[simp]
def mulCircuit : Circuit.Circuit := {
  name   := "mul",
  inputs := [("x", Ast.Ty.int)],
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}

def δ₁ : Env.CircuitEnv := fun nm => if nm = "mul" then mulCircuit else mulCircuit
def σ₁ : Env.ValEnv := fun x =>
  if x = "x" then Ast.Value.vInt 5 else Ast.Value.vStar
def Γ₁ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)

#eval Eval.eval σ₁ δ₁ 123 mulCircuit.body

example {p : ℕ} : Ty.TypeJudgment σ₁ δ₁ Γ₁ 123 (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x"))
((Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.var "x") IntegerOp.add (Expr.var "x")))), σ₁) := by
  apply Ty.TypeJudgment.T_BinOpInt
  exact p
  apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                    Ty.SubtypeJudgment.TSub_Refl             -- underlying int <: int
                    (by intro _; trivial)                     -- φ₁ → true
                  )
  apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
  simp [Γ₁]
  apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                    Ty.SubtypeJudgment.TSub_Refl             -- underlying int <: int
                    (by intro _; trivial)                     -- φ₁ → true
                  )
  apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
  simp [Γ₁]

example {p : ℕ} :
  Ty.TypeJudgment σ₁ δ₁ Γ₁ 123
    (Ast.Expr.letIn "out"
       (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x"))
       (Ast.Expr.var "out"))
    ((Ty.refin Ty.int (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))), σ₁)
:= by
  apply Ty.TypeJudgment.T_LetIn
  · apply Ty.TypeJudgment.T_BinOpInt
    -- 最初の x
    exact p
    · apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                        Ty.SubtypeJudgment.TSub_Refl
                        (by intro _; trivial))
      apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
      simp [Γ₁]
    -- 二番目の x
    · apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                        Ty.SubtypeJudgment.TSub_Refl
                        (by intro _; trivial))
      apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
      simp [Γ₁]

  -- ③ e₁ の評価結果を計算
  · simp [Eval.eval, Eval.evalIntegerOp, σ₁]; rfl
  -- ④ ボディ out の型付け（環境に out ↦ {v:int | v = x+x} が入っている）
  set σ₂ := Env.setVal σ₁ "out" (Value.vInt 10)
  set Γ₂ := (Env.setTy Γ₁ "out" (Ty.int.refin (expr_eq v ((Expr.var "x").intExpr IntegerOp.add (Expr.var "x")))))
  have hΓout : Γ₂ "out" = Ty.int.refin (expr_eq v (Expr.intExpr (Expr.var "x") IntegerOp.add (Expr.var "x"))) := by {
    simp [Γ₂]
    rfl
  }
  have hφout : PropSemantics.expr2prop σ₁ δ₁ 123
      (expr_eq v (Expr.intExpr (Expr.var "x") IntegerOp.add (Expr.var "x"))) :=
    by {
      simp [PropSemantics.expr2prop, Eval.evalIntegerOp, σ₂]
      sorry
    }
  rw[← hΓout]
  apply Ty.TE_Var_env hφout hΓout


#check Ty.circuit2prop 7 δ₁ mulCircuit

theorem mulCircuit_correct : (Ty.circuit2prop 7 δ₁ mulCircuit) := by
  unfold Ty.circuit2prop
  intros xs henv h₁ h₂ h₃ h₄ h₅
  cases xs
  case nil =>
    simp_all
  case cons hmod hlist =>
    simp [mulCircuit]
    -- Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.var "y") IntegerOp.add (Expr.var "y")))
    have hsub : Ty.TypeJudgment henv δ₁ h₁ 1000 (Expr.var "out") (Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.var "y") IntegerOp.add (Expr.var "y"))), henv) := by {
      dsimp [henv]
      sorry
    }
    sorry
