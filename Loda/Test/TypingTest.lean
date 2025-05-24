import Loda.Typing

open Ast

-- refinement subtyping: {v:int | y + y} <: {v:int | 2 * y}
-- (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var "y"))
lemma two_mul_I
  (fuel: ℕ) (σ: Env.ValEnv) (δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : σ x = Value.vInt xv)
  : @Ty.SubtypeJudgment fuel σ δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  have hv : ∃ vv, Eval.eval fuel σ δ v = some (Value.vInt vv) := by {
    apply Ty.exprIntVSound at h
    exact h
  }
  obtain ⟨vv, hv_eq⟩ := hv
  dsimp [PropSemantics.exprToProp, Eval.eval] at h ⊢
  unfold exprEq
  unfold exprEq at h
  simp [decide_eq_true] at h ⊢
  rw[hσx]
  rw[hσx] at h
  simp[Eval.evalIntegerOp]
  rw[hv_eq]
  rw[hv_eq] at h
  simp_all
  rw[two_mul]
  simp_all

lemma two_mul_F {p: ℕ}
  (fuel: ℕ) (σ: Env.ValEnv) (δ: Env.CircuitEnv)
  (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : σ x = Value.vF p xv)
  : @Ty.SubtypeJudgment fuel σ δ Γ
      (pure (Ty.refin Ty.int (exprEq v (Expr.fieldExpr (Expr.var x) FieldOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (exprEq v (Expr.fieldExpr (Expr.constF p 2) FieldOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  have hv : ∃ vv, Eval.eval fuel σ δ v = some (Value.vF p vv) := by {
    apply Ty.exprFielVdSound at h
    exact h
  }
  obtain ⟨vv, hv_eq⟩ := hv
  dsimp [PropSemantics.exprToProp, Eval.eval] at h ⊢
  unfold exprEq
  unfold exprEq at h
  simp [decide_eq_true] at h ⊢
  rw[hσx]
  rw[hσx] at h
  simp[Eval.evalIntegerOp]
  rw[hv_eq]
  rw[hv_eq] at h
  simp_all
  rw[two_mul]
  simp_all


lemma x_plus_x {p : ℕ} (fuel: ℕ) (x: String) (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ: Env.TyEnv) (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true))
  : @Ty.TypeJudgment fuel σ δ Γ (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
      (Ty.refin Ty.int (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))) := by
  apply Ty.TypeJudgment.TE_BinOpInt
  apply Ty.TypeJudgment.TE_SUB (Ty.SubtypeJudgment.TSub_Refine
                    Ty.SubtypeJudgment.TSub_Refl             -- underlying int <: int
                    (by intro _; trivial)                     -- φ₁ → true
                  )
  apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
  simp [hΓx]
  apply Ty.TypeJudgment.TE_SUB (Ty.SubtypeJudgment.TSub_Refine
                    Ty.SubtypeJudgment.TSub_Refl             -- underlying int <: int
                    (by intro _; trivial)                     -- φ₁ → true
                  )
  apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
  simp [hΓx]

lemma let_x_plus_x_y {p : ℕ} (fuel: ℕ) (x y: String) (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (hΓx: Γ x =  Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)) :
  @Ty.TypeJudgment fuel σ δ Γ
    (Ast.Expr.letIn y
       (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
       (Ast.Expr.var y))
    (Ty.refin Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))))
:= by
  apply Ty.TypeJudgment.TE_LetIn
  · apply Ty.TypeJudgment.TE_BinOpInt
    · apply Ty.TypeJudgment.TE_SUB (Ty.SubtypeJudgment.TSub_Refine
                        Ty.SubtypeJudgment.TSub_Refl
                        (by intro _; trivial))
      apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
      simp [hΓx]
    · apply Ty.TypeJudgment.TE_SUB (Ty.SubtypeJudgment.TSub_Refine
                        Ty.SubtypeJudgment.TSub_Refl
                        (by intro _; trivial))
      apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
      simp [hΓx]
  let sum_ty : Ast.Ty := Ast.Ty.refin Ast.Ty.int
      (Ast.exprEq Ast.v
         (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))
  set Γ' := (Env.updateTy Γ y (Ty.int.refin (exprEq v ((Expr.var x).intExpr IntegerOp.add (Expr.var x)))))
  have h_sum_ty_judgment :
    @Ty.TypeJudgment fuel σ δ Γ
      (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
      (Ast.Ty.refin Ast.Ty.int
      (Ast.exprEq Ast.v
         (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))):= by {
        apply x_plus_x
        exact p
        apply hΓx
      }
  have hφ :
      (@Ty.TypeJudgment fuel σ δ Γ (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
        (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))))
      → PropSemantics.exprToProp fuel σ δ
          (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))) :=
      Ty.typeJudgmentRefinementSound Γ Ast.Ty.int (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)) (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))
  apply hφ at h_sum_ty_judgment
  have hΓout : Γ' y = Ty.int.refin (exprEq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x))) := by {
    simp [Γ']
    unfold Env.updateTy
    simp_all
  }
  rw[← hΓout]
  apply Ty.varRefineSound h_sum_ty_judgment hΓout

@[simp]
def mulCircuit : Ast.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}
def Δ : Env.CircuitEnv := fun nm => if nm = "mul" then mulCircuit else mulCircuit

theorem mulCircuit_correct : (Ty.circuitCorrect 7 1000 Δ mulCircuit) := by
  -- circuit2prop の定義展開と前提の整理
  unfold Ty.circuitCorrect
  unfold mulCircuit
  simp_all
  -- 任意の入力 x と型付け前提 hΓ を仮定
  intro x hσ
  set σ := (Env.updateVal (fun x ↦ Value.vStar) "x" (Value.vInt x))
  set Γ := (Env.updateTy (fun x ↦ Ty.unit) "x" (Ty.int.refin (Expr.constBool true)))
  -- let-in レマを呼び出して本体の型付けを得る
  have h_body :
    Ty.TypeJudgment
      (Env.updateTy (fun _ => Ast.Ty.unit) "x" (Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)))
      (Ast.Expr.letIn "out"
         (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x"))
         (Ast.Expr.var "out"))
      (Ast.Ty.refin Ast.Ty.int
         (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))) := by {
          apply @let_x_plus_x_y 7 1000 "x" "out" σ Δ Γ
          simp [Γ]
          rfl
         }
  have h_sub :
    @Ty.SubtypeJudgment 1000 σ Δ Γ
      (pure (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))))
      (pure (Ast.Ty.refin Ast.Ty.int (Ast.exprEq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x"))))) := by {
        apply two_mul_I 1000 σ Δ Γ "x" x
        simp [σ]
        rfl
      }
  exact Ty.TypeJudgment.TE_SUB h_sub h_body


def σ : Env.ValEnv := fun x =>
  if x = "x" then Ast.Value.vInt 5 else Ast.Value.vStar
def Γ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)
#eval Eval.eval 1000 σ Δ mulCircuit.body
