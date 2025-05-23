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
  fun _ => { name := "idInt", inputs := ("x", Ty.int), output := ("out", Ty.int),
                 body := Expr.var "x" }

example : @Ty.SubtypeJudgment σ0 δ0 Γ0 123 (pure Ty.int) (pure Ty.int) :=
  Ty.SubtypeJudgment.TSub_Refl

-- TE_VAR: assume env maps "b" to {v | v = eval ...}
example : @Ty.TypeJudgment σ0 δ0 123 Γ0 (Expr.var "b") (Ty.refin Ty.bool (expr_eq v (Expr.var "b"))) := by
  apply Ty.TypeJudgment.TE_Var
  simp [Γ0]
  rfl

-- refinement subtyping: {v:int | True} <: {v:int | True}
example : @Ty.SubtypeJudgment σ0 δ0 Γ0 123
  (pure (Ty.refin Ty.int (Expr.constBool true)))
  (pure (Ty.refin Ty.int (Expr.constBool true))) :=
  Ty.SubtypeJudgment.TSub_Refl

-- refinement subtyping: {v:int | y + y} <: {v:int | 2 * y}
-- (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var "y"))
lemma x_plus_x_eq_2_times_x
  (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ: Env.TyEnv) (x: String) (xv: ℕ) (hσx : σ x = Value.vInt xv)
  : @Ty.SubtypeJudgment σ δ Γ 1000
      (pure (Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))))
      (pure (Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.constInt 2) IntegerOp.mul (Expr.var x)))))
  := by
  apply Ty.SubtypeJudgment.TSub_Refine
  · apply Ty.SubtypeJudgment.TSub_Refl
  intro h
  have hv : ∃ vv, Eval.eval σ δ 1000 v = some (Value.vInt vv) := by {
    apply Ty.IntExprEqImpliesIntVal at h
    exact h
  }
  obtain ⟨vv, hv_eq⟩ := hv
  dsimp [PropSemantics.expr2prop, Eval.eval] at h ⊢
  unfold expr_eq
  unfold expr_eq at h
  simp [decide_eq_true] at h ⊢
  rw[hσx]
  rw[hσx] at h
  simp[Eval.evalIntegerOp]
  rw[hv_eq]
  rw[hv_eq] at h
  simp_all
  rw[two_mul]

lemma x_plus_x {p : ℕ} (x: String) (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ: Env.TyEnv) (hΓx: Γ x = Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true))
  : @Ty.TypeJudgment σ δ 1000 Γ (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
      (Ty.refin Ty.int (expr_eq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x)))) := by
  apply Ty.TypeJudgment.T_BinOpInt
  exact p
  apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                    Ty.SubtypeJudgment.TSub_Refl             -- underlying int <: int
                    (by intro _; trivial)                     -- φ₁ → true
                  )
  apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
  simp [hΓx]
  apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                    Ty.SubtypeJudgment.TSub_Refl             -- underlying int <: int
                    (by intro _; trivial)                     -- φ₁ → true
                  )
  apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
  simp [hΓx]

lemma let_x_plus_x_y {p : ℕ} (x y: String) (σ: Env.ValEnv) (δ: Env.CircuitEnv) (Γ : Env.TyEnv)
  (hΓx: Γ x =  Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)) :
  @Ty.TypeJudgment σ δ 1000 Γ
    (Ast.Expr.letIn y
       (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
       (Ast.Expr.var y))
    (Ty.refin Ty.int (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))))
:= by
  apply Ty.TypeJudgment.T_LetIn
  · apply Ty.TypeJudgment.T_BinOpInt
    exact p
    · apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                        Ty.SubtypeJudgment.TSub_Refl
                        (by intro _; trivial))
      apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
      simp [hΓx]
    · apply Ty.TypeJudgment.T_SUB (Ty.SubtypeJudgment.TSub_Refine
                        Ty.SubtypeJudgment.TSub_Refl
                        (by intro _; trivial))
      apply Ty.TypeJudgment.TE_Var (Ast.Expr.constBool true)
      simp [hΓx]
  let sum_ty : Ast.Ty := Ast.Ty.refin Ast.Ty.int
      (Ast.expr_eq Ast.v
         (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))
  set Γ' := (Env.setTy Γ y (Ty.int.refin (expr_eq v ((Expr.var x).intExpr IntegerOp.add (Expr.var x)))))
  have h_sum_ty_judgment :
    @Ty.TypeJudgment σ δ 1000 Γ
      (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
      (Ast.Ty.refin Ast.Ty.int
      (Ast.expr_eq Ast.v
         (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))):= by {
        apply x_plus_x
        exact p
        apply hΓx
      }
  have hφ :
      (@Ty.TypeJudgment σ δ 1000 Γ (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))
        (Ast.Ty.refin Ast.Ty.int (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))))
      → PropSemantics.expr2prop σ δ 1000
          (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x))) :=
      @Ty.type_judgment2prop σ δ Γ 1000 Ast.Ty.int (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)) (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var x) Ast.IntegerOp.add (Ast.Expr.var x)))
  apply hφ at h_sum_ty_judgment
  -- ④ ボディ out の型付け（環境に out ↦ {v:int | v = x+x} が入っている）
  have hΓout : Γ' y = Ty.int.refin (expr_eq v (Expr.intExpr (Expr.var x) IntegerOp.add (Expr.var x))) := by {
    simp [Γ']
    unfold Env.setTy
    simp_all
  }
  rw[← hΓout]
  apply Ty.TE_Var_env h_sum_ty_judgment hΓout

@[simp]
def mulCircuit : Circuit.Circuit := {
  name   := "mul",
  inputs := ("x", Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)),
  output := ("out", Ast.Ty.refin (Ast.Ty.int) (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x")))),
  body   := (Ast.Expr.letIn "out" (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")) (Ast.Expr.var "out"))
}
def δ₁ : Env.CircuitEnv := fun nm => if nm = "mul" then mulCircuit else mulCircuit

theorem mulCircuit_correct : (Ty.circuit2prop 7 δ₁ mulCircuit) := by
  -- circuit2prop の定義展開と前提の整理
  unfold Ty.circuit2prop
  unfold mulCircuit
  simp_all
  -- 任意の入力 x と型付け前提 hΓ を仮定
  intro x hσ
  set σ := (Env.setVal (fun x ↦ Value.vStar) "x" (Value.vInt x))
  set Γ := (Env.setTy (fun x ↦ Ty.unit) "x" (Ty.int.refin (Expr.constBool true)))
  -- let-in レマを呼び出して本体の型付けを得る
  have h_body :
    Ty.TypeJudgment
      (Env.setTy (fun _ => Ast.Ty.unit) "x" (Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)))
      (Ast.Expr.letIn "out"
         (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x"))
         (Ast.Expr.var "out"))
      (Ast.Ty.refin Ast.Ty.int
         (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))) := by {
          apply @let_x_plus_x_y 7 "x" "out" σ δ₁ Γ
          simp [Γ]
          rfl
         }
  have h_sub :
    @Ty.SubtypeJudgment σ δ₁ Γ 1000
      (pure (Ast.Ty.refin Ast.Ty.int (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.var "x") Ast.IntegerOp.add (Ast.Expr.var "x")))))
      (pure (Ast.Ty.refin Ast.Ty.int (Ast.expr_eq Ast.v (Ast.Expr.intExpr (Ast.Expr.constInt 2) Ast.IntegerOp.mul (Ast.Expr.var "x"))))) := by {
        apply x_plus_x_eq_2_times_x σ δ₁ Γ "x" x
        simp [σ]
        rfl
      }
  exact Ty.TypeJudgment.T_SUB h_sub h_body


def σ₁ : Env.ValEnv := fun x =>
  if x = "x" then Ast.Value.vInt 5 else Ast.Value.vStar
def Γ₁ : Env.TyEnv := fun _ => Ast.Ty.refin Ast.Ty.int (Ast.Expr.constBool true)
#eval Eval.eval σ₁ δ₁ 123 mulCircuit.body
