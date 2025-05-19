import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

import Loda.Field

open Std (Format)

variable {p : ℕ} [Fact p.Prime]

namespace Ast

/-- Field operators =⊙. -/
inductive BooleanOp where
  | and   -- ∧
  | or   -- ∨
  deriving DecidableEq, Repr

/-- Field operators =⊕. -/
inductive IntegerOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  deriving DecidableEq, Repr

/-- Field operators =⊗. -/
inductive FieldOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | div   -- /
  deriving DecidableEq, Repr

/-- Binary relations =⊘. -/
inductive RelOp where
  | eq   -- =
  | lt   -- <
  | le   -- ≤
  deriving DecidableEq, Repr

mutual
  /-- AST of CODA expressions. -/
  inductive Expr where
    | constF      : ∀ p, F p → Expr                  -- field constant
    | constInt    : Int → Expr                       -- integer constant
    | constBool   : Bool → Expr                      -- boolean constant
    | var         : String → Expr                    -- variable x
    | wildcard    : Expr                             -- ⋆
    | assertE     : Expr → Expr → Expr               -- assert e₁ = e₂
    | boolExpr    : Expr → BooleanOp → Expr → Expr
    | intExpr     : Expr → IntegerOp → Expr → Expr
    | fieldExpr   : Expr → FieldOp → Expr → Expr
    | binRel      : Expr → RelOp → Expr → Expr       -- e₁ ⊘ e₂
    | circRef     : String → List Expr → Expr        -- #C e₁ ... eₙ
    | arrCons     : Expr → Expr → Expr               -- e₁ :: e₂
    | arrMap      : Expr → Expr → Expr               -- map e₁ e₂
    | arrLen      : Expr → Expr                      -- length e
    | arrIdx      : Expr → Expr → Expr               -- e₁[e₂]
    | prodCons    : List Expr → Expr                 -- (e₁, ..., eₙ)
    | prodMatch   : Expr → List String → Expr → Expr -- match e with (x₁,...,xₙ)→e
    | prodIdx     : Expr → Nat → Expr                -- e.i
    | lam         : String → Ty → Expr → Expr        -- λx : τ. e
    | app         : Expr → Expr → Expr               -- e₁ e₂
    | letIn       : String → Expr → Expr → Expr      -- let x = e₁ in e₂
    | iter        : Expr → -- start s
                    Expr → -- end e
                    Expr → -- step f
                    Expr → -- acc a
                    Expr      -- iteration body result

  /-- Values of CODA. -/
  inductive Value where
    | vF       : ∀ p, F p → Value
    | vStar    : Value
    | vInt     : Int → Value
    | vBool    : Bool → Value
    | vProd    : List Value → Value
    | vArr     : List Value → Value
    | vClosure : String → Expr → (String → Value) → Value

  /-- Basic Types in CODA. -/
  inductive Ty where
    | unit     : Ty
    | field    : ℕ → Ty                   -- F p
    | int      : Ty                       -- Int
    | bool     : Ty                       -- Bool
    | prod     : List Ty → Ty             -- T₁ × ... × Tₙ (unit is prod [])
    | arr      : Ty → Ty                  -- [T]
    | refin    : Ty → Expr → Ty   -- {ν : T | ϕ}
    | func     : String → Ty → Ty → Ty    -- x: τ₁ → τ₂
    --deriving DecidableEq, Repr
end

instance : Repr Value where
  reprPrec
    | Value.vF p x, _ => Format.text s!"F{p}.mk {x.val}"
    | Value.vStar, _    => Format.text "*"
    | Value.vInt i, _   => Format.text (toString i)
    | Value.vBool b, _  => Format.text (toString b)
    | Value.vProd vs, _ => Format.text "Prod"
    | Value.vArr vs, _  => Format.text "Arr"
    | Value.vClosure name _ _, _ => Format.text s!"<closure {name}>"

def beq : Value → Value → Bool
  | Value.vF p₁ x, Value.vF p₂ y        => p₁ = p₂ ∧ x.val % p₁ = y.val % p₁
  | Value.vF _ _, Value.vStar           => true
  | Value.vStar, Value.vF _ _           => true
  | Value.vInt i₁, Value.vInt i₂        => i₁ = i₂
  | Value.vBool b₁, Value.vBool b₂      => b₁ = b₂
  | Value.vProd _, Value.vProd _        => false --(xs.zip ys).all (fun (x, y) => (x = y))
  | Value.vArr _, Value.vArr _          => false
  | Value.vClosure _ _ _, Value.vClosure _ _ _ => false -- closures not comparable
  | _, _                    => false

instance : BEq Value where
  beq := beq

def eeq (e₁ e₂: Ast.Expr): Ast.Expr :=
  Ast.Expr.binRel e₁ Ast.RelOp.eq e₂
def v: Ast.Expr := Ast.Expr.var ".v"

end Ast
