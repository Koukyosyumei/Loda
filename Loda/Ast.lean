import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

import Loda.Field

/-!
  # Abstract Syntax Tree for Loda Expressions

  This module defines the Abstract Syntax Tree (AST) for Loda, including expression
  syntax (`Expr`), runtime values (`Value`), and type representations (`Type`).
  It also provides utilities for pretty-printing and equality checking.
-/

open Std (Format)

variable {p : ℕ} [Fact p.Prime]

namespace Ast

/-- Boolean binary operators. -/
inductive BooleanOp where
  | and   -- ∧
  | or    -- ∨
  deriving DecidableEq, Repr

/-- Integer binary operators. -/
inductive IntegerOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  deriving DecidableEq, Repr

/-- Field `F p` binary operators. -/
inductive FieldOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | div   -- /
  deriving DecidableEq, Repr

/-- Relational operators. -/
inductive RelOp where
  | eq   -- =
  | lt   -- <
  | le   -- ≤
  deriving DecidableEq, Repr

mutual
  /-- Core expressions syntax for Loda. -/
  inductive Expr where
    | constF      : (p: ℕ) → (x : F p) → Expr                            -- field constant
    | constInt    : (n: Int) → Expr                                      -- integer constant
    | constBool   : (b: Bool) → Expr                                     -- boolean constant
    | var         : (name: String) → Expr                                -- variable x
    | wildcard    : Expr                                                 -- ⋆
    | assertE     : (lhs: Expr) → (rhs: Expr) → Expr                     -- assert e₁ = e₂
    | boolExpr    : (lhs: Expr) → (op: BooleanOp) → (rhs: Expr) → Expr
    | intExpr     : (lhs: Expr) → (op: IntegerOp) → (rhs: Expr) → Expr
    | fieldExpr   : (lhs: Expr) → (op: FieldOp) → (rhs: Expr) → Expr
    | binRel      : (lhs: Expr) → (op: RelOp) → (rhs: Expr) → Expr       -- e₁ ⊘ e₂
    | circRef     : (name: String) → (arg: Expr) → Expr                  -- #C e₁ ... eₙ
    | arrCons     : (head: Expr) → (tail: Expr) → Expr                   -- e₁ :: e₂
    | arrMap      : (f: Expr) → (arr: Expr) → Expr                       -- map e₁ e₂
    | arrLen      : (arr: Expr) → Expr                                   -- length e
    | arrIdx      : (arr: Expr) → (idx: Expr) → Expr                     -- e₁[e₂]
    | prodCons    : (items: List Expr) → Expr                            -- (e₁, ..., eₙ)
    | prodMatch   : Expr → List String → Expr → Expr                     -- match e with (x₁,...,xₙ)→e
    | prodIdx     : (tuple: Expr) → (idx: Nat) → Expr                    -- e.i
    | lam         : (param: String) → (τ: Ty) → (body: Expr) → Expr      -- λx : τ. e
    | app         : (f: Expr) → (arg: Expr) → Expr                       -- e₁ e₂
    | letIn       : (name: String) → (val: Expr) → (body: Expr) → Expr   -- let x = e₁ in e₂
    | iter        : (start: Expr) → (stp: Expr) → (step: Expr) → (acc: Expr) → Expr

  /-- Runtime values in Loda. -/
  inductive Value where
    | vF       : (p: ℕ) → (x: F p) → Value
    | vStar    : Value
    | vInt     : (n: Int) → Value
    | vBool    : (b: Bool) → Value
    | vProd    : (elems: List Value) → Value
    | vArr     : (elems: List Value) → Value
    | vClosure : (param: String) → (body: Expr) → (σ: String → Value) → Value

  /-- Basic Types in CODA. -/
  inductive Ty where
    | unit     : Ty
    | field    : (p: ℕ) → Ty                                      -- F p
    | int      : Ty                                               -- Int
    | bool     : Ty                                               -- Bool
    | prod     : (tys: List Ty) → Ty                              -- T₁ × ... × Tₙ (unit is prod [])
    | arr      : (ty: Ty) → Ty                                    -- [T]
    | refin    : (ty: Ty) → (prop: Expr) → Ty                     -- {ν : T | ϕ}
    | func     : (param: String) → (dom: Ty) → (cond: Ty) → Ty    -- x: τ₁ → τ₂
    --deriving DecidableEq, Repr
end

/-- Pretty-print a `Value`. -/
def valueToString : Value → String
  | Value.vF p x      => s!"F{p}.mk {x.val}"
  | Value.vStar       => "*"
  | Value.vInt i      => toString i
  | Value.vBool b     => toString b
  | Value.vProd vs    =>
    let elems := vs.map valueToString
    s!"({String.intercalate ", " elems})"
  | Value.vArr vs     =>
    let elems := vs.map valueToString
    s!"[{String.intercalate ", " elems}]"
  | Value.vClosure n _ _ => s!"<closure {n}>"

instance : Repr Value where
  reprPrec v _ := Format.text (valueToString v)

/-- Test for equality of two `Value`s. -/
def valueEq : Value → Value → Bool
  | Value.vF p₁ x, Value.vF p₂ y               => p₁ = p₂ ∧ x.val % p₁ = y.val % p₁
  | Value.vF _ _, Value.vStar                  => true
  | Value.vStar, Value.vF _ _                  => true
  | Value.vInt i₁, Value.vInt i₂               => i₁ = i₂
  | Value.vBool b₁, Value.vBool b₂             => b₁ = b₂
  | Value.vProd vs₁, Value.vProd vs₂           => false -- vs₁.zip vs₂ |>.all fun (u, v) => valueEq u v
  | Value.vArr vs₁, Value.vArr vs₂             => false -- vs₁.zip vs₂ |>.all fun (u, v) => valueEq u v
  | Value.vClosure _ _ _, Value.vClosure _ _ _ => false -- closures not comparable
  | _, _                                       => false

instance : BEq Value where
  beq := valueEq

/-- Convenience: `exprEq e₁ e₂` builds `e₁ = e₂` as an `Expr`. -/
def exprEq (e₁ e₂: Expr): Expr :=
  Expr.binRel e₁ RelOp.eq e₂

def v: Expr := Expr.var ".v"

structure Circuit where
  name    : String
  inputs  : String × Ast.Ty
  output  : String × Ast.Ty
  body    : Ast.Expr

end Ast
