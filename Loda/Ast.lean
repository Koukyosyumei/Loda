import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

import Lean
import Lean.Meta
import Lean.Elab.Command

import Std.Data.HashMap.Basic

import Loda.Field

/-!
  # Abstract Syntax Tree for Loda Expressions

  This module defines the Abstract Syntax Tree (AST) for Loda, including expression
  syntax (`Expr`), runtime values (`Value`), and type representations (`Type`).
  It also provides utilities for pretty-printing and equality checking.
-/

open Std (Format)

namespace Ast

/-- Boolean binary operators. -/
inductive BooleanOp where
  | and   -- ∧
  | or    -- ∨
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Integer binary operators. -/
inductive IntegerOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Field `F p` binary operators. -/
inductive FieldOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | div   -- /
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Relational operators. -/
inductive RelOp where
  | eq   -- =
  | lt   -- <
  | le   -- ≤
  deriving DecidableEq, Repr, Lean.ToExpr

mutual
  /-- Core expressions syntax for Loda. -/
  inductive Expr where
    | constF      : (x : F) → Expr                                       -- field constant
    | constBool   : (b: Bool) → Expr                                     -- boolean constant
    | var         : (name: String) → Expr                                -- variable x
    | wildcard    : Expr                                                 -- ⋆
    | assertE     : (lhs: Expr) → (rhs: Expr) → Expr                     -- assert e₁ = e₂
    | boolExpr    : (lhs: Expr) → (op: BooleanOp) → (rhs: Expr) → Expr
    | fieldExpr   : (lhs: Expr) → (op: FieldOp) → (rhs: Expr) → Expr
    | binRel      : (lhs: Expr) → (op: RelOp) → (rhs: Expr) → Expr       -- e₁ ⊘ e₂
    | circRef     : (name: String) → (arg: Expr) → Expr                  -- #C e₁ ... eₙ
    | arrCons     : (head: Expr) → (tail: Expr) → Expr                   -- e₁ :: e₂
    | arrLen      : (arr: Expr) → Expr                                   -- length e
    | arrIdx      : (arr: Expr) → (idx: Expr) → Expr                     -- e₁[e₂]
    | branch      : (cond: Expr) → (th: Expr) → (els: Expr) → Expr       -- if cond then e₁ else e₂
    | lam         : (param: String) → (τ: Ty) → (body: Expr) → Expr      -- λx : τ. e
    | app         : (f: Expr) → (arg: Expr) → Expr                       -- e₁ e₂
    | letIn       : (name: String) → (val: Expr) → (body: Expr) → Expr   -- let x = e₁ in e₂
    | iter        : (start: Expr) → (stp: Expr) → (step: Expr) → (acc: Expr) → Expr
    deriving Lean.ToExpr

  /-- Runtime values in Loda. -/
  inductive Value where
    | vF       : (x: F) → Value
    | vStar    : Value
    | vBool    : (b: Bool) → Value
    | vArr     : (elems: List Value) → Value
    | vClosure : (param: String) → (body: Expr) → (σ: List (String × Value)) → Value
    deriving Lean.ToExpr

  inductive Predicate where
    | const    : Expr → Predicate
    | eq       : Expr → Predicate
    deriving Lean.ToExpr

  /-- Basic Types in Loda. -/
  inductive Ty where
    | unknown  : Ty
    | unit     : Ty
    | field    : Ty                                               -- F p
    | bool     : Ty                                               -- Bool
    | arr      : (ty: Ty) → Ty                                    -- [T]
    | refin    : (ty: Ty) → (prop: Predicate) → Ty                -- {ν : T | ϕ}
    | func     : (param: String) → (dom: Ty) → (cond: Ty) → Ty    -- x: τ₁ → τ₂
    deriving Lean.ToExpr
end

/-- Test for equality of two `Value`s. -/
def valueEq : Value → Value → Bool
  | Value.vF x, Value.vF y                     => x = y
  | Value.vBool b₁, Value.vBool b₂             => b₁ = b₂
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
deriving Lean.ToExpr

instance : Repr BooleanOp where
  reprPrec
    | BooleanOp.and, _ => Format.text "∧"
    | BooleanOp.or, _  => Format.text "∨"

instance : Repr IntegerOp where
  reprPrec
    | IntegerOp.add, _ => Format.text "+"
    | IntegerOp.sub, _ => Format.text "-"
    | IntegerOp.mul, _ => Format.text "*"

instance : Repr FieldOp where
  reprPrec
    | FieldOp.add, _ => Format.text "+"
    | FieldOp.sub, _ => Format.text "-"
    | FieldOp.mul, _ => Format.text "*"
    | FieldOp.div, _ => Format.text "/"

instance : Repr RelOp where
  reprPrec
    | RelOp.eq, _ => Format.text "="
    | RelOp.lt, _ => Format.text "<"
    | RelOp.le, _ => Format.text "≤"

mutual
  partial def exprToString : Expr → String
    | Expr.constF x        => s!"F {x.val}"
    | Expr.constBool b       => toString b
    | Expr.var name          => name
    | Expr.wildcard          => "⋆"
    | Expr.assertE l r       => s!"assert {exprToString l} = {exprToString r}"
    | Expr.boolExpr l op r   => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.fieldExpr l op r  => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.binRel l op r     => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.circRef name arg  => s!"#{name} {exprToString arg}"
    | Expr.arrCons h t       => s!"{exprToString h} :: {exprToString t}"
    | Expr.arrLen a          => s!"length {exprToString a}"
    | Expr.arrIdx a i        => s!"{exprToString a}[{exprToString i}]"
    | Expr.branch c e₁ e₂    => s!"if {exprToString c} then {exprToString e₁} else {exprToString e₂}"
    | Expr.lam param τ body  => s!"λ{param} : {tyToString τ}. {exprToString body}"
    | Expr.app f arg         => s!"{exprToString f} {exprToString arg}"
    | Expr.letIn n v b       => s!"let {n} = {exprToString v} in {exprToString b}"
    | Expr.iter s e step acc =>
        s!"iter {exprToString s} {exprToString e} {exprToString step} {exprToString acc}"

  partial def predicateToString : Predicate → String
    | Predicate.const e => exprToString e
    | Predicate.eq    e => s!"v = {exprToString e}"

  partial def tyToString : Ty → String
    | Ty.unknown        => "unknown"
    | Ty.unit           => "unit"
    | Ty.field          => "F"
    | Ty.bool           => "Bool"
    | Ty.arr t          => s!"[{tyToString t}]"
    | Ty.refin t p      => s!"{tyToString t} | {predicateToString p}"
    | Ty.func x d c     => s!"({x} : {tyToString d}) → {tyToString c}"
end

instance : Repr Expr where
  reprPrec e _ := Format.text (exprToString e)

instance : Repr Ty where
  reprPrec e _ := Format.text (tyToString e)

/-- Pretty-print a `Value`. -/
def valueToString : Value → String
  | Value.vF x      => s!"F {x.val}"
  | Value.vStar       => "*"
  | Value.vBool b     => toString b
  | Value.vArr vs     =>
    let elems := vs.map valueToString
    s!"[{String.intercalate ", " elems}]"
  | Value.vClosure n _ _ => s!"<closure {n}>"

instance : Repr Value where
  reprPrec v _ := Format.text (valueToString v)

instance : Repr Circuit where
  reprPrec c _ :=
    let (inName, inTy) := c.inputs
    let (outName, outTy) := c.output
    Format.text s!
"Circuit \{
  name   := \"{c.name}\",
  input  := ({inName} : {repr inTy}),
  output := ({outName} : {repr outTy}),
  body   := {repr c.body}
}"

def DefaultCircuit : Circuit := {
    name := "dummy"
    inputs := ("_", Ty.unit)
    output := ("_", Ty.unit)
    body := Expr.wildcard
  }

instance : Inhabited Circuit where
  default := DefaultCircuit

end Ast
