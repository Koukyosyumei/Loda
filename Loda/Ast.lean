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

variable {p : ℕ} [Fact p.Prime]

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
    | constF      : (p: ℕ) → (x : F p) → Expr                            -- field constant
    | constInt    : (n: ℤ) → Expr                                      -- integer constant
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
    deriving Lean.ToExpr

  /-- Runtime values in Loda. -/
  inductive Value where
    | vF       : (p: ℕ) → (x: F p) → Value
    | vStar    : Value
    | vInt     : (n: ℤ) → Value
    | vBool    : (b: Bool) → Value
    | vProd    : (elems: List Value) → Value
    | vArr     : (elems: List Value) → Value
    | vClosure : (param: String) → (body: Expr) → (σ: List (String × Value)) → Value
    deriving Lean.ToExpr

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
    deriving Lean.ToExpr
end

/-- Test for equality of two `Value`s. -/
def valueEq : Value → Value → Bool
  | Value.vF p₁ x, Value.vF p₂ y               => p₁ = p₂ ∧ x.val % p₁ = y.val % p₁
  | Value.vF _ _, Value.vStar                  => true
  | Value.vStar, Value.vF _ _                  => true
  | Value.vStar, Value.vStar                   => true
  | Value.vInt i₁, Value.vInt i₂               => i₁ = i₂
  | Value.vBool b₁, Value.vBool b₂             => b₁ = b₂
  | Value.vProd vs₁, Value.vProd vs₂           => false -- vs₁.zip vs₂ |>.all fun (u, v) => valueEq u v
  | Value.vArr vs₁, Value.vArr vs₂             => false -- vs₁.zip vs₂ |>.all fun (u, v) => valueEq u v
  --| Value.vClosure _ _ _, Value.vClosure _ _ _ => false -- closures not comparable
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
    | Expr.constF p x        => s!"F{p}.mk {x.val}"
    | Expr.constInt n        => toString n
    | Expr.constBool b       => toString b
    | Expr.var name          => name
    | Expr.wildcard          => "⋆"
    | Expr.assertE l r       => s!"assert {exprToString l} = {exprToString r}"
    | Expr.boolExpr l op r   => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.intExpr l op r    => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.fieldExpr l op r  => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.binRel l op r     => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.circRef name arg  => s!"#{name} {exprToString arg}"
    | Expr.arrCons h t       => s!"{exprToString h} :: {exprToString t}"
    | Expr.arrMap f a        => s!"map {exprToString f} {exprToString a}"
    | Expr.arrLen a          => s!"length {exprToString a}"
    | Expr.arrIdx a i        => s!"{exprToString a}[{exprToString i}]"
    | Expr.prodCons items    =>
        let strs := items.map exprToString
        s!"({String.intercalate ", " strs})"
    | Expr.prodMatch e names body =>
        let pat := "(" ++ String.intercalate ", " names ++ ")"
        s!"match {exprToString e} with {pat} → {exprToString body}"
    | Expr.prodIdx t i       => s!"{exprToString t}.{i}"
    | Expr.lam param τ body  => s!"λ{param} : {tyToString τ}. {exprToString body}"
    | Expr.app f arg         => s!"{exprToString f} {exprToString arg}"
    | Expr.letIn n v b       => s!"let {n} = {exprToString v} in {exprToString b}"
    | Expr.iter s e step acc =>
        s!"iter {exprToString s} {exprToString e} {exprToString step} {exprToString acc}"

  partial def tyToString : Ty → String
    | Ty.unit           => "unit"
    | Ty.field p        => s!"F{p}"
    | Ty.int            => "Int"
    | Ty.bool           => "Bool"
    | Ty.prod tys       =>
        match tys with
        | [] => "unit"
        | [t] => tyToString t
        | _ => "(" ++ String.intercalate " × " (tys.map tyToString) ++ ")"
    | Ty.arr t          => s!"[{tyToString t}]"
    | Ty.refin t e      => s!"{tyToString t} | {exprToString e}"
    | Ty.func x d c     => s!"({x} : {tyToString d}) → {tyToString c}"
end

instance : Repr Expr where
  reprPrec e _ := Format.text (exprToString e)

instance : Repr Ty where
  reprPrec e _ := Format.text (tyToString e)

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
