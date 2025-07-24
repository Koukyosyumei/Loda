import Lean
import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Loda.Ast
import Loda.Typing
import Loda.Field
import Loda.Env
import Loda.Eval

open Lean Parser
open Lean Meta

---------------------------------------------
--------------- Declare Types ---------------
---------------------------------------------
declare_syntax_cat loda_ty

-- Basic types
syntax "Field"                                 : loda_ty
syntax "Bool"                                  : loda_ty

-- Array types: “[T]”
syntax "[" loda_ty "]"                         : loda_ty

-- Refinement types: “{ x : T | φ }”
syntax "{" loda_ty "|" term "}"      : loda_ty

-- Function‐type arrow: “(x : T1) → T2”
syntax "(" ident ":" loda_ty ")" "→" loda_ty   : loda_ty

---------------------------------------------------
--------------- Declare Expressions ---------------
---------------------------------------------------
declare_syntax_cat loda_expr

-- Constants:
syntax num                                       : loda_expr
syntax "true"                                    : loda_expr
syntax "false"                                   : loda_expr

-- Wildcard “*”
syntax "*"                                       : loda_expr

-- Variables (any identifier)
syntax ident                                     : loda_expr

-- Boolean‐operators: “e₁ ∧ e₂” or “e₁ && e₂”, “e₁ ∨ e₂” or “e₁ || e₂”
syntax loda_expr "&&" loda_expr                  : loda_expr
syntax loda_expr "||" loda_expr                  : loda_expr
syntax loda_expr "and" loda_expr                 : loda_expr  -- alternative keyword
syntax loda_expr "or"  loda_expr                 : loda_expr

-- Integer ops:  “e₁ + e₂”  “e₁ - e₂”  “e₁ * e₂”
syntax loda_expr "+" loda_expr                   : loda_expr
syntax loda_expr "-" loda_expr                   : loda_expr
syntax loda_expr "*" loda_expr                   : loda_expr
syntax loda_expr "/" loda_expr                   : loda_expr

-- Relational:  “e₁ == e₂”  “e₁ < e₂”  “e₁ <= e₂”
syntax loda_expr "==" loda_expr                  : loda_expr
syntax loda_expr "<"  loda_expr                  : loda_expr
syntax loda_expr "<=" loda_expr                  : loda_expr

-- Branch: if c {e₁} else {e₂}
syntax "if" loda_expr "{" loda_expr "}" "else" "{" loda_expr "}" : loda_expr

-- Assert: “assert e₁ = e₂”
syntax "assert" loda_expr "=" loda_expr          : loda_expr

-- Circuit reference:  “#Name (e₁, e₂, … ,eₙ)”
syntax "#" ident "(" sepBy1(loda_expr, ",") ")"  : loda_expr

-- Array cons: “e₁ :: e₂”
syntax loda_expr "::" loda_expr                  : loda_expr
-- Array length: “length a”
syntax "length" loda_expr                        : loda_expr
-- Array indexing: “a[e]”
syntax loda_expr "[" loda_expr "]"               : loda_expr

-- Lambda:  “lam x: T => e”
syntax "lam" ident ":" loda_ty "=>" loda_expr    : loda_expr

-- Application (juxtaposition) is “f a” or you can rely on precedence of “loda_expr loda_expr” by default.
syntax loda_expr "(" loda_expr ")"               : loda_expr

-- Let‐binding: “let x = e₁ in e₂”
syntax "let" ident "=" loda_expr "in" loda_expr  : loda_expr

-- Iteration:  “iter init cond {step} acc”
syntax "iter" loda_expr loda_expr "{" loda_expr "}" loda_expr  : loda_expr

---------------------------------------------------
--------------- Declare Param ---------------------
---------------------------------------------------
declare_syntax_cat loda_param
syntax ident ":" loda_ty : loda_param

---------------------------------------------------
--------------- Declare Circuit -------------------
---------------------------------------------------
declare_syntax_cat loda_circuit

-- circuit A (x1, x2, …, xn) -> T {body}
syntax "circuit" ident "(" sepBy(loda_param, ",") ")" "->" loda_ty "{" loda_expr "}" : loda_circuit

---------------------------------------------------
--------------- Declare File ----------------------
---------------------------------------------------

declare_syntax_cat loda_file
syntax (loda_circuit)+ : loda_file

namespace Frontend

unsafe def elaborateProp (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  | `(term| $n:num) => do
      let v := n.getNat
      let v' := (v: F)
      pure (Ast.Expr.constF v')

  -- Boolean literals
  | `(term| True)  => pure (Ast.Expr.constBool True)
  | `(term| False) => pure (Ast.Expr.constBool False)

  -- Boolean variables (identifiers)  — we treat `p` as a Bool var
  | `(term| $x:ident) => pure (Ast.Expr.var x.getId.toString)

  -- ¬ φ
  | `(term| ! $φ:term) => do
      let φ' ← elaborateProp φ
      -- We could encode “¬ φ” as `boolExpr φ Not φ`, but we don’t currently have a `UnaryOp`.
      -- For now, we can say “(φ == false)”
      pure (Ast.Expr.binRel φ' Ast.RelOp.eq (Ast.Expr.constBool False))

  | `(term| $e₁:term + $e₂:term) => do
      let e₁' ← elaborateProp e₁
      let e₂' ← elaborateProp e₂
      pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.add e₂')

  | `(term| $e₁:term * $e₂:term) => do
      let e₁' ← elaborateProp e₁
      let e₂' ← elaborateProp e₂
      pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.mul e₂')

  -- φ && ψ  or φ ∧ ψ
  | `(term| $φ:term && $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.and ψ')

  | `(term| $φ:term "and" $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.and ψ')

  -- φ || ψ  or φ ∨ ψ
  | `(term| $φ:term || $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.or ψ')

  | `(term| $φ:term "or" $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.boolExpr φ' Ast.BooleanOp.or ψ')

  -- φ == ψ
  | `(term| $φ:term == $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.binRel φ' Ast.RelOp.eq ψ')

  -- φ < ψ
  | `(term| $φ:term < $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.binRel φ' Ast.RelOp.lt ψ')

  -- φ <= ψ
  | `(term| $φ:term <= $ψ:term) => do
      let φ' ← elaborateProp φ
      let ψ' ← elaborateProp ψ
      pure (Ast.Expr.binRel φ' Ast.RelOp.le ψ')

  | _ => throwError "unsupported proposition syntax: {stx}"


/-- Given a `Syntax` of category `loda_ty`, return the corresponding `Ast.Ty`. -/
unsafe def elaborateType (stx : Syntax) : MetaM Ast.Ty := do
  match stx with

  -- Field and Bool
  | `(loda_ty| Field)      => pure (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.const (Ast.Expr.constBool True)))
  | `(loda_ty| Bool)       => pure Ast.Ty.bool

  -- Array type: “[T]”
  | `(loda_ty| [ $t:loda_ty ]) => do
      let t' ← elaborateType t
      pure (Ast.Ty.arr t')

  -- Refinement: “{ x : T | φ }”
  | `(loda_ty| { $T:loda_ty | $φ:term } ) => do
      let T' ← match T with
      --| `(loda_ty| Int) => pure Ast.Ty.int
      | `(loda_ty| Field) => pure Ast.Ty.field
      | `(loda_ty| Bool) => pure Ast.Ty.bool
      | _ => throwError "unsupported type syntax: {stx}"
      -- We want to turn `φ` (a Lean `term`) into an `Ast.Expr` (of Boolean sort).
      let φ' ← elaborateProp φ
      pure (Ast.Ty.refin T' (Ast.Predicate.eq φ'))

  -- Function type: “(x : T1) → T2”
  | `(loda_ty| ( $x:ident : $Tdom:loda_ty ) → $Tcod:loda_ty ) => do
      let dom ← elaborateType Tdom
      let cod ← elaborateType Tcod
      pure (Ast.Ty.func x.getId.toString dom cod)

  | _ => throwError "unsupported type syntax: {stx}"

/--
  `elaborateExpr` turns a `Syntax` node of category `loda_expr` into an `Ast.Expr`.
  We match eagerly on every concrete‐syntax pattern we declared above.
-/
unsafe def elaborateExpr (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  -- Integer literal “123”: → `constF 123`
  | `(loda_expr| $n:num) => do
    let v := n.getNat
    let v' := (v: F)
    pure (Ast.Expr.constF v')

  -- Boolean literals
  | `(loda_expr| true)  => pure (Ast.Expr.constBool True)
  | `(loda_expr| false) => pure (Ast.Expr.constBool False)

  -- Wildcard “*”
  | `(loda_expr| *) => pure Ast.Expr.wildcard

  -- Variables (ident): “x”, “y”, etc.
  | `(loda_expr| $x:ident) => pure (Ast.Expr.var x.getId.toString)

  -- if c {e₁} else {e₂}
  | `(loda_expr| if $c {$e₁} else {$e₂}) => do
    let c' ← elaborateExpr c
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.branch c' e₁' e₂')

  -- assert e₁ = e₂
  | `(loda_expr| assert $e₁ = $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.assertE e₁' e₂')

  -- Boolean “e₁ && e₂”
  | `(loda_expr| $e₁ && $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.and e₂')

  | `(loda_expr| $e₁ and $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.and e₂')

  -- Boolean “e₁ || e₂”
  | `(loda_expr| $e₁ || $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.or e₂')

  | `(loda_expr| $e₁ or $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.boolExpr e₁' Ast.BooleanOp.or e₂')

  -- Field arithmetic: “e₁ + e₂”  “e₁ - e₂”  “e₁ * e₂”
  | `(loda_expr| $e₁ + $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.add e₂')

  | `(loda_expr| $e₁ - $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.sub e₂')

  | `(loda_expr| $e₁ * $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.mul e₂')

  | `(loda_expr| $e₁ / $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.fieldExpr e₁' Ast.FieldOp.div e₂')

  -- Relational: “e₁ == e₂”, “e₁ < e₂”, “e₁ <= e₂”
  | `(loda_expr| $e₁ == $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.binRel e₁' Ast.RelOp.eq e₂')

  | `(loda_expr| $e₁ < $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.binRel e₁' Ast.RelOp.lt e₂')

  | `(loda_expr| $e₁ <= $e₂) => do
    let e₁' ← elaborateExpr e₁
    let e₂' ← elaborateExpr e₂
    pure (Ast.Expr.binRel e₁' Ast.RelOp.le e₂')

  -- $ts,*
  -- Circuit reference: “#C (e₁, e₂, …, eN)”
  | `(loda_expr| # $C:ident ($args:loda_expr,*)) => do
    let name := C.getId.toString
    -- We only support a single‐argument circRef in AST, so if there are multiple args,
    -- you might want to nest them or wrap them in a tuple. For now, assume 1:
    match args.getElems.toList with
    | [a] =>
        let a'  ← elaborateExpr a
        pure (Ast.Expr.circRef name a')
    | _   => throwError "only single‐arg circuit calls supported, got {args.getElems.toList.length}"

  -- Array “cons”:  “e₁ :: e₂”
  | `(loda_expr| $h :: $t) => do
    let h' ← elaborateExpr h
    let t' ← elaborateExpr t
    pure (Ast.Expr.arrCons h' t')

  -- Array length: “length a”
  | `(loda_expr| length $a) => do
    let a' ← elaborateExpr a
    pure (Ast.Expr.arrLen a')

  -- Array indexing: “a[e]”
  | `(loda_expr| $a [ $i ] ) => do
    let a' ← elaborateExpr a
    let i' ← elaborateExpr i
    pure (Ast.Expr.arrIdx a' i')

  -- Lambda:  “lam x : T => body”
  | `(loda_expr| lam $x:ident : $T:loda_ty => $body) => do
    let T'   ← elaborateType T
    let b'   ← elaborateExpr body
    pure (Ast.Expr.lam x.getId.toString T' b')

  -- Application “f (a)”
  | `(loda_expr| $f ($a)) => do
    let f' ← elaborateExpr f
    let a' ← elaborateExpr a
    pure (Ast.Expr.app f' a')

  -- Let‐binding: “let x = v in body”
  | `(loda_expr| let $x:ident = $v in $body) => do
    let v' ← elaborateExpr v
    let b' ← elaborateExpr body
    pure (Ast.Expr.letIn x.getId.toString v' b')

  -- Iteration: “iter start cond {step} acc”
  | `(loda_expr| iter $s $c {$st} $acc) => do
    let s'   ← elaborateExpr s
    let c'   ← elaborateExpr c
    let st'  ← elaborateExpr st
    let acc' ← elaborateExpr acc
    -- We currently ignore the invariant–variable name `x`, but you could store it if you like.
    pure (Ast.Expr.iter s' c' st' acc')

  -- Catch‐all
  | _ => throwError "unsupported expression syntax: {stx}"

/-- Helper: elaborate a single parameter syntax `(x : T)` into `(String × Ast.Ty)`. -/
unsafe def elaborateParam (stx : Syntax) : MetaM (String × Ast.Ty) := do
  match stx with
  | `(loda_param| $x:ident : $T:loda_ty) => do
      let T' ← elaborateType T
      pure (x.getId.toString, T')
  | _ =>
      throwError "unsupported parameter syntax: {stx}, expected `x : T`"

-- circuit A (x1, x2, …, xn) -> T {body}
/-- Given a single `loda_circuit` syntax, produce an `Ast.Circuit`. -/
unsafe def elaborateCircuit (stx : Syntax) : MetaM Ast.Circuit := do
  match stx with
  | `(loda_circuit| circuit $name:ident ( $params,* ) -> $retTy:loda_ty { $body:loda_expr } ) => do
      let nameStr  := name.getId.toString
      let paramStx := params.getElems.toList
      let params₁  ← paramStx.mapM elaborateParam
      let retTy'   ← elaborateType retTy
      let body'    ← elaborateExpr body
      match params₁.head? with
      | some p =>       pure {
        name   := nameStr,
        inputs := p,
        output := ("output", retTy'),
        body   := body'
      }
      | _ => throwError "invalid `circuit …` syntax: {stx}"
  | _ => throwError "invalid `circuit …` syntax: {stx}"

/-- A “file” of Loda is one or more `circuit` declarations. -/
unsafe def elabLodaFile (stx : Syntax) : MetaM (Array Ast.Circuit) := do
  match stx with
  | `(loda_file| $[$cs:loda_circuit]*) =>
      cs.mapM fun c => elaborateCircuit c
  | _ => throwError "invalid Loda file syntax"

/--
  If you ever want to parse a string in MetaM (outside of the “command” front‐end),
  you can do something like this:
-/
unsafe def parseLodaProgram (content : String) : MetaM (List Ast.Circuit) := do
  let env ← getEnv
  let fname := `anonymous
  match Lean.Parser.runParserCategory env `loda_file content fname.toString with
  | Except.error err => throwError err
  | Except.ok stx   =>
      let cs ← elabLodaFile stx
      pure cs.toList

end Frontend
