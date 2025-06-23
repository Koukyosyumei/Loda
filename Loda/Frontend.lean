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

-- Bracketed “unit” or empty‐tuple:
syntax "Unit"                                  : loda_ty
-- Field type with a prime: “F p”
syntax "F" num                                 : loda_ty
-- Built‐in Int and Bool
syntax "Int"                                   : loda_ty
syntax "Bool"                                  : loda_ty

-- Product types: “(T1 , T2 , … , Tn)” or “()” for unit
syntax "()"                                    : loda_ty  -- empty product = unit
syntax "(" loda_ty,+ ")"                       : loda_ty

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
syntax num                                       : loda_expr  -- integer literal
syntax "true"                                    : loda_expr
syntax "false"                                   : loda_expr
syntax num "." num                               : loda_expr  -- “p.x” for field literal: x ∈ F p

-- Wildcard “*”
syntax "*"                                       : loda_expr

-- Variables (any identifier)
syntax ident                                     : loda_expr

-- Boolean‐operators: “e1 ∧ e2” or “e1 && e2”, “e1 ∨ e2” or “e1 || e2”
syntax loda_expr "&&" loda_expr                  : loda_expr
syntax loda_expr "||" loda_expr                  : loda_expr
syntax loda_expr "and" loda_expr                 : loda_expr  -- alternative keyword
syntax loda_expr "or"  loda_expr                 : loda_expr

-- Integer ops:  “e1 + e2”  “e1 - e2”  “e1 * e2”
syntax loda_expr "+" loda_expr                   : loda_expr
syntax loda_expr "-" loda_expr                   : loda_expr
syntax loda_expr "*" loda_expr                   : loda_expr

-- Field ops: “e1 +ₓ e2”, “e1 -ₓ e2”, “e1 *ₓ e2”, “e1 /ₓ e2”  (use subscript X or “fadd fsub fmul fdiv”)
syntax loda_expr "fadd" loda_expr                : loda_expr
syntax loda_expr "fsub" loda_expr                : loda_expr
syntax loda_expr "fmul" loda_expr                : loda_expr
syntax loda_expr "fdiv" loda_expr                : loda_expr

-- Relational:  “e1 == e2”  “e1 < e2”  “e1 <= e2”
syntax loda_expr "==" loda_expr                  : loda_expr
syntax loda_expr "<"  loda_expr                  : loda_expr
syntax loda_expr "<=" loda_expr                  : loda_expr

-- Assert: “assert e1 = e2”
syntax "assert" loda_expr "=" loda_expr          : loda_expr

-- Circuit reference:  “#Name (e₁, e₂, … ,eₙ)”
syntax "#" ident "(" sepBy1(loda_expr, ",") ")"  : loda_expr

-- Array cons: “e₁ :: e₂”
syntax loda_expr "::" loda_expr                  : loda_expr
-- Array map: “map f a”
syntax "map" loda_expr loda_expr                 : loda_expr
-- Array length: “length a”
syntax "length" loda_expr                        : loda_expr
-- Array indexing: “a[e]”
syntax loda_expr "[" loda_expr "]"               : loda_expr

-- Tuples: “( e₁ , e₂ , … , eₙ )”
syntax "(" ")"                                   : loda_expr  -- unit‐tuple
syntax "(" sepBy1(loda_expr, ",") ")"            : loda_expr
-- Tuple match: “match e with (x1 , x2 , … , xn) => eBody”
syntax "match" loda_expr "with" "(" sepBy1(ident, ",") ")" "=>" loda_expr : loda_expr
-- Tuple indexing: “e.1”  “e.2” … etc.
syntax loda_expr "." num                         : loda_expr

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
      pure (Ast.Expr.constInt v)

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

  | `(term| $e1:term + $e2:term) => do
      let e1' ← elaborateProp e1
      let e2' ← elaborateProp e2
      pure (Ast.Expr.intExpr e1' Ast.IntegerOp.add e2')

  | `(term| $e1:term * $e2:term) => do
      let e1' ← elaborateProp e1
      let e2' ← elaborateProp e2
      pure (Ast.Expr.intExpr e1' Ast.IntegerOp.mul e2')

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
  -- Unit type “()` or “Unit”
  | `(loda_ty| Unit)  => pure (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.const (Ast.Expr.constBool True)))
  | `(loda_ty| () )   => pure Ast.Ty.unit

  -- Field type “F p”
  | `(loda_ty| F $p:num) => do
      let pVal := p.getNat
      pure (Ast.Ty.field pVal)

  -- Int and Bool
  | `(loda_ty| Int)        => pure (Ast.Ty.refin Ast.Ty.int (Ast.Predicate.const (Ast.Expr.constBool True)))
  | `(loda_ty| Bool)       => pure Ast.Ty.bool

  -- Product types: “( T1 , T2 , … )”
  | `(loda_ty| ( $ts,* ) ) => do
      let tys ← ts.getElems.toList.mapM fun elem => elaborateType elem
      match tys with
      | []      => pure Ast.Ty.unit
      | _       => pure (Ast.Ty.prod tys)

  -- Array type: “[T]”
  | `(loda_ty| [ $t:loda_ty ]) => do
      let t' ← elaborateType t
      pure (Ast.Ty.arr t')

  -- Refinement: “{ x : T | φ }”
  | `(loda_ty| { $T:loda_ty | $φ:term } ) => do
      let T' ← match T with
      | `(loda_ty| Int) => pure Ast.Ty.int
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
  -- Integer literal “123”: → `constInt 123`
  | `(loda_expr| $n:num) => do
      let v := n.getNat
      pure (Ast.Expr.constInt v)

  -- Field literal “p.x”   where `p` and `x` are both numeral tokens
  | `(loda_expr| $p:num . $x:num) => do
      let pVal := p.getNat
      let xVal := x.getNat
      pure (Ast.Expr.constF pVal xVal)

  -- Boolean literals
  | `(loda_expr| true)  => pure (Ast.Expr.constBool True)
  | `(loda_expr| false) => pure (Ast.Expr.constBool False)

  -- Wildcard “*”
  | `(loda_expr| *) => pure Ast.Expr.wildcard

  -- Variables (ident): “x”, “y”, etc.
  | `(loda_expr| $x:ident) => pure (Ast.Expr.var x.getId.toString)

  -- assert e1 = e2
  | `(loda_expr| assert $e1 = $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.assertE e1' e2')

  -- Boolean “e1 && e2”
  | `(loda_expr| $e1 && $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.boolExpr e1' Ast.BooleanOp.and e2')

  | `(loda_expr| $e1 and $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.boolExpr e1' Ast.BooleanOp.and e2')

  -- Boolean “e1 || e2”
  | `(loda_expr| $e1 || $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.boolExpr e1' Ast.BooleanOp.or e2')

  | `(loda_expr| $e1 or $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.boolExpr e1' Ast.BooleanOp.or e2')

  -- Integer arithmetic: “e1 + e2”  “e1 - e2”  “e1 * e2”
  | `(loda_expr| $e1 + $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.intExpr e1' Ast.IntegerOp.add e2')

  | `(loda_expr| $e1 - $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.intExpr e1' Ast.IntegerOp.sub e2')

  | `(loda_expr| $e1 * $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.intExpr e1' Ast.IntegerOp.mul e2')

  -- Field operations: “fadd e1 e2”, “fsub e1 e2”, “fmul e1 e2”, “fdiv e1 e2”
  | `(loda_expr| $e1 fadd $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.fieldExpr e1' Ast.FieldOp.add e2')

  | `(loda_expr| $e1 fsub $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.fieldExpr e1' Ast.FieldOp.sub e2')

  | `(loda_expr| $e1 fmul $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.fieldExpr e1' Ast.FieldOp.mul e2')

  | `(loda_expr| $e1 fdiv $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.fieldExpr e1' Ast.FieldOp.div e2')

  -- Relational: “e1 == e2”, “e1 < e2”, “e1 <= e2”
  | `(loda_expr| $e1 == $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.binRel e1' Ast.RelOp.eq e2')

  | `(loda_expr| $e1 < $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.binRel e1' Ast.RelOp.lt e2')

  | `(loda_expr| $e1 <= $e2) => do
      let e1' ← elaborateExpr e1
      let e2' ← elaborateExpr e2
      pure (Ast.Expr.binRel e1' Ast.RelOp.le e2')

  -- $ts,*
  -- Circuit reference: “#C (e1, e2, …, eN)”
  | `(loda_expr| # $C:ident ($args:loda_expr,*)) => do
      let name := C.getId.toString
      -- We only support a single‐argument circRef in AST, so if there are multiple args,
      -- you might want to nest them or wrap them in a tuple. For now, assume 1:
      match args.getElems.toList with
      | [a] =>
        let a'  ← elaborateExpr a
        pure (Ast.Expr.circRef name a')
      | _   => throwError "only single‐arg circuit calls supported, got {args.getElems.toList.length}"

  -- Array “cons”:  “e1 :: e2”
  | `(loda_expr| $h :: $t) => do
      let h' ← elaborateExpr h
      let t' ← elaborateExpr t
      pure (Ast.Expr.arrCons h' t')

  -- Array map:  “map f a”
  | `(loda_expr| map $f $a) => do
      let f' ← elaborateExpr f
      let a' ← elaborateExpr a
      pure (Ast.Expr.arrMap f' a')

  -- Array length: “length a”
  | `(loda_expr| length $a) => do
      let a' ← elaborateExpr a
      pure (Ast.Expr.arrLen a')

  -- Array indexing: “a[e]”
  | `(loda_expr| $a [ $i ] ) => do
      let a' ← elaborateExpr a
      let i' ← elaborateExpr i
      pure (Ast.Expr.arrIdx a' i')

  -- Tuple “( )” or “( e1 , e2 , … )”
  | `(loda_expr| ( ) ) => pure (Ast.Expr.prodCons [])   -- empty tuple
  | `(loda_expr| ( $es,* ) ) => do
      let elems ← es.getElems.toList.mapM elaborateExpr
      pure (Ast.Expr.prodCons elems)

  -- Match on tuple: “match e with ( x1 , x2 , … ) => body”
  | `(loda_expr| match $e with ( $xs,* ) => $body) => do
      let e'    ← elaborateExpr e
      let names := xs.getElems.toList.map fun x => x.getId.toString
      let b'    ← elaborateExpr body
      pure (Ast.Expr.prodMatch e' names b')

  -- Tuple‐indexing: “e . i”
  | `(loda_expr| $e . $i:num ) => do
      let e' ← elaborateExpr e
      let idx := i.getNat
      pure (Ast.Expr.prodIdx e' idx)

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
