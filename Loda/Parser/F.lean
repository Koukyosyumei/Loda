import Lean
import Lean.Meta
import Lean.Elab.Command
import Lean.Parser

import Loda.Ast
import Loda.Typing
import Loda.Field

open Lean Parser
open Lean Meta

---------------------------------------------
--------------- Declare Types ---------------
---------------------------------------------

declare_syntax_cat loda_ty

-- Bracketed “unit” or empty‐tuple:
syntax "Unit" : loda_ty

-- Field type with a prime: “F p”
syntax "F" num : loda_ty

-- Built‐in Int and Bool
syntax "Int"  : loda_ty
syntax "Bool" : loda_ty

-- Product types: “(T1 , T2 , … , Tn)” or “()” for unit
syntax "()"                                        : loda_ty  -- empty product = unit
syntax "(" sepBy1(loda_ty, ",") ")"                    : loda_ty

-- Array types: “[T]”
syntax "[" loda_ty "]"                                : loda_ty

-- Refinement types: “{ x : T | φ }”
syntax "{" ident ":" loda_ty "|" term "}"              : loda_ty

-- Function‐type arrow: “(x : T1) → T2”
syntax "(" ident ":" loda_ty ")" "→" loda_ty           : loda_ty

---------------------------------------------------
--------------- Declare Expressions ---------------
---------------------------------------------------

declare_syntax_cat loda_expr

-- Constants:
syntax num                                       : loda_expr  -- integer literal
syntax "true"                                    : loda_expr
syntax "false"                                   : loda_expr
syntax num "." num                                : loda_expr  -- “p.x” for field literal: x ∈ F p

-- Wildcard “*”
syntax "*"                                       : loda_expr

-- Variables (any identifier)
syntax ident                                     : loda_expr

-- Boolean‐operators: “e1 ∧ e2” or “e1 && e2”, “e1 ∨ e2” or “e1 || e2”
syntax loda_expr "&&" loda_expr                   : loda_expr
syntax loda_expr "||" loda_expr                   : loda_expr
syntax loda_expr "and" loda_expr                   : loda_expr  -- alternative keyword
syntax loda_expr "or"  loda_expr                   : loda_expr

-- Integer ops:  “e1 + e2”  “e1 - e2”  “e1 * e2”
syntax loda_expr "+" loda_expr                     : loda_expr
syntax loda_expr "-" loda_expr                     : loda_expr
syntax loda_expr "*" loda_expr                     : loda_expr

-- Field ops: “e1 +ₓ e2”, “e1 -ₓ e2”, “e1 *ₓ e2”, “e1 /ₓ e2”  (use subscript X or “fadd fsub fmul fdiv”)
syntax loda_expr "fadd" loda_expr : loda_expr      -- interpret as FieldOp.add
syntax loda_expr "fsub" loda_expr : loda_expr
syntax loda_expr "fmul" loda_expr : loda_expr
syntax loda_expr "fdiv" loda_expr : loda_expr

-- Relational:  “e1 == e2”  “e1 < e2”  “e1 <= e2”
syntax loda_expr "==" loda_expr                     : loda_expr
syntax loda_expr "<"  loda_expr                     : loda_expr
syntax loda_expr "<=" loda_expr                     : loda_expr

-- Assert: “assert e1 = e2”
syntax "assert" loda_expr "=" loda_expr             : loda_expr

-- Circuit reference:  “#Name e₁ e₂ … eₙ”
syntax "#" ident (loda_expr)+                       : loda_expr

-- Array cons: “e₁ :: e₂”
syntax loda_expr "::" loda_expr                     : loda_expr

-- Array map: “map f a”
syntax "map" loda_expr loda_expr                     : loda_expr

-- Array length: “length a”
syntax "length" loda_expr                           : loda_expr

-- Array indexing: “a[e]”
syntax loda_expr "[" loda_expr "]"                   : loda_expr

-- Tuples: “( e₁ , e₂ , … , eₙ )”
syntax "(" ")"                                        : loda_expr  -- unit‐tuple
syntax "(" sepBy1(loda_expr, ",") ")"                 : loda_expr

-- Tuple match: “match e with (x1 , x2 , … , xn) => eBody”
syntax "match" loda_expr "with" "(" sepBy1(ident, ",") ")" "=>" loda_expr : loda_expr

-- Tuple indexing: “e.1”  “e.2” … etc.
syntax loda_expr "." num                              : loda_expr

-- Lambda:  “λ x : T => e”   or “\\x: T => e”
syntax "\\" ident ":" loda_ty "=>" loda_expr          : loda_expr

-- Application (juxtaposition) is “f a” or you can rely on precedence of “loda_expr loda_expr” by default.

-- Let‐binding: “let x = e₁ in e₂”
syntax "let" ident "=" loda_expr "in" loda_expr       : loda_expr

-- Iteration:  “iter init cond (step) (acc) inv: ( λx . T )”
syntax "iter" loda_expr loda_expr "(" loda_expr ")" "(" loda_expr ")" "inv:" "(" "\\" ident "." loda_ty ")" : loda_expr

declare_syntax_cat loda_param
syntax ident ":" loda_ty                              : loda_param

declare_syntax_cat loda_circuit
syntax "circuit" ident "(" sepBy(loda_param, ",") ")" "->" loda_ty "{" loda_expr "}" : loda_circuit

declare_syntax_cat loda_file
syntax (loda_circuit)+                               : loda_file

syntax "loda_circuit" loda_circuit                    : command

namespace Frontend

unsafe def elaborateProp (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  -- Boolean literals
  | `(term| True)  => pure (Ast.Expr.constBool True)
  | `(term| False) => pure (Ast.Expr.constBool False)

  -- Boolean variables (identifiers)  — we treat `p` as a Bool var
  | `(term| $x:ident) => pure (Ast.Expr.var x.getId.toString)

  -- ¬ φ
  | `(term| ! $φ:term) => do
      let φ' ← elaborateProp φ
      -- You could encode “¬ φ” as `boolExpr φ Not φ`, but you don’t currently have a `UnaryOp`.
      -- For now, we can say “(φ == false)”
      pure (Ast.Expr.binRel φ' Ast.RelOp.eq (Ast.Expr.constBool False))

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
  | `(loda_ty| Unit)       => pure Ast.Ty.unit
  | `(loda_ty| () )   => pure Ast.Ty.unit

  -- Field type “F p”
  | `(loda_ty| F $p:num) => do
      let pVal := p.getNat
      pure (Ast.Ty.field pVal)

  -- Int and Bool
  | `(loda_ty| Int)        => pure Ast.Ty.int
  | `(loda_ty| Bool)       => pure Ast.Ty.bool

  -- Array type: “[T]”
  | `(loda_ty| [ $t:loda_ty ]) => do
      let t' ← elaborateType t
      pure (Ast.Ty.arr t')

  -- Refinement: “{ x : T | φ }”
  | `(loda_ty| { $_:ident : $T:loda_ty | $φ:term } ) => do
      let T'   ← elaborateType T
      -- We want to turn `φ` (a Lean `term`) into an `Ast.Expr` (of Boolean sort).
      let φ'   ← elaborateProp φ
      pure (Ast.Ty.refin T' φ')

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

  -- Circuit reference: “#C e1 e2 … eN”
  /-
  | `(loda_expr| # $C:ident $args*) => do
      let name := C.getId.toString
      -- We only support a single‐argument circRef in AST, so if there are multiple args,
      -- you might want to nest them or wrap them in a tuple. For now, assume 1:
      match args.getElems with
      | [a] =>
        let a'  ← elaborateExpr a
        pure (Ast.Expr.circRef name a')
      | _   => throwError "only single‐arg circuit calls supported, got {args.getElems.length}"
  -/

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
  /-
  | `(loda_expr| ( $es:sepBy(_ , ",") ) ) => do
      let elems ← es.getElems.mapM elaborateExpr
      pure (Ast.Expr.prodCons elems)
  -/

  -- Match on tuple: “match e with ( x1 , x2 , … ) => body”
  /-
  | `(loda_expr| match $e with ( $xs:sepBy(ident, ",") ) => $body) => do
      let e'    ← elaborateExpr e
      let names := xs.getElems.map fun x => x.getId.toString
      let b'    ← elaborateExpr body
      pure (Ast.Expr.prodMatch e' names b')
  -/

  -- Tuple‐indexing: “e . i”
  | `(loda_expr| $e . $i:num ) => do
      let e' ← elaborateExpr e
      let idx := i.getNat
      pure (Ast.Expr.prodIdx e' idx)

  -- Lambda:  “\\ x : T => body”
  /-
  | `(loda_expr| "\\" $x:ident ":" $T:loda_ty "=>" $body) => do
      let T'   ← elaborateType T
      let b'   ← elaborateExpr body
      pure (Ast.Expr.lam x.getId.toString T' b')
  -/

  -- Application “f a”
  /-
  | `(loda_expr| $f $a) => do
      let f' ← elaborateExpr f
      let a' ← elaborateExpr a
      pure (Ast.Expr.app f' a')
  -/

  -- Let‐binding: “let x = v in body”
  | `(loda_expr| let $x:ident = $v in $body) => do
      let v' ← elaborateExpr v
      let b' ← elaborateExpr body
      pure (Ast.Expr.letIn x.getId.toString v' b')

  /-
  -- Iteration: “iter start cond (step) (acc) inv:( \\x . T )”
  | `(loda_expr| iter $s $c "(" $st:_) "(" $acc:_) inv:( "\\" $x:ident "." $T:loda_ty ")" ) => do
      let s'   ← elaborateExpr s
      let c'   ← elaborateExpr c
      let st'  ← elaborateExpr st
      let acc' ← elaborateExpr acc
      let T'   ← elaborateType T
      -- We currently ignore the invariant–variable name `x`, but you could store it if you like.
      pure (Ast.Expr.iter s' c' st' acc')
  -/

  -- Catch‐all
  | _ => throwError "unsupported expression syntax: {stx}"

end Frontend
