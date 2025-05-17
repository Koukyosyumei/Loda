import Lean.Elab.Command

import Loda.Ast
import Loda.Typing
import Load.Compile

open Lean Meta

-- Main syntax categories
declare_syntax_cat loda_circuit
declare_syntax_cat loda_param
declare_syntax_cat loda_ty
declare_syntax_cat loda_expr

-- Type syntax
syntax "F" : loda_ty
syntax "Int" : loda_ty
syntax "Bool" : loda_ty
syntax "{" ident ":" loda_ty "|" term "}" : loda_ty  -- Refinement type
syntax "[" loda_ty "]" : loda_ty                     -- Array type
syntax loda_ty "^" term : loda_ty                    -- Sized array

-- Expression syntax
syntax ident : loda_expr                             -- Variables
syntax num : loda_expr                               -- Numbers
syntax "*" : loda_expr                               -- Wildcard
syntax "assert" loda_expr "=" loda_expr : loda_expr  -- Assertions
syntax "#" ident loda_expr* : loda_expr              -- Circuit references
syntax loda_expr "[" loda_expr "]" : loda_expr       -- Array indexing
syntax "\\" ident "." loda_expr : loda_expr          -- Lambda expressions
syntax "let" ident "=" loda_expr "in" loda_expr : loda_expr  -- Let bindings

-- Iterator with invariant annotation
syntax "iter" loda_expr loda_expr "(" loda_expr ")" "(" loda_expr ")"
       "inv:" "(" "\\" ident "." loda_ty ")" : loda_expr

-- Circuit declarations
syntax "circuit" ident
       "(" sepBy(loda_param, ",") ")"
       "->" loda_ty "{" loda_expr "}" : loda_circuit

-- Parameter syntax
syntax ident ":" loda_ty : loda_param

-- Make it usable as a command
syntax "loda_circuit" loda_circuit : command

@[command_elab "loda_circuit"] def elabCodaCircuit : CommandElab
  | `(loda_circuit $circ) => do
    let ast ← elaborateCircuit circ
    -- Register the circuit in an environment
    addCodaCircuit ast
    -- You might also want to output the circuit definition
    pure ()

def elaborateCircuit (stx : Syntax) : MetaM Ast.Circuit := do
  match stx with
  | `(loda_circuit| circuit $name:ident ($params,*) -> $retTy $body) => do
    let name := name.getId.toString
    let params ← params.mapM elaborateParam
    let retTy ← elaborateType retTy
    let body ← elaborateExpr body
    pure { name := name, inputs := params, output := retTy, body := body }
  | _ => throwError "Invalid circuit syntax"

def elaborateType (stx : Syntax) : MetaM Ast.Ty := do
  match stx with
  | `(loda_ty| F) =>
    -- You might need to specify which field (which prime p)
    pure (Ast.Ty.field 0) -- Replace with appropriate prime
  | `(loda_ty| Int) =>
    pure Ast.Ty.int
  | `(loda_ty| Bool) =>
    pure Ast.Ty.bool
  | `(loda_ty| { $v:ident : $t:loda_ty | $phi:term }) => do
    let tAst ← elaborateType t
    let vName := v.getId.toString
    -- Convert phi to a Prop; this is challenging and requires special handling
    let phiProp ← elaborateProp phi
    -- Create a dummy value for the refinement
    let dummyValue := Ast.Value.vStar -- This might need to be improved
    pure (Ast.Ty.refin dummyValue tAst phiProp)
  -- Handle other type forms...
  | _ => throwError "Unsupported type syntax"

def elaborateExpr (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  | `($n:numLit) =>
    if let some num := n.isNatLit? then
      pure (Loda.Ast.Expr.constInt (Int.ofNat num))
    else
      throwError "Invalid number literal"
  | `($x:ident) =>
    pure (Loda.Ast.Expr.var x.getId.toString)
  | `(*) =>
    pure Loda.Ast.Expr.wildcard
  | `(assert $e1 = $e2) => do
    let e1Ast ← elaborateExpr e1
    let e2Ast ← elaborateExpr e2
    pure (Loda.Ast.Expr.assertE e1Ast e2Ast)
  -- Handle other expression forms...
  | _ => throwError "Unsupported expression syntax"
