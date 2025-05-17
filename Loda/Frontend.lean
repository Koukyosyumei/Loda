import Lean
import Lean.Meta
import Lean.Elab.Command

import Loda.Ast
import Loda.Typing
import Loda.Compile

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

-- Helper function to convert a Lean term to an Ast.Value (incomplete)
--  This is a simplified version.  You'll need to expand this significantly
--  to handle the full range of possible Lean expressions that might appear
--  in your Loda programs.
unsafe def elaborateTerm (stx : Syntax) (expectedType : Option Expr) : MetaM Expr := do
  match stx with
  | `(term| $i:ident) => do
    -- Resolve the identifier to a Lean expression.  This could be a
    -- variable, a constant, or a function.
    let expr ← elaborateTerm i none
    --  Optionally check the type.
    match expectedType with
    | some expected =>
      let actual ← inferType expr
      unless ← isDefEq expected actual do
        throwError "Type mismatch: expected {expected}, got {actual} for {i}"
    | none => pure ()
    return expr
  | `(term| $n:num) => do
    --  Handle numeric literals.  The type of the literal will be inferred
    --  by Lean, but we could optionally check it against an expectedType.
    let expr ← elaborateTerm n none
    match expectedType with
    | some expected =>
      let actual ← inferType expr
      unless ← isDefEq expected actual do
        throwError "Type mismatch: expected {expected}, got {actual} for {n}"
    | none => pure ()
    return expr
  | `(term| True) =>
    return mkConst ``True
  | `(term| False) =>
    return mkConst ``False
  | `(term| $b:term && $c:term) => do
    let b_expr ← elaborateTerm b none
    let c_expr ← elaborateTerm c none
    return mkApp2 (mkConst ``And) b_expr c_expr
  | `(term| $b:term || $c:term) => do
    let b_expr ← elaborateTerm b none
    let c_expr ← elaborateTerm c none
    return mkApp2 (mkConst ``Or) b_expr c_expr
  | `(term| ! $b:term) => do
    let b_expr ← elaborateTerm b none
    return mkApp (mkConst ``Not) b_expr
  | `(term| $f:term $arg:term) => do
    --  Handle function application.  Elaborate the function and the argument,
    --  and then apply the function to the argument.
    let f_expr ← elaborateTerm f none
    let arg_expr ← elaborateTerm arg none
    return mkApp f_expr arg_expr
  /-
  | `(term| $x:ident : $T:term => $b:term) => do
    let T_expr ← elaborateType T
     -- Introduce a bound variable with the specified type
    withLocalDecl x.getId (typeToType T_expr) BinderInfo.implicit fun x_var => do
      -- Elaborate the body of the lambda under the binding
      let b_expr ← elaborateTerm b none
      -- Construct the lambda expression
      return mkLambda x.getId T_expr b_expr
  -/
  | _ =>
    throwError "Unsupported term syntax: {stx}"

-- Function to elaborate a Lean term into an Ast.Prop (incomplete)
unsafe def elaborateProp (stx : Syntax) : MetaM Prop := do
    --  This is the *core* of the problem.  We need to convert a Lean
    --  term (which represents a logical proposition) into a Lean `Prop`.
    --  This is generally *impossible* to do automatically in full generality,
    --  because Lean's term language is much richer than the language of
    --  propositions.  However, for a *restricted* subset of Lean terms,
    --  we can do it.
    --
    --  Here's a very basic starting point.  You will need to extend this
    --  significantly to handle the kinds of propositions that you expect
    --  to see in your Loda programs.
    match stx with
    | `(term| $b:term && $c:term) => do
      let bProp ← elaborateProp b
      let cProp ← elaborateProp c
      pure (bProp ∧ cProp)
    | `(term| $b:term || $c:term) => do
      let bProp ← elaborateProp b
      let cProp ← elaborateProp c
      pure (bProp ∨ cProp)
    | `(term| ! $b:term) => do
      let bProp ← elaborateProp b
      pure (¬bProp)
    | `(term| $x:term = $y:term) => do
      let xVal ← elaborateTerm x none
      let yVal ← elaborateTerm y none
      pure (xVal = yVal)  --  VERY simplified.  Assumes decidable equality.
    | `(term| $p:ident) => do
        -- Try to resolve the identifier as a proposition
        let pExpr ←  elaborateTerm p none
        -- Check if the type of pExpr is Prop
        let pType ← inferType pExpr
        if pType == mkSort levelZero then
          -- If it is a Prop, return it.
          return True
        else
          -- Otherwise, it's not a proposition.
          throwError "Expected a proposition, but got {p} of type {pType}"
    | `(term| True) =>  pure True
    | `(term| False) => pure False
    /-
    | `(term| forall $x:ident : $T:term, $p:term) => do
        let T_expr ← elaborateType T
        -- Introduce a bound variable with the specified type
        withLocalDecl x.getId (typeToType T_expr) BinderInfo.implicit fun x_var => do
          -- Elaborate the body of the forall under the binding
          let p_prop ← elaborateProp p
          -- Construct the forall proposition
          pure (forall x_var, p_prop)
    | `(term| exists $x:ident : $T:term, $p:term) => do
        let T_expr ← elaborateType T
        -- Introduce a bound variable with the specified type
        withLocalDecl x.getId (typeToType T_expr) BinderInfo.implicit fun x_var => do
          -- Elaborate the body of the exists under the binding
          let p_prop ← elaborateProp p
          -- Construct the exists proposition
          pure (Exists fun x_var => p_prop)
    -/
    | _ =>
      --  This is the catch-all case.  For a real compiler, you would
      --  either:
      --    1.  Handle more cases (e.g., function application, etc.)
      --    2.  Restrict the allowed syntax for propositions in Loda (and
      --        give a good error message here).
      --    3.  Use Lean's metaprogramming facilities to try to *prove*
      --        the proposition (this is very advanced, and might not
      --        always be possible).
      --    4.  Represent the proposition in your AST as an uninterpreted
      --        term, and handle it later in your compiler pipeline.
      throwError "Unsupported proposition syntax: {stx}"

unsafe def elaborateType (stx : Syntax) : MetaM Ast.Ty := do
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

unsafe def elaborateExpr (stx : Syntax) : MetaM Ast.Expr := do
  match stx with
  -- Numeric literal: match on a numeric literal syntax
  /-
  | `(term| $n) =>
    if let some num := n.isNatLit? then
      pure (Expr.constInt (Int.ofNat num))
    else
      throwError "Invalid number literal"
  -/

  -- Identifier variable
  | `(term| $x:ident) =>
    pure (Ast.Expr.var x.getId.toString)

  -- Wildcard `_`
  | `(term| _) =>
    pure Ast.Expr.wildcard

  -- Assertion: match any ident, then check if 'assert'
  | `(term| `assert $e1:term = $e2:term) => do
    let e1Ast ← elaborateExpr e1
    let e2Ast ← elaborateExpr e2
    pure (Ast.Expr.assertE e1Ast e2Ast)

  -- Circuit call prefixed by `#`
  /-
  | `(term| "#" $c:ident $args*) => do
    let cName := c.getId.toString
    let argsAst ← args.mapM elaborateExpr
    pure (Ast.Expr.circRef cName argsAst)
  -/

  -- Array indexing: arr[idx]
  /-
  | `(term| $arr:term [ $idx:term ]) => do
    let arrAst ← elaborateExpr arr
    let idxAst ← elaborateExpr idx
    pure (Expr.mkApp (Expr.mkProj ``Array.get 0 arrAst) #[idxAst])
  -/

  -- Lambda abstraction: \x. body
  | `(term| "\\" $x:ident ":" $ty "=>" $body) => do
    let tyAst ← elaborateType ty
    let bodyAst ← elaborateExpr body
    pure (Ast.Expr.lam x.getId.toString tyAst bodyAst)

  -- Let-binding: let x = val in body
  /-
  | `(term| let $x:ident := $val; $body) => do
    let valAst ← elaborateExpr val
    let bodyAst ← elaborateExpr body
    pure (Expr.letE x.getId.toString valAst bodyAst)
  -/

  -- Iteration: iter init cond (step) (body) inv:(inv)
  /-
  | `(term| `iter $init $cond ($step) ($body) `inv:( $inv ) ) => do
    let initAst ← elaborateExpr init
    let condAst ← elaborateExpr cond
    let stepAst ← elaborateExpr step
    let bodyAst ← elaborateExpr body
    let invAst  ← elaborateProp inv
    pure (Expr.mkIter initAst condAst stepAst bodyAst invAst)
  -/

  -- Unary negation
  /-
  | `(term| - $e) => do
    let eAst ← elaborateExpr e
    pure (Expr.unOp "-" eAst)
  -/

  -- Binary operations
  | `(term| $e1 + $e2) => do
    let e1Ast ← elaborateExpr e1; let e2Ast ← elaborateExpr e2
    pure (Ast.Expr.fieldExpr e1Ast Ast.FieldOp.add e2Ast)
  /-
  | `(term| $e1 - $e2) => do
    let e1Ast ← elaborateExpr e1; let e2Ast ← elaborateExpr e2
    pure (Expr.binOp "-" e1Ast e2Ast)
  | `(term| $e1 * $e2) => do
    let e1Ast ← elaborateExpr e1; let e2Ast ← elaborateExpr e2
    pure (Expr.binOp "*" e1Ast e2Ast)
  | `(term| $e1 / $e2) => do
    let e1Ast ← elaborateExpr e1; let e2Ast ← elaborateExpr e2
    pure (Expr.binOp "/" e1Ast e2Ast)
  | `(term| $e1 % $e2) => do
    let e1Ast ← elaborateExpr e1; let e2Ast ← elaborateExpr e2
    pure (Expr.binOp "%" e1Ast e2Ast)
  -/

  -- Tuple: (e1, e2, ...)
  /-
  | `(term| ( $`[$es:term`],* )) => do
    let esAst ← es.getElems.mapM elaborateExpr
    pure (Expr.mkAppN (Expr.const ``Prod.mk []) esAst)
  -/

  /-
  -- Field projection: e.f
  | `(term| $e:term . $f:ident) => do
    let eAst ← elaborateExpr e
    pure (Expr.app (Expr.mkProj (← getConstName f.getId) 1) #[eAst])

  -- Cast: e : ty
  | `(term| $e:term ":" $ty:term) => do
    let eAst  ← elaborateExpr e
    let tyAst ← elaborateType ty
    pure (Expr.cast eAst tyAst)
  -/

  | _ => throwError "Unsupported expression syntax: {stx}"

-- Elaborate a single parameter: `(param| x : T)
unsafe def elaborateParam (stx : Syntax) : MetaM (String × Ast.Ty) := do
  match stx with
  | `(term| $x:ident ":" $ty:term) => do
    let tyAst ← elaborateType ty
    pure (x.getId.toString, tyAst)
  | _ =>
    throwError "Unsupported parameter syntax: {stx}, expected `x : T`"

unsafe def elaborateCircuit (stx : Syntax) : MetaM Ast.Circuit := do
  match stx with
  | `(loda_circuit| circuit $name:ident ($params:loda_param,*) -> $retTy:loda_ty {$body:loda_expr}) => do
    let nameStr := name.getId.toString
    let paramsList ← params.getElems.mapM elaborateParam
    let retTyAst ← elaborateType retTy
    let bodyAst ← elaborateExpr body
    pure { name := nameStr, inputs := paramsList.toList, output := retTyAst, body := bodyAst }
  | _ => throwError "Invalid circuit syntax"

/-
@[command_elab "loda_circuit"] def elabCodaCircuit : CommandElab
  | `(loda_circuit $circ) => do
    let ast ← elaborateCircuit circ
    -- Register the circuit in an environment
    addCodaCircuit ast
    -- You might also want to output the circuit definition
    pure ()
-/
