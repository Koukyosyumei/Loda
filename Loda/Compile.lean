import Loda.Ast
import Loda.Typing

/-- Compilation values representing partially evaluated expressions. -/
inductive CompValue where
  | constF      : ∀ p, F p → CompValue                             -- field constant
  | constInt    : Int → CompValue                                  -- integer constant
  | constBool   : Bool → CompValue                                 -- boolean constant
  | prodValue   : List CompValue → CompValue                       -- (u₁, ..., uₙ)
  | arrValue    : List CompValue → CompValue                       -- array value
  | closure     : String → Expr → (String → CompValue) → CompValue -- Closure(λx : τ. e, σ)
  | r1csVar     : Nat → CompValue                                  -- R1CS variable r
  | binOp       : CompValue → CompValue → CompValue                -- Irreducible expression (u₁ ⊗ u₂)
  | unit        : CompValue                                        -- unit value

/-- Valuation environment mapping variables to compilation values. -/
def CompEnv := String → CompValue

/-- Set a variable in the valudation environment. -/
def setCompValue (σ: CompEnv) (x: String) (v: CompValue) : CompEnv :=
  fun y => if y = x then v else σ y

/-- R1CS constraint in the form A * B + C = 0. -/
structure R1CSConstraint where
  A : CompValue
  B : CompValue
  C : CompValue

/-- Compilation state tracking fresh variables and constraints. -/
structure CompState where
  nextVar : Nat                     -- Counter for fresh variables
  constraints : List R1CSConstraint -- Generated constraints
deriving Nonempty

/-- Empty compilation state. -/
def emptyState : CompState := { nextVar := 0, constraints := [] }

/-- Generate a fresh R1CS variable. -/
def freshVar (s: CompState) : (CompState × CompValue) :=
  let varId := s.nextVar
  let var := CompValue.r1csVar varId
  let s' := { s with nextVar := varId + 1 }
  (s', var)

/-- Add a constraint to the compilation state. -/
def addConstraint (s: CompState) (c: R1CSConstraint) : CompState :=
  { s with constraints := c :: s.constraints }

/-- Check if a CompValue is a field constant. -/
def isField : CompValue → Bool
  | CompValue.constF _ _ => true
  | _ => false

/-- Evaluate a binary field operation if both operands are constants. -/
def evalFieldBinOp (u₁: CompValue) (op: FieldOp) (u₂: CompValue) : Option CompValue :=
  match u₁, op, u₂ with
  | CompValue.constF p v₁, FieldOp.add, CompValue.constF _ v₂ => some (CompValue.constF p ((v₁.val + v₂.val) % p))
  | CompValue.constF p v₁, FieldOp.sub, CompValue.constF _ v₂ => some (CompValue.constF p ((v₁.val - v₂.val) % p))
  | CompValue.constF p v₁, FieldOp.mul, CompValue.constF _ v₂ => some (CompValue.constF p ((v₁.val * v₂.val) % p))
  | _, _, _ => none

/-- Create an equality constraint (u₁ = u₂) as an R1CS constraint. -/
def mkEqualityConstraint (u₁: CompValue) (u₂: CompValue) : R1CSConstraint :=
  -- Equality u₁ = u₂ becomes u₁ - u₂ = 0, or 1*u₁ + (-1)*u₂ + 0 = 0
  {
    A := CompValue.constInt 1,
    B := u₁,
    C := CompValue.binOp (CompValue.constInt (-1)) u₂
  }


/-- Create constraint for function application. -/
def mkApplicationConstraint (fn: CompValue) (arg: CompValue) (result: CompValue) : R1CSConstraint :=
  -- In a real implementation, this would create constraints
  -- that enforce the relationship: result = fn(arg)
  {
    A := fn,
    B := arg,
    C := CompValue.binOp (CompValue.constInt (-1)) result
  }

/-- Create constraint connecting circuit inputs to outputs. -/
def mkConnectionConstraint (input: CompValue) (output: CompValue) : R1CSConstraint :=
  -- Simplified constraint that represents some relationship between input and output
  {
    A := CompValue.constInt 1,
    B := input,
    C := CompValue.binOp (CompValue.constInt (-1)) output
  }

/-- Compile an expression to R1CS constraints and a compilation value. -/
unsafe def compile (σ: CompEnv) (δ: CircuitEnv) (s: CompState) (e: Expr) : (CompState × CompValue) :=
  match e with
  -- C-VALUE (constants) just return the value with no constraints
  | Expr.constF p v => (s, CompValue.constF p v)
  | Expr.constInt i => (s, CompValue.constInt i)
  | Expr.constBool b => (s, CompValue.constBool b)

  -- C-VAR (variables) lookup in the environment
  | Expr.var x => (s, σ x)

  -- C-NONDET (wildcard) generates a fresh R1CS variable
  | Expr.wildcard => freshVar s

  -- C-ASSERT (assert e₁ = e₂) adds an equality constraint
  | Expr.assertE e₁ e₂ =>
      let (s₁, u₁) := compile σ δ s e₁
      let (s₂, u₂) := compile σ δ s₁ e₂
      let constraint := mkEqualityConstraint u₁ u₂
      let s₃ := addConstraint s₂ constraint
      (s₃, CompValue.unit)

  -- C-RED and C-IRRED for field operations
  | Expr.fieldExpr e₁ op e₂ =>
      let (s₁, u₁) := compile σ δ s e₁
      let (s₂, u₂) := compile σ δ s₁ e₂
      -- C-RED: If both operands are field constants, try to reduce
      if isField u₁ && isField u₂ then
        match evalFieldBinOp u₁ op u₂ with
        | some result => (s₂, result)
        | none => (s₂, CompValue.binOp u₁ u₂)
      -- C-IRRED: Otherwise, create an irreducible expression
      else
        (s₂, CompValue.binOp u₁ u₂)

  -- Lambda abstraction
  | Expr.lam x τ body =>
      (s, CompValue.closure x body σ)

  -- Function application
  | Expr.app e₁ e₂ =>
      let (s₁, u₁) := compile σ δ s e₁
      let (s₂, u₂) := compile σ δ s₁ e₂
      match u₁ with
      | CompValue.closure x body σ' =>
          let σ'' := setCompValue σ' x u₂
          compile σ'' δ s₂ body
      | _ => (s₂, CompValue.unit) -- Error case

  -- Let binding
  | Expr.letIn x e₁ e₂ =>
      let (s₁, u₁) := compile σ δ s e₁
      let σ' := setCompValue σ x u₁
      compile σ' δ s₁ e₂

  -- Product construction
  | Expr.prodCons es =>
      let folder := fun (acc : CompState × List CompValue) e =>
        let (s', vs) := acc
        let (s'', v) := compile σ δ s' e
        (s'', vs ++ [v])
      let (s', vs) := List.foldl folder (s, []) es
      (s', CompValue.prodValue vs)

  -- Array construction
  | Expr.arrCons h t =>
      let (s₁, u₁) := compile σ δ s h
      let (s₂, u₂) := compile σ δ s₁ t
      match u₂ with
      | CompValue.arrValue vs => (s₂, CompValue.arrValue (u₁ :: vs))
      | _ => (s₂, CompValue.arrValue [u₁]) -- Assume empty array if not an array

  -- Iterator (would need to be unrolled during compilation)
  | Expr.iter idx start ed step acc =>
      -- Compile start and end expressions
      let (s₁, startVal) := compile σ δ s start
      let (s₂, endVal) := compile σ δ s₁ ed

      -- Extract concrete integer values (needed for unrolling)
      match startVal, endVal with
      | CompValue.constInt startInt, CompValue.constInt endInt =>
          -- Initialize result with accumulator value
          let (s₃, accVal) := compile σ δ s₂ acc

          -- Recursively unroll the loop from startInt to endInt-1
          let rec unroll (i: Int) (state: CompState) (accValue: CompValue) : (CompState × CompValue) :=
              if i >= endInt then
                  (state, accValue)  -- Base case: return final accumulator
              else
                  let (state', stepVal) := compile σ δ state step
                  -- Compile step function application to current index and accumulator
                  match stepVal with
                  | CompValue.closure idx_var body σ' =>
                      -- Bind index variable to current value i
                      let σ_idx := setCompValue σ' idx_var (CompValue.constInt i)
                      let (state'', stepFn) := compile σ_idx δ state body

                      -- Evaluate to get function from accumulator to next value
                      match stepFn with
                        | CompValue.closure acc_var innerBody σ'' =>
                            -- Bind accumulator variable
                            let σ_acc := setCompValue σ'' acc_var accValue
                            -- Compute next accumulator value
                            let (state''', newAccVal) := compile σ_acc δ state'' innerBody
                            -- Continue unrolling with updated accumulator
                            unroll (i+1) state''' newAccVal
                        | _ => (state'', CompValue.unit) -- Error: not a function
                  | _ =>
                      -- Directly apply step to index and accumulator if not a closure
                      let (state', fnVal) := compile σ δ state step
                      let idxVal := CompValue.constInt i
                      -- Create application constraints
                      let (state'', appVal) :=
                          match fnVal with
                          | CompValue.closure _ _ _ =>
                              -- First apply to index
                              let (s1, r1) := freshVar state'
                              let c1 := mkApplicationConstraint fnVal idxVal r1
                              let s2 := addConstraint s1 c1
                              -- Then apply to accumulator
                              let (s3, r2) := freshVar s2
                              let c2 := mkApplicationConstraint r1 accValue r2
                              let s4 := addConstraint s3 c2
                              (s4, r2)
                          | _ => (state', CompValue.unit) -- Error case
                      unroll (i+1) state'' appVal

          -- Start unrolling with initial accumulator
          unroll startInt s₃ accVal

      | _, _ =>
          -- If bounds aren't constant integers, create a fresh variable
          -- and add constraints that would represent the loop semantics
          let (s₃, resultVar) := freshVar s₂
          (s₃, resultVar)

  -- Circuit reference
  | Expr.circRef name args =>
      -- Compile all arguments
      let compileArgs := fun (acc : CompState × List CompValue) arg =>
          let (state, values) := acc
          let (state', value) := compile σ δ state arg
          (state', values ++ [value])
      let (s', argVals) := List.foldl compileArgs (s, []) args

      -- 1. Look up the circuit from a global environment
      let circuit := δ name

      -- 2. Create fresh variables for circuit inputs
      let genInputVars := fun (acc : CompState × List (String × CompValue)) (input : String × Ty) =>
          let (state, vars) := acc
          let (state', v) := freshVar state
          (state', vars ++ [(input.fst, v)])
      let (stateWithInputs, inputVars) := List.foldl genInputVars (s', []) circuit.inputs

      -- 3. Create symbolic environment mapping input names to fresh variables
      let σCircuit := List.foldl (fun env (x, v) => setCompValue env x v) σ inputVars
      -- Add constraints binding argument values to input variables
      let addInputConstraints := fun (state : CompState) (idx : Nat) =>
          match inputVars[idx]?, argVals[idx]? with
          | some (inputName, inputVar), some argVal => addConstraint state (mkEqualityConstraint inputVar argVal)
          | _, _ => state
      let stateWithBindings := List.range (min inputVars.length argVals.length)
                              |>.foldl addInputConstraints stateWithInputs

      -- 4. Compile the circuit body with the new symbolic environment
      let (stateWithBody, bodyValue) := compile σCircuit δ stateWithBindings circuit.body

      -- 5. Create fresh variable for the circuit output and bind the body result to it
      let (stateWithOutput, outputVar) := freshVar stateWithBody
      let outputConstraint := mkEqualityConstraint outputVar bodyValue
      let finalState := addConstraint stateWithOutput outputConstraint

      (finalState, outputVar)

  -- Default for other expressions
  | _ => (s, CompValue.unit)
