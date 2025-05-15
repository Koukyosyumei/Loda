import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

namespace AST

variable {p : ℕ} [p_prime: Fact p.Prime]

inductive FieldOp where
  | add : FieldOp     -- Addition (+)
  | sub : FieldOp     -- Subtraction (-)
  | mul : FieldOp     -- Multiplication (*)
  | div : FieldOp     -- Division (/)
  | eq : FieldOp      -- Equality (=)
  deriving Inhabited, BEq

inductive BoolOp where
  | and : BoolOp      -- Conjunction (∧)
  | or : BoolOp       -- Disjunction (∨)
  | not : BoolOp      -- Negation (¬)
  | eq : BoolOp       -- Equality (=)
  deriving Inhabited, BEq

inductive IntOp where
  | add : IntOp       -- Addition (+z)
  | sub : IntOp       -- Subtraction (-z)
  | mul : IntOp       -- Multiplication (*z)
  | lt : IntOp        -- Less than (<)
  | leq : IntOp       -- Less than or equal (≤)
  | eq : IntOp        -- Equality (=)
  deriving Inhabited, BEq

inductive Expr  where
  | constField : (F p) → Expr
  | constBool : Bool → Expr
  | constInt : Int → Expr
  | var : String → Expr
  | wildcard : Expr  -- The '*' non-deterministic choice
  | assert : Expr → Expr → Expr
  | binOpField : FieldOp → Expr → Expr → Expr
  | binOpBool : BoolOp → Expr → Expr → Expr
  | binOpInt : IntOp → Expr → Expr → Expr
  | circuitRef : String → List Expr → Expr
  | tuple : List Expr → Expr
  | lambda : String → Type → Expr → Expr
  | app : Expr → Expr → Expr
  | let_ : String → Expr → Expr → Expr
  | iter : String → Type → Expr → Expr → Expr → Expr → Expr
  | arrayIndex : Expr → Expr → Expr
  | arrayConstructor : Expr → Expr → Expr
  | mapArray : Expr → Expr → Expr
  deriving Inhabited

inductive RType where
  | field : RType
  | int : RType
  | bool : RType
  | product : List RType → RType
  | array : RType → RType
  | refinement : String → RType → Expr → RType
  | functionType : String → RType → RType → RType
  deriving Inhabited

-- Type Environment manages type definitions and constraints
structure TypeEnvironment where
  -- Maps type names to their definitions
  typeDefinitions : String → RType
  -- Maps type variables to their bounds
  typeVars : String → RType
  -- Maps refinement variables to their types
  refinementVars : String → RType
  deriving Inhabited

def TypeEnvironment.lookupType (Δ : TypeEnvironment) (name : String) : RType :=
  Δ.typeDefinitions name

def TypeEnvironment.lookupTypeVar (Δ : TypeEnvironment) (name : String) : RType :=
  Δ.typeVars name

def TypeEnvironment.lookupRefinementVar (Δ : TypeEnvironment) (name : String) : RType :=
  Δ.refinementVars name




/-
structure Circuit where
  name : String
  inputs : List (String × RType)
  outputType : RType
  body : Expr
-/

end AST
