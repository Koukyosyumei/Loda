import Loda.Ast
import Std.Data.HashMap.Basic
import Lean.Environment
import Lean

/-!
  # Environments for Loda

  This module provides:
  1. A **valuation environment** mapping variable names to runtime values.
  2. A **circuit environment** mapping circuit names to their declarations.
  3. A **type environment** mapping variable names to Loda types.
-/
namespace Env

/-- A valuation environment: maps variable names to runtime `Value`s. -/
abbrev ValEnv := String -> Ast.Value

/--
  Extend `σ` by binding `ident` to `val`.
  When you lookup `ident`, you get `val`; otherwise you delegate to the old `σ`.
-/
@[inline]
def updateVal (σ: ValEnv) (ident: String) (val: Ast.Value) : ValEnv :=
  fun y => if y = ident then val else σ y

/-- A circuit environment: maps circuit names to their `Circuit`. -/
abbrev CircuitEnv := Std.HashMap String Ast.Circuit

/--
  Extend `δ` by binding `ident` to `circuit`.
  When you lookup `ident`, you get `circuit`; otherwise you delegate to the old `δ`.
-/
@[inline]
def updateCircuit (Δ: CircuitEnv) (ident: String) (circuit: Ast.Circuit) : CircuitEnv :=
  Δ.insert ident circuit

abbrev CircuitEntry := String × Ast.Circuit

initialize circuitExt : Lean.SimplePersistentEnvExtension CircuitEntry CircuitEnv ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun as => (Std.HashMap.emptyWithCapacity),
    addEntryFn := fun m (name, circuit) => m.insert name circuit,
    toArrayFn := fun m => m.toArray
  }

def addCircuitToEnv (name : String) (circuit : Ast.Circuit) : Lean.CoreM Unit := do
  Lean.modifyEnv (circuitExt.addEntry · (name, circuit))

def getCircuitEnv : Lean.CoreM CircuitEnv := do
  let env ← Lean.getEnv
  return circuitExt.getState env

def getCircuitFromEnv (name : String) : Lean.CoreM (Option Ast.Circuit) := do
  let env ← Lean.getEnv
  return (circuitExt.getState env).get? name

/-- A type environment: maps variable names to Loda `Ty`s. -/
def TyEnv := String -> Ast.Ty

/--
  Extend `Γ` by binding `ident` to `τ`.
  When you lookup `ident`, you get `τ`; otherwise you delegate to the old `Γ`.
-/
@[inline]
def updateTy (Γ: TyEnv) (ident: String) (τ: Ast.Ty) : TyEnv :=
  fun y => if y = ident then τ else Γ y

end Env
