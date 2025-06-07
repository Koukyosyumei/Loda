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

builtin_initialize circuitExt : Lean.SimpleScopedEnvExtension CircuitEntry CircuitEnv ←
  Lean.registerSimpleScopedEnvExtension {
    name         := `circuits
    addEntry     := fun map (name, circuit) => map.insert name circuit
    initial      := {}
  }

builtin_initialize circuitEnvRef : IO.Ref CircuitEnv ← IO.mkRef {}
builtin_initialize lastCircuitRef: IO.Ref (Option Ast.Circuit) ← IO.mkRef none

/-- Get the current circuit env. -/
def getCircuitEnv : IO CircuitEnv := circuitEnvRef.get

/-- Register a new circuit. -/
def registerCircuit (name : String) (c : Ast.Circuit) : IO Unit :=
  circuitEnvRef.modify (fun env => env.insert name c)

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
