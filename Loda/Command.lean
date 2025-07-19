import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Loda.Frontend

open Lean Parser
open Lean Meta

syntax (name := loda_register) "#loda_register" loda_circuit : command
syntax (name := loda_check) "#loda_check" ident : command
syntax (name := loda_prove) "#loda_prove" ident ":=" "by" tacticSeq: command

builtin_initialize tempCircuitRef : IO.Ref (Option Ast.Circuit) ← IO.mkRef none

@[command_elab loda_register]
unsafe def elabLodaCircuitRegister : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(command| #loda_register $circ:loda_circuit) =>
      Elab.Command.runTermElabM fun _ => do
        let ast ← Frontend.elaborateCircuit circ
        logInfo m!"Successfully elaborated circuit {repr ast}"
        Env.addCircuitToEnv ast.name ast
        logInfo m!"Successfully registered circuit '{ast.name}'."
  | _ => Elab.throwUnsupportedSyntax

@[command_elab loda_check]
unsafe def elabLodaCircuitCheck : Elab.Command.CommandElab
  | `(command| #loda_check $cName:ident) => do
    let Δ ← Elab.Command.liftCoreM Env.getCircuitEnv
    let circ := Env.lookupCircuit Δ cName.getId.toString
    logInfo m!"{repr circ}"
  | _ => Elab.throwUnsupportedSyntax

@[command_elab loda_prove]
unsafe def elabLodaProve : Elab.Command.CommandElab
  | `(command| #loda_prove $cName:ident := by $proof:tacticSeq) => do
    -- Get the circuit from environment
    let Δ ← Elab.Command.liftCoreM Env.getCircuitEnv
    let circ := Env.lookupCircuit Δ cName.getId.toString

    let circExpr := toExpr circ
    let deltaExpr := toExpr Δ

    let circTerm ← Elab.Command.liftTermElabM $ PrettyPrinter.delab circExpr
    let deltaTerm ← Elab.Command.liftTermElabM $ PrettyPrinter.delab deltaExpr

    -- Generate theorem name
    let theoremName := cName.getId.toString ++ "_correct"
    let theoremIdent := mkIdent (Name.mkSimple theoremName)

    -- Generate the theorem syntax
    let theoremStx ← `(command|
      theorem $theoremIdent (Δ: Env.CircuitEnv) (h_delta: Δ = $deltaTerm) : (Ty.circuitCorrect $deltaTerm $circTerm) := by
        (unfold Ty.circuitCorrect; simp_all; intro x hs hσ; set envs := Ty.makeEnvs $circTerm x);
        (set σ := envs.1); (set Γ := envs.2); ($proof);
    )
    logInfo m!"Proof state opened for '{theoremName}' - continue with tactics!"
    -- Elaborate the generated theorem command
    Elab.Command.elabCommand theoremStx
  | _ => Elab.throwUnsupportedSyntax
