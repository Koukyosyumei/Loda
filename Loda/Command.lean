import Lean.Meta
import Lean.Elab.Command
import Lean.Parser
import Lean.Elab

import Loda.Frontend

open Lean Parser
open Lean Meta

syntax (name := loda_register) "#loda_register" loda_circuit : command

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

syntax (name := loda_check) "#loda_check" ident : command

@[command_elab loda_check]
unsafe def elabLodaCircuitCheck : Elab.Command.CommandElab
  | `(command| #loda_check $cName:ident) => do
    let Δ ← Elab.Command.liftCoreM Env.getCircuitEnv
    let circ := Env.lookupCircuit Δ cName.getId.toString
    logInfo m!"Successfully elaborated circuit {repr circ}"
  | _ => Elab.throwUnsupportedSyntax

syntax (name := loda_eval) "#loda_eval" ident (ident "=" loda_expr)* : command

@[command_elab loda_eval]
unsafe def elabLodaEval : Elab.Command.CommandElab
  | `(command| #loda_eval $cName:ident $[$xs:ident = $ts:loda_expr]*) => do
    -- 1) Lookup the AST.Circuit by name in your Env.CircuitEnv
    let Δ ← Elab.Command.liftCoreM Env.getCircuitEnv
    let circ := Env.lookupCircuit Δ cName.getId.toString
    -- 2) Build a ValEnv from the `x=5 y=7 …`
    let σ₁ ← (xs.zip ts).foldlM (init := []) fun env (x, t) => do
        let e ← Elab.Command.liftTermElabM <| Frontend.elaborateExpr t.raw
        let vOpt := Eval.eval 1000 env Δ e
        match vOpt with
        | some v => pure <| Env.updateVal env x.getId.toString v
        | none   => pure <| Env.updateVal env x.getId.toString Ast.Value.vStar
    -- 3) Evaluate
    let res := Eval.eval 1000 σ₁ Δ circ.body
    match res with
    | some output => logInfo m!"→ {repr output}"
    | _ => Elab.throwUnsupportedSyntax
  | _ => Elab.throwUnsupportedSyntax

syntax (name := loda_prove) "#loda_prove" ident ":=" "by" tacticSeq: command


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
      theorem $theoremIdent : (Ty.circuitCorrect 1000 $deltaTerm $circTerm) := by $proof
    )
    logInfo m!"Proof state opened for '{theoremName}' - continue with tactics!"
    -- Elaborate the generated theorem command
    Elab.Command.elabCommand theoremStx
  | _ => Elab.throwUnsupportedSyntax
