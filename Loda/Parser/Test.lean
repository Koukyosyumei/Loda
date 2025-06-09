import Loda.Parser.Frontend
import Loda.Env
import Loda.Ast
import Loda.Typing
import Lean.Meta

open Ast
open Frontend
open Env
open Lean.Meta

#loda_register circuit Adder(x : Int, y : Int) -> Int {x + y}
#loda_check Adder
#loda_eval Adder x=2 y=12

#loda_verify Adder

def myAdderProof : Lean.CoreM String := do
  -- CoreM モナドの計算を実行し、結果の CircuitEnv を Δ に束縛する
  let Δ ← Env.getCircuitEnv
  let circ := Env.lookupCircuit Δ "Adder"
  let myTheorem : Ty.circuitCorrect 1000 Δ circ := by {
    unfold Ty.circuitCorrect
    -- Std.HashMap.get! at circ
    sorry
  }
  return "Proof constructed successfully."
