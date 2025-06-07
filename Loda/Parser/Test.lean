import Loda.Parser.Frontend
import Loda.Env
import Loda.Ast
import Loda.Typing

open Ast
open Frontend
open Env

#loda_load circuit Adder(x : Int, y : Int) -> Int {x + y}


#check Env.circuitEnvRef

#eval do
  let adder : Ast.Circuit := {
    name   := "Adder",
    inputs := ("x", Ast.Ty.int),
    output := ("output", Ast.Ty.int),
    body   := (Ast.Expr.var "x")
  }
  --let σ := Env.circuitEnvRef
  --σ.modify (fun env => env.insert "Adder" adder)

  --Env.getCircuitEnv

  --Env.registerCircuit "adder" adder

--#eval Env.registerCircuit "add" Adder

--#eval Env.registerCircuit "adder" Adder

--Env.registerCircuit "adder" Adder
