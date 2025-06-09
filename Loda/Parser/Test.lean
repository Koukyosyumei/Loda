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

#loda_prove Adder := by {
  unfold Ty.circuitCorrect
  sorry
}

#print Adder_correct
