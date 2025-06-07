import Loda.Parser.Frontend
import Loda.Env
import Loda.Ast
import Loda.Typing

open Ast
open Frontend
open Env

#loda_check circuit Adder(x : Int, y : Int) -> Int {x + y}
#loda_register circuit Adder(x : Int, y : Int) -> Int {x + y}
#loda_eval Adder x=2 y=12
