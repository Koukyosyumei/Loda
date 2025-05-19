import Loda.Ast
import Loda.Circuit

namespace Env

/-- Valuation (environment). -/
def ValEnv := String -> Ast.Value

def setVal (σ: ValEnv) (x : String) (v: Ast.Value) : ValEnv :=
  fun y => if y = x then v else σ y

/-- Global circuit definitions; populate this map with your circuits. -/
def CircuitEnv := String -> Circuit.Circuit

def setCircuit (δ : CircuitEnv) (x : String) (v: Circuit.Circuit) : CircuitEnv :=
  fun y => if y = x then v else δ y

/-- Type Environment. -/
def TyEnv := String -> Ast.Ty

def setTy (Γ : TyEnv) (x : String) (v: Ast.Ty) : TyEnv :=
  fun y => if y = x then v else Γ y

end Env
