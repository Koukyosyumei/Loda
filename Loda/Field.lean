import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic  -- for `Nat.Prime`
import Init.Prelude

/-!
# Finite field Fp implementation in Lean4

This file defines a prime field `Fp p` for a given prime `p`, along with
addition, multiplication, negation, inversion (via Fermat's little theorem),
and exponentiation.
-/

/-- `Fp p` is the prime field of order `p`, assuming `p` is prime. -/
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p
instance (p : ℕ) [Fact p.Prime] : Repr (F p) where
  reprPrec x _ := "F" ++ toString p ++ ".mk " ++ toString x.val

variable {p : ℕ} [Fact p.Prime]

/-- Coercion from `Fin p` to `Fp p`. -/
instance : Coe (Fin p) (F p) where
  coe x := x

/-- Zero element of `Fp p`. -/
def zero : F p := 0
instance : Zero (F p) where
  zero := zero

/-- One element of `Fp p`. -/
def one: F p := 1
instance : One (F p) where
  one := one

/-- Addition in `Fp p`. -/
def add (a b : F p) : F p := (a.val + b.val) % p
instance : Add (F p) where
  add := add

/-- Negation in `Fp p`. -/
def neg (a : F p) : F p := (p - a.val) % p
instance : Neg (F p) where
  neg := neg

/-- Multiplication in `Fp p`. -/
def mul (a b : F p) : F p := (a.val * b.val) % p
instance : Mul (F p) where
  mul := mul

/-- Exponentiation by natural number in `Fp p`. -/
instance : Pow (F p) ℕ where
  pow a n := a ^ n  -- this just defers to ZMod's own `^`

/-- Inverse in `Fp p` using Fermat's little theorem (`a^(p-2)`). -/
instance : Inv (F p) where
  inv a := a ^ (p - 2)

-- First, correctly implement division in Fp
instance : Div (F p) where
  div a b := a * (b ^ (p - 2))

-- Then implement HDiv with the correct signature
instance : HDiv (F p) (F p) (F p) where
  hDiv := fun a b => a * (b ^ (p - 2))

def a : F 5 := 2
def b : F 5 := 3

set_option diagnostics true

#eval (a * b)                 -- Expected: 1
#eval ((2 : F 5) + (3 : F 5)) -- Expected 0
#eval (a^2)
#eval (a^3)
#eval (a^4)
--#eval (a * (b ^ (5 - 2)))
