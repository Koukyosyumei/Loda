import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic  -- for `Nat.Prime`
import Init.Prelude
import Mathlib.Tactic.NormNum.Core

/-!
# Finite field Fp implementation in Lean4

This file defines a prime field `Fp p` for a given prime `p`, along with
addition, multiplication, negation, inversion (via Fermat's little theorem),
and exponentiation.
-/

/-- `Fp p` is the prime field of order `p`, assuming `p` is prime. -/
abbrev F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p
instance (p : ℕ) [Fact p.Prime] : Repr (F p) where
  reprPrec x _ := "F" ++ toString p ++ ".mk " ++ toString x.val

def a : F 5 := 2
def b : F 5 := 3

#eval (a * b)                 -- Expected: 1
#eval ((2 : F 5) + (3 : F 5)) -- Expected 0
#eval (a^2)
#eval (a^3)
#eval (a^4)
#eval (a * b.inv)
