import Init.Prelude
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic  -- for `Nat.Prime`
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

instance (p : ℕ) : Lean.ToExpr (F p) where
  toExpr x :=
    let fpType := Lean.mkApp (Lean.mkConst ``F) (Lean.toExpr p)
    let natVal := Lean.toExpr x.val
    Lean.mkApp3 (Lean.mkConst ``OfNat.ofNat) fpType natVal
      (Lean.mkApp (Lean.mkConst ``instOfNat) natVal)
  toTypeExpr := Lean.mkApp (Lean.mkConst ``F) (Lean.toExpr p)
