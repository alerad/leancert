/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.QProduct.Finite

/-!
# Boolean certificates for finite q-product integrals

The checker is exact rational arithmetic.  The golden theorem lifts a successful
boolean check to a semantic interval enclosure for the real integral.
-/

namespace LeanCert.QProduct

/-- Exact finite q-product interval checker. -/
def checkFiniteIntegralInterval (S : Finset Nat) (lo hi : ℚ) : Bool :=
  decide (lo ≤ finiteIntegralRat S) && decide (finiteIntegralRat S ≤ hi)

/-- Golden theorem for exact finite q-product interval certificates. -/
theorem verify_finiteIntegral_interval (S : Finset Nat) (lo hi : ℚ)
    (hcheck : checkFiniteIntegralInterval S lo hi = true) :
    (lo : ℝ) ≤ F S ∧ F S ≤ (hi : ℝ) := by
  simp only [checkFiniteIntegralInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rw [← finiteIntegralRat_correct]
  exact ⟨by exact_mod_cast hcheck.1, by exact_mod_cast hcheck.2⟩

/-- Exact finite q-product upper-bound checker. -/
def checkFiniteIntegralUpper (S : Finset Nat) (hi : ℚ) : Bool :=
  decide (finiteIntegralRat S ≤ hi)

/-- Exact finite q-product lower-bound checker. -/
def checkFiniteIntegralLower (S : Finset Nat) (lo : ℚ) : Bool :=
  decide (lo ≤ finiteIntegralRat S)

theorem verify_finiteIntegral_upper (S : Finset Nat) (hi : ℚ)
    (hcheck : checkFiniteIntegralUpper S hi = true) :
    F S ≤ (hi : ℝ) := by
  simp only [checkFiniteIntegralUpper, decide_eq_true_eq] at hcheck
  rw [← finiteIntegralRat_correct]
  exact_mod_cast hcheck

theorem verify_finiteIntegral_lower (S : Finset Nat) (lo : ℚ)
    (hcheck : checkFiniteIntegralLower S lo = true) :
    (lo : ℝ) ≤ F S := by
  simp only [checkFiniteIntegralLower, decide_eq_true_eq] at hcheck
  rw [← finiteIntegralRat_correct]
  exact_mod_cast hcheck

end LeanCert.QProduct
