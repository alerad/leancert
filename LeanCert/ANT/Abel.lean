/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Step
import Mathlib.Algebra.BigOperators.Module

/-!
# Abel / partial-summation certificates

The first layer is the exact finite Abel transform.  It is deliberately discrete:
continuous Stieltjes-integral refinements can be built on top of this identity
without changing finite certificate data.
-/

namespace LeanCert.ANT

open scoped BigOperators

/-- Prefix sum `∑ i < n, a i`. -/
noncomputable def prefixSum (a : Nat → ℝ) (n : Nat) : ℝ :=
  ∑ i ∈ Finset.range n, a i

/-- Rational prefix sum `∑ i < n, a i`. -/
def prefixSumRat (a : Nat → ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, a i

/-- Rational finite Abel transform on `[m, n)`. -/
def abelTransformRat (a f : Nat → ℚ) (m n : Nat) : ℚ :=
  f (n - 1) * prefixSumRat a n -
    f m * prefixSumRat a m -
      ∑ i ∈ Finset.Ico m (n - 1),
        (f (i + 1) - f i) * prefixSumRat a (i + 1)

/-- Direct rational weighted sum on `[m, n)`. -/
def weightedSumRat (a f : Nat → ℚ) (m n : Nat) : ℚ :=
  ∑ i ∈ Finset.Ico m n, f i * a i

theorem prefixSumRat_cast (a : Nat → ℚ) (n : Nat) :
    (prefixSumRat a n : ℝ) = prefixSum (fun i => (a i : ℝ)) n := by
  unfold prefixSumRat prefixSum
  rw [Rat.cast_sum]

/-- Abel's finite summation-by-parts identity, in the rational evaluator form. -/
theorem weightedSumRat_eq_abelTransformRat {a f : Nat → ℚ} {m n : Nat}
    (hmn : m < n) :
    (weightedSumRat a f m n : ℝ) = (abelTransformRat a f m n : ℝ) := by
  unfold weightedSumRat abelTransformRat prefixSumRat
  rw [Rat.cast_sum, Rat.cast_sub, Rat.cast_sub, Rat.cast_mul, Rat.cast_mul, Rat.cast_sum]
  simp only [Rat.cast_mul]
  have h := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ)
    (fun i => (f i : ℝ)) (fun i => (a i : ℝ)) hmn
  simpa [prefixSum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Exact rational Abel interval checker. -/
def checkAbelInterval (a f : Nat → ℚ) (m n : Nat) (lo hi : ℚ) : Bool :=
  decide (lo ≤ abelTransformRat a f m n) && decide (abelTransformRat a f m n ≤ hi)

/-- Exact rational Abel upper checker. -/
def checkAbelUpper (a f : Nat → ℚ) (m n : Nat) (hi : ℚ) : Bool :=
  decide (abelTransformRat a f m n ≤ hi)

/-- Exact rational Abel lower checker. -/
def checkAbelLower (a f : Nat → ℚ) (m n : Nat) (lo : ℚ) : Bool :=
  decide (lo ≤ abelTransformRat a f m n)

/-- Golden theorem for exact finite Abel interval certificates. -/
theorem verify_abel_interval (a f : Nat → ℚ) {m n : Nat} (hmn : m < n) (lo hi : ℚ)
    (hcheck : checkAbelInterval a f m n lo hi = true) :
    (lo : ℝ) ≤ (weightedSumRat a f m n : ℝ) ∧
      (weightedSumRat a f m n : ℝ) ≤ (hi : ℝ) := by
  simp only [checkAbelInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rw [weightedSumRat_eq_abelTransformRat hmn]
  exact ⟨by exact_mod_cast hcheck.1, by exact_mod_cast hcheck.2⟩

/-- Golden theorem for exact finite Abel upper certificates. -/
theorem verify_abel_upper (a f : Nat → ℚ) {m n : Nat} (hmn : m < n) (hi : ℚ)
    (hcheck : checkAbelUpper a f m n hi = true) :
    (weightedSumRat a f m n : ℝ) ≤ (hi : ℝ) := by
  simp only [checkAbelUpper, decide_eq_true_eq] at hcheck
  rw [weightedSumRat_eq_abelTransformRat hmn]
  exact_mod_cast hcheck

/-- Golden theorem for exact finite Abel lower certificates. -/
theorem verify_abel_lower (a f : Nat → ℚ) {m n : Nat} (hmn : m < n) (lo : ℚ)
    (hcheck : checkAbelLower a f m n lo = true) :
    (lo : ℝ) ≤ (weightedSumRat a f m n : ℝ) := by
  simp only [checkAbelLower, decide_eq_true_eq] at hcheck
  rw [weightedSumRat_eq_abelTransformRat hmn]
  exact_mod_cast hcheck

end LeanCert.ANT
