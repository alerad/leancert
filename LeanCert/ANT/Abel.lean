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

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

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

/-- Direct real weighted sum on `[m, n)`, with rational weights. -/
noncomputable def weightedSum (a : Nat → ℝ) (f : Nat → ℚ) (m n : Nat) : ℝ :=
  ∑ i ∈ Finset.Ico m n, (f i : ℝ) * a i

/-- Abel transform written against an arbitrary real prefix function `A`. -/
noncomputable def abelTransformOfPrefix (f : Nat → ℚ) (A : Nat → ℝ) (m n : Nat) : ℝ :=
  (f (n - 1) : ℝ) * A n -
    (f m : ℝ) * A m -
      ∑ i ∈ Finset.Ico m (n - 1),
        ((f (i + 1) - f i : ℚ) : ℝ) * A (i + 1)

/-- Direct real weighted sum on `[m, n)`. -/
noncomputable def weightedSumReal (a f : Nat → ℝ) (m n : Nat) : ℝ :=
  ∑ i ∈ Finset.Ico m n, f i * a i

/-- Abel transform on `[m, n)` with real weights and an arbitrary real prefix function `A`. -/
noncomputable def abelTransformReal (f A : Nat → ℝ) (m n : Nat) : ℝ :=
  f (n - 1) * A n -
    f m * A m -
      ∑ i ∈ Finset.Ico m (n - 1),
        (f (i + 1) - f i) * A (i + 1)

theorem prefixSumRat_cast (a : Nat → ℚ) (n : Nat) :
    (prefixSumRat a n : ℝ) = prefixSum (fun i => (a i : ℝ)) n := by
  unfold prefixSumRat prefixSum
  rw [Rat.cast_sum]

/-- Abel's finite summation-by-parts identity for real summands and real weights. -/
theorem weightedSumReal_eq_abelTransformReal {a f : Nat → ℝ} {m n : Nat}
    (hmn : m < n) :
    weightedSumReal a f m n = abelTransformReal f (prefixSum a) m n := by
  unfold weightedSumReal abelTransformReal
  have h := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ) f a hmn
  simpa [prefixSum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Abel's finite summation-by-parts identity for real summands and rational weights. -/
theorem weightedSum_eq_abelTransformOfPrefix {a : Nat → ℝ} {f : Nat → ℚ} {m n : Nat}
    (hmn : m < n) :
    weightedSum a f m n = abelTransformOfPrefix f (prefixSum a) m n := by
  unfold weightedSum abelTransformOfPrefix
  have h := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ)
    (fun i => (f i : ℝ)) a hmn
  simpa [prefixSum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

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
  LeanCert.Cert.checkRatInterval (abelTransformRat a f m n) (abelTransformRat a f m n) lo hi

/-- Exact rational Abel upper checker. -/
def checkAbelUpper (a f : Nat → ℚ) (m n : Nat) (hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatUpper (abelTransformRat a f m n) hi

/-- Exact rational Abel lower checker. -/
def checkAbelLower (a f : Nat → ℚ) (m n : Nat) (lo : ℚ) : Bool :=
  LeanCert.Cert.checkRatLower (abelTransformRat a f m n) lo

/-- Golden theorem for exact finite Abel interval certificates. -/
theorem verify_abel_interval (a f : Nat → ℚ) {m n : Nat} (hmn : m < n) (lo hi : ℚ)
    (hcheck : checkAbelInterval a f m n lo hi = true) :
    (lo : ℝ) ≤ (weightedSumRat a f m n : ℝ) ∧
      (weightedSumRat a f m n : ℝ) ≤ (hi : ℝ) := by
  simp only [checkAbelInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rw [weightedSumRat_eq_abelTransformRat hmn]
  exact LeanCert.Cert.verify_rat_interval le_rfl le_rfl hcheck

/-- Golden theorem for exact finite Abel upper certificates. -/
theorem verify_abel_upper (a f : Nat → ℚ) {m n : Nat} (hmn : m < n) (hi : ℚ)
    (hcheck : checkAbelUpper a f m n hi = true) :
    (weightedSumRat a f m n : ℝ) ≤ (hi : ℝ) := by
  simp only [checkAbelUpper, decide_eq_true_eq] at hcheck
  rw [weightedSumRat_eq_abelTransformRat hmn]
  exact LeanCert.Cert.verify_rat_upper le_rfl hcheck

/-- Golden theorem for exact finite Abel lower certificates. -/
theorem verify_abel_lower (a f : Nat → ℚ) {m n : Nat} (hmn : m < n) (lo : ℚ)
    (hcheck : checkAbelLower a f m n lo = true) :
    (lo : ℝ) ≤ (weightedSumRat a f m n : ℝ) := by
  simp only [checkAbelLower, decide_eq_true_eq] at hcheck
  rw [weightedSumRat_eq_abelTransformRat hmn]
  exact LeanCert.Cert.verify_rat_lower le_rfl hcheck

/-! ### Bounded Abel certificates -/

/-- Lower contribution of `c * A` when `A ∈ [lo, hi]`. -/
def coeffLowerRat (c lo hi : ℚ) : ℚ :=
  if 0 ≤ c then c * lo else c * hi

/-- Upper contribution of `c * A` when `A ∈ [lo, hi]`. -/
def coeffUpperRat (c lo hi : ℚ) : ℚ :=
  if 0 ≤ c then c * hi else c * lo

private theorem coeffLowerRat_le_mul {c lo hi : ℚ} {A : ℝ}
    (hlo : (lo : ℝ) ≤ A) (hhi : A ≤ (hi : ℝ)) :
    (coeffLowerRat c lo hi : ℝ) ≤ (c : ℝ) * A := by
  unfold coeffLowerRat
  by_cases hc : 0 ≤ c
  · simp [hc]
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast hc)
  · simp [hc]
    have hc_nonpos : (c : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hc
    exact mul_le_mul_of_nonpos_left hhi hc_nonpos

private theorem mul_le_coeffUpperRat {c lo hi : ℚ} {A : ℝ}
    (hlo : (lo : ℝ) ≤ A) (hhi : A ≤ (hi : ℝ)) :
    (c : ℝ) * A ≤ (coeffUpperRat c lo hi : ℝ) := by
  unfold coeffUpperRat
  by_cases hc : 0 ≤ c
  · simp [hc]
    exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast hc)
  · simp [hc]
    have hc_nonpos : (c : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hc
    exact mul_le_mul_of_nonpos_left hlo hc_nonpos

/-- Lower bound for the Abel transform from prefix envelopes. -/
def abelBoundLowerRat (f ALo AHi : Nat → ℚ) (m n : Nat) : ℚ :=
  coeffLowerRat (f (n - 1)) (ALo n) (AHi n) +
    coeffLowerRat (-(f m)) (ALo m) (AHi m) +
      ∑ i ∈ Finset.Ico m (n - 1),
        coeffLowerRat (-(f (i + 1) - f i)) (ALo (i + 1)) (AHi (i + 1))

/-- Upper bound for the Abel transform from prefix envelopes. -/
def abelBoundUpperRat (f ALo AHi : Nat → ℚ) (m n : Nat) : ℚ :=
  coeffUpperRat (f (n - 1)) (ALo n) (AHi n) +
    coeffUpperRat (-(f m)) (ALo m) (AHi m) +
      ∑ i ∈ Finset.Ico m (n - 1),
        coeffUpperRat (-(f (i + 1) - f i)) (ALo (i + 1)) (AHi (i + 1))

theorem abelBoundLowerRat_le_transform
    (f ALo AHi : Nat → ℚ) (A : Nat → ℝ) (m n : Nat)
    (hA : ∀ k, (ALo k : ℝ) ≤ A k ∧ A k ≤ (AHi k : ℝ)) :
    (abelBoundLowerRat f ALo AHi m n : ℝ) ≤ abelTransformOfPrefix f A m n := by
  unfold abelBoundLowerRat abelTransformOfPrefix
  rw [Rat.cast_add, Rat.cast_add, Rat.cast_sum]
  apply add_le_add
  · apply add_le_add
    · exact coeffLowerRat_le_mul (hA n).1 (hA n).2
    · simpa using coeffLowerRat_le_mul (c := -(f m)) (hA m).1 (hA m).2
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hterm := coeffLowerRat_le_mul (c := -(f (i + 1) - f i))
      (hA (i + 1)).1 (hA (i + 1)).2
    convert hterm using 1 <;> simp [Nat.add_comm] <;> ring_nf

theorem transform_le_abelBoundUpperRat
    (f ALo AHi : Nat → ℚ) (A : Nat → ℝ) (m n : Nat)
    (hA : ∀ k, (ALo k : ℝ) ≤ A k ∧ A k ≤ (AHi k : ℝ)) :
    abelTransformOfPrefix f A m n ≤ (abelBoundUpperRat f ALo AHi m n : ℝ) := by
  unfold abelBoundUpperRat abelTransformOfPrefix
  rw [Rat.cast_add, Rat.cast_add, Rat.cast_sum]
  apply add_le_add
  · apply add_le_add
    · exact mul_le_coeffUpperRat (hA n).1 (hA n).2
    · simpa using mul_le_coeffUpperRat (c := -(f m)) (hA m).1 (hA m).2
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hterm := mul_le_coeffUpperRat (c := -(f (i + 1) - f i))
      (hA (i + 1)).1 (hA (i + 1)).2
    convert hterm using 1 <;> simp [Nat.add_comm] <;> ring_nf

/-- Alias with the semantic object first in the name. -/
theorem abelTransformOfPrefix_le_abelBoundUpperRat
    (f ALo AHi : Nat → ℚ) (A : Nat → ℝ) (m n : Nat)
    (hA : ∀ k, (ALo k : ℝ) ≤ A k ∧ A k ≤ (AHi k : ℝ)) :
    abelTransformOfPrefix f A m n ≤ (abelBoundUpperRat f ALo AHi m n : ℝ) :=
  transform_le_abelBoundUpperRat f ALo AHi A m n hA

/-- Alias with the semantic object first in the name. -/
theorem abelTransformOfPrefix_ge_abelBoundLowerRat
    (f ALo AHi : Nat → ℚ) (A : Nat → ℝ) (m n : Nat)
    (hA : ∀ k, (ALo k : ℝ) ≤ A k ∧ A k ≤ (AHi k : ℝ)) :
    (abelBoundLowerRat f ALo AHi m n : ℝ) ≤ abelTransformOfPrefix f A m n :=
  abelBoundLowerRat_le_transform f ALo AHi A m n hA

/-- Boolean interval checker for Abel bounds from prefix envelopes. -/
def checkAbelBoundInterval (f ALo AHi : Nat → ℚ) (m n : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (abelBoundLowerRat f ALo AHi m n)
    (abelBoundUpperRat f ALo AHi m n) lo hi

/-- Golden theorem for bounded Abel certificates. -/
theorem verify_abelBound_interval
    (a : Nat → ℝ) (f ALo AHi : Nat → ℚ) {m n : Nat} (hmn : m < n)
    (hA : ∀ k, (ALo k : ℝ) ≤ prefixSum a k ∧ prefixSum a k ≤ (AHi k : ℝ))
    (lo hi : ℚ)
    (hcheck : checkAbelBoundInterval f ALo AHi m n lo hi = true) :
    (lo : ℝ) ≤ weightedSum a f m n ∧ weightedSum a f m n ≤ (hi : ℝ) := by
  rw [weightedSum_eq_abelTransformOfPrefix hmn]
  exact LeanCert.Cert.verify_rat_interval
    (abelBoundLowerRat_le_transform f ALo AHi (prefixSum a) m n hA)
    (transform_le_abelBoundUpperRat f ALo AHi (prefixSum a) m n hA)
    hcheck

end LeanCert.ANT
