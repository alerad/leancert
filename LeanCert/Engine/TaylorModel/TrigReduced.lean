/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Trig
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Core.IntervalRat.Taylor

/-!
# Taylor Models with Range Reduction for Trigonometric Functions

This file implements range reduction for sin and cos to improve Taylor series
convergence for intervals far from 0.

## Problem

Standard Taylor series for sin/cos centered at 0 have remainder bounds of
`|x|^{n+1} / (n+1)!`. For intervals far from 0 (e.g., [10, 11]), this remainder
is huge even for moderate n.

## Solution: Range Reduction

Use the periodicity of sin/cos:
- `sin(x) = sin(x - 2πk)` for any integer k
- `cos(x) = cos(x - 2πk)` for any integer k

By choosing k to bring x - 2πk into [-π, π], the Taylor series converges much
faster since |x - 2πk| ≤ π ≈ 3.14.

## Main definitions

* `twoPiRatLo`, `twoPiRatHi` - Rational bounds for 2π
* `reduceToMainPeriod` - Shift interval to be near 0
* `sinIntervalReduced`, `cosIntervalReduced` - Interval evaluation with range reduction
-/

namespace LeanCert.Engine.TaylorModel

open LeanCert.Core

/-! ### Rational approximations of π and 2π -/

/-- Lower bound for π: 314159265/100000000 < π -/
def piRatLo : ℚ := 314159265/100000000

/-- Upper bound for π: π < 355/113 -/
def piRatHi : ℚ := 355/113

/-- Lower bound for 2π -/
def twoPiRatLo : ℚ := 2 * piRatLo

/-- Upper bound for 2π -/
def twoPiRatHi : ℚ := 2 * piRatHi

/-- `piRatLo < π`, proved from Mathlib's decimal π bounds. -/
theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi := by
  have h₁ : (piRatLo : ℝ) < (3.14159265358979323846 : ℝ) := by
    norm_num [piRatLo]
  exact lt_trans h₁ Real.pi_gt_d20

/-- `π < piRatHi`, proved from Mathlib's decimal π bounds. -/
theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) := by
  have h₁ : (3.14159265358979323847 : ℝ) < (piRatHi : ℝ) := by
    norm_num [piRatHi]
  exact lt_trans Real.pi_lt_d20 h₁

/-- twoPiRatLo < 2π -/
theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi := by
  unfold twoPiRatLo
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  have h := piRatLo_lt_pi
  linarith

/-- 2π < twoPiRatHi -/
theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) := by
  unfold twoPiRatHi
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  have h := pi_lt_piRatHi
  linarith

/-- twoPiRatLo ≤ twoPiRatHi -/
theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi := by
  unfold twoPiRatLo twoPiRatHi piRatLo piRatHi
  norm_num

/-! ### Range reduction -/

/-- Compute the shift amount k such that I.midpoint - k * 2π is approximately in [-π, π]. -/
def computeShiftK (I : IntervalRat) : ℤ :=
  let mid := I.midpoint
  (mid / twoPiRatHi).floor

/-- Shift an interval by subtracting k * 2π (using rational bounds).

    For positive k: subtract k * twoPiRatHi from lo, k * twoPiRatLo from hi
    For negative k: opposite to maintain containment
-/
def shiftInterval (I : IntervalRat) (k : ℤ) : IntervalRat :=
  if hk : k ≥ 0 then
    ⟨I.lo - k * twoPiRatHi, I.hi - k * twoPiRatLo,
      by have h1 := twoPiRatLo_le_twoPiRatHi
         have hk_cast : (0 : ℚ) ≤ k := Int.cast_nonneg hk
         have h2 : (k : ℚ) * twoPiRatLo ≤ k * twoPiRatHi :=
           mul_le_mul_of_nonneg_left h1 hk_cast
         linarith [I.le]⟩
  else
    ⟨I.lo - k * twoPiRatLo, I.hi - k * twoPiRatHi,
      by have h1 := twoPiRatLo_le_twoPiRatHi
         have hkneg : k < 0 := Int.not_le.mp hk
         have hk_cast : (k : ℚ) ≤ 0 := Int.cast_nonpos.mpr (le_of_lt hkneg)
         have h2 : (k : ℚ) * twoPiRatHi ≤ k * twoPiRatLo :=
           mul_le_mul_of_nonpos_left h1 hk_cast
         linarith [I.le]⟩

/-- Reduce interval to be approximately in [-π, π] by subtracting multiples of 2π. -/
def reduceToMainPeriod (I : IntervalRat) : IntervalRat × ℤ :=
  let k := computeShiftK I
  (shiftInterval I k, k)

/-! ### Correctness of range reduction -/

/-- If x ∈ I (as reals), then x - 2πk ∈ shiftInterval I k (as reals). -/
theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  simp only [IntervalRat.mem_def] at hx ⊢
  unfold shiftInterval
  split_ifs with hk
  · -- k ≥ 0 case
    constructor
    · -- x - 2πk ≥ I.lo - k * twoPiRatHi
      have h1 : (I.lo : ℝ) ≤ x := hx.1
      have h2 : 2 * Real.pi ≤ (twoPiRatHi : ℝ) := le_of_lt two_pi_lt_twoPiRatHi
      have hk_cast : (0 : ℝ) ≤ k := Int.cast_nonneg hk
      have h3 : 2 * Real.pi * k ≤ (twoPiRatHi : ℝ) * k :=
        mul_le_mul_of_nonneg_right h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
    · -- x - 2πk ≤ I.hi - k * twoPiRatLo
      have h1 : x ≤ (I.hi : ℝ) := hx.2
      have h2 : (twoPiRatLo : ℝ) ≤ 2 * Real.pi := le_of_lt twoPiRatLo_lt_two_pi
      have hk_cast : (0 : ℝ) ≤ k := Int.cast_nonneg hk
      have h3 : (twoPiRatLo : ℝ) * k ≤ 2 * Real.pi * k :=
        mul_le_mul_of_nonneg_right h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
  · -- k < 0 case
    have hkneg : k < 0 := Int.not_le.mp hk
    have hk_cast : (k : ℝ) ≤ 0 := Int.cast_nonpos.mpr (le_of_lt hkneg)
    constructor
    · -- x - 2πk ≥ I.lo - k * twoPiRatLo
      have h1 : (I.lo : ℝ) ≤ x := hx.1
      have h2 : (twoPiRatLo : ℝ) ≤ 2 * Real.pi := le_of_lt twoPiRatLo_lt_two_pi
      -- k < 0 and twoPiRatLo ≤ 2π, so k * 2π ≤ k * twoPiRatLo
      have h3 : (k : ℝ) * (2 * Real.pi) ≤ k * twoPiRatLo :=
        mul_le_mul_of_nonpos_left h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
    · -- x - 2πk ≤ I.hi - k * twoPiRatHi
      have h1 : x ≤ (I.hi : ℝ) := hx.2
      have h2 : 2 * Real.pi ≤ (twoPiRatHi : ℝ) := le_of_lt two_pi_lt_twoPiRatHi
      -- k < 0 and 2π ≤ twoPiRatHi, so k * twoPiRatHi ≤ k * 2π
      have h3 : (k : ℝ) * twoPiRatHi ≤ k * (2 * Real.pi) :=
        mul_le_mul_of_nonpos_left h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith

/-- Convenience form: if x ∈ I, then x - 2πk ∈ (reduceToMainPeriod I).1 -/
theorem mem_reduceToMainPeriod_of_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x - 2 * Real.pi * (reduceToMainPeriod I).2 ∈ (reduceToMainPeriod I).1 := by
  unfold reduceToMainPeriod
  exact mem_shiftInterval_of_mem hx

/-! ### Reduced trigonometric interval evaluation -/

/-- Evaluate sin on an interval using range reduction. -/
noncomputable def sinIntervalReduced (I : IntervalRat) (degree : ℕ := 15) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    (tmSin Ired degree).bound

/-- Evaluate cos on an interval using range reduction. -/
noncomputable def cosIntervalReduced (I : IntervalRat) (degree : ℕ := 15) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    (tmCos Ired degree).bound

/-! ### Correctness theorems -/

/-- sin x ∈ sinIntervalReduced I for all x ∈ I -/
theorem mem_sinIntervalReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (degree : ℕ := 15) :
    Real.sin x ∈ sinIntervalReduced I degree := by
  unfold sinIntervalReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hsin_eq : Real.sin x = Real.sin (x - 2 * Real.pi * k) := by
    have h := Real.sin_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  · push_neg at hwide
    rw [hsin_eq]
    exact taylorModel_correct (tmSin Ired degree) Real.sin
      (fun z hz => tmSin_correct Ired degree z hz) (x - 2 * Real.pi * k) hxred

/-- cos x ∈ cosIntervalReduced I for all x ∈ I -/
theorem mem_cosIntervalReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (degree : ℕ := 15) :
    Real.cos x ∈ cosIntervalReduced I degree := by
  unfold cosIntervalReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hcos_eq : Real.cos x = Real.cos (x - 2 * Real.pi * k) := by
    have h := Real.cos_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  · push_neg at hwide
    rw [hcos_eq]
    exact taylorModel_correct (tmCos Ired degree) Real.cos
      (fun z hz => tmCos_correct Ired degree z hz) (x - 2 * Real.pi * k) hxred

/-! ### Computable versions using Core sinComputable/cosComputable

These are fully computable wrappers that combine range reduction with the
simpler Core Taylor series evaluation. These are what should be used in
`evalIntervalCore`.
-/

/-- Computable sin evaluation with range reduction.
    Uses Core.sinComputable on the reduced interval. -/
def sinComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    IntervalRat.sinComputable Ired n

/-- Computable cos evaluation with range reduction.
    Uses Core.cosComputable on the reduced interval. -/
def cosComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    IntervalRat.cosComputable Ired n

/-- sin x ∈ sinComputableReduced I for all x ∈ I -/
theorem mem_sinComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.sin x ∈ sinComputableReduced I n := by
  unfold sinComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hsin_eq : Real.sin x = Real.sin (x - 2 * Real.pi * k) := by
    have h := Real.sin_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  · push_neg at hwide
    rw [hsin_eq]
    exact IntervalRat.mem_sinComputable hxred n

/-- cos x ∈ cosComputableReduced I for all x ∈ I -/
theorem mem_cosComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.cos x ∈ cosComputableReduced I n := by
  unfold cosComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hcos_eq : Real.cos x = Real.cos (x - 2 * Real.pi * k) := by
    have h := Real.cos_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  · push_neg at hwide
    rw [hcos_eq]
    exact IntervalRat.mem_cosComputable hxred n

end LeanCert.Engine.TaylorModel
