/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Trig
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Core.TrigReduction

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

/-! ### Shared range-reduction API -/

def piRatLo : ℚ := LeanCert.Core.TrigReduction.piRatLo
def piRatHi : ℚ := LeanCert.Core.TrigReduction.piRatHi
def twoPiRatLo : ℚ := LeanCert.Core.TrigReduction.twoPiRatLo
def twoPiRatHi : ℚ := LeanCert.Core.TrigReduction.twoPiRatHi
def computeShiftK : IntervalRat → ℤ := LeanCert.Core.TrigReduction.computeShiftK
def shiftInterval : IntervalRat → ℤ → IntervalRat := LeanCert.Core.TrigReduction.shiftInterval
def reduceToMainPeriod : IntervalRat → IntervalRat × ℤ :=
  LeanCert.Core.TrigReduction.reduceToMainPeriod

theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi :=
  LeanCert.Core.TrigReduction.piRatLo_lt_pi

theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.pi_lt_piRatHi

theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_lt_two_pi

theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.two_pi_lt_twoPiRatHi

theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_le_twoPiRatHi

theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  change x - 2 * Real.pi * k ∈ LeanCert.Core.TrigReduction.shiftInterval I k
  exact LeanCert.Core.TrigReduction.mem_shiftInterval_of_mem hx

theorem mem_reduceToMainPeriod_of_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x - 2 * Real.pi * (reduceToMainPeriod I).2 ∈ (reduceToMainPeriod I).1 := by
  change x - 2 * Real.pi * (LeanCert.Core.TrigReduction.reduceToMainPeriod I).2 ∈
    (LeanCert.Core.TrigReduction.reduceToMainPeriod I).1
  exact LeanCert.Core.TrigReduction.mem_reduceToMainPeriod_of_mem hx

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
  · push Not at hwide
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
  · push Not at hwide
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
  · push Not at hwide
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
  · push Not at hwide
    rw [hcos_eq]
    exact IntervalRat.mem_cosComputable hxred n

end LeanCert.Engine.TaylorModel
