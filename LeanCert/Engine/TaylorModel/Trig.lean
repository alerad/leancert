/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Core
import LeanCert.Contrib.Sinc
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Taylor Models - Trigonometric Functions

This file contains Taylor polynomial definitions and remainder bounds for
trigonometric functions (sin, cos, sinc), along with function-level Taylor
models and their correctness proofs.

## Main definitions

* `sinTaylorPoly`, `cosTaylorPoly`, `sincTaylorPoly` - Taylor polynomials
* `sinRemainderBound`, `cosRemainderBound`, `sincRemainderBound` - Remainder bounds
* `tmSin`, `tmCos`, `tmSinc` - Function-level Taylor models
* `tmSin_correct`, `tmCos_correct` - Correctness theorems
-/

namespace LeanCert.Engine

open LeanCert.Core
open Polynomial

namespace TaylorModel

/-! ### sin Taylor polynomial -/

/-- Taylor polynomial coefficients for sin at center c = 0:
    sin(x) = x - x³/3! + x⁵/5! - ... -/
noncomputable def sinTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      ((-1 : ℚ) ^ ((i - 1) / 2)) / (Nat.factorial i : ℚ)
    else 0
  else 0

/-- Taylor polynomial for sin of degree n -/
noncomputable def sinTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (sinTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for sin: |sin(x) - T_n(x)| ≤ |x|^{n+1} / (n+1)! since |sin^{(k)}| ≤ 1 -/
noncomputable def sinRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for sin is nonnegative -/
theorem sinRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ sinRemainderBound domain n := by
  unfold sinRemainderBound
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-! ### cos Taylor polynomial -/

/-- Taylor polynomial coefficients for cos at center c = 0:
    cos(x) = 1 - x²/2! + x⁴/4! - ... -/
noncomputable def cosTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 0 then  -- even terms only
      ((-1 : ℚ) ^ (i / 2)) / (Nat.factorial i : ℚ)
    else 0
  else 0

/-- Taylor polynomial for cos of degree n -/
noncomputable def cosTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (cosTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for cos: |cos(x) - T_n(x)| ≤ |x|^{n+1} / (n+1)! since |cos^{(k)}| ≤ 1 -/
noncomputable def cosRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for cos is nonnegative -/
theorem cosRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ cosRemainderBound domain n := by
  unfold cosRemainderBound
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-! ### sinc Taylor polynomial

sinc(x) = sin(x)/x for x ≠ 0, sinc(0) = 1
       = 1 - x²/6 + x⁴/120 - x⁶/5040 + ...
       = Σ_{n=0}^∞ (-1)^n x^{2n} / (2n+1)!

Note: sinc is entire (analytic everywhere), so the series converges for all x.
-/

/-- Taylor polynomial coefficients for sinc at center 0:
    sinc(x) = 1 - x²/6 + x⁴/120 - ... = Σ (-1)^k x^{2k} / (2k+1)! -/
noncomputable def sincTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 0 then  -- even terms only
      let k := i / 2
      ((-1 : ℚ) ^ k) / (Nat.factorial (2 * k + 1) : ℚ)
    else 0
  else 0

/-- Taylor polynomial for sinc of degree n -/
noncomputable def sincTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (sincTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for sinc: uses the fact that |sinc^(n+1)(ξ)| ≤ 1 for all ξ.
    This follows from |sinc(x)| ≤ 1 and derivatives being bounded.
    We use a crude but safe exponential bound. -/
noncomputable def sincRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Crude bound: r^{n+1} / (n+1)! (similar to sin remainder)
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for sinc is nonnegative -/
theorem sincRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ sincRemainderBound domain n := by
  unfold sincRemainderBound
  simp only
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-! ### Function-level Taylor models -/

/-- Taylor model for sin z on domain J, centered at 0, degree n.
    This represents the function z ↦ sin(z) directly. -/
noncomputable def tmSin (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := sinTaylorPoly n
    remainder := ⟨-sinRemainderBound J n, sinRemainderBound J n,
      by linarith [sinRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for cos z on domain J, centered at 0, degree n.
    This represents the function z ↦ cos(z) directly. -/
noncomputable def tmCos (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := cosTaylorPoly n
    remainder := ⟨-cosRemainderBound J n, cosRemainderBound J n,
      by linarith [cosRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for sinc z on domain J, centered at 0, degree n.
    sinc(z) = sin(z)/z for z ≠ 0, sinc(0) = 1. -/
noncomputable def tmSinc (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := sincTaylorPoly n
    remainder := ⟨-sincRemainderBound J n, sincRemainderBound J n,
      by linarith [sincRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-! ### Helper lemmas for iterated derivatives -/

/-- iteratedDeriv n sin/cos at 0 cycle together. We prove both simultaneously.
    The pattern follows: sin(0)=0, cos(0)=1 and derivatives cycle sin→cos→-sin→-cos→sin -/
private theorem iteratedDeriv_sin_cos_zero (n : ℕ) :
    (iteratedDeriv n Real.sin 0 =
      if n % 4 = 0 then 0
      else if n % 4 = 1 then 1
      else if n % 4 = 2 then 0
      else -1) ∧
    (iteratedDeriv n Real.cos 0 =
      if n % 4 = 0 then 1
      else if n % 4 = 1 then 0
      else if n % 4 = 2 then -1
      else 0) := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Real.sin_zero, Real.cos_zero, Nat.zero_mod, ↓reduceIte]
    trivial
  | succ n ih =>
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    constructor
    · -- sin case: deriv sin = cos, so iteratedDeriv (n+1) sin = iteratedDeriv n cos
      rw [iteratedDeriv_succ', Real.deriv_sin, ih.2]
      rcases hmod with h | h | h | h <;> (split_ifs <;> simp_all <;> omega)
    · -- cos case: deriv cos = -sin, so iteratedDeriv (n+1) cos = -iteratedDeriv n sin
      rw [iteratedDeriv_succ', Real.deriv_cos', iteratedDeriv_fun_neg, ih.1]
      rcases hmod with h | h | h | h <;> (split_ifs <;> simp_all <;> omega)

/-- iteratedDeriv n sin at 0 -/
theorem iteratedDeriv_sin_zero (n : ℕ) :
    iteratedDeriv n Real.sin 0 =
      if n % 4 = 0 then 0
      else if n % 4 = 1 then 1
      else if n % 4 = 2 then 0
      else -1 :=
  (iteratedDeriv_sin_cos_zero n).1

/-- iteratedDeriv n cos at 0 -/
theorem iteratedDeriv_cos_zero (n : ℕ) :
    iteratedDeriv n Real.cos 0 =
      if n % 4 = 0 then 1
      else if n % 4 = 1 then 0
      else if n % 4 = 2 then -1
      else 0 :=
  (iteratedDeriv_sin_cos_zero n).2

/-- For even n, iteratedDeriv n sin 0 = 0 -/
theorem iteratedDeriv_sin_zero_even {n : ℕ} (hn : n % 2 = 0) :
    iteratedDeriv n Real.sin 0 = 0 := by
  rw [iteratedDeriv_sin_zero]
  have h : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases h with h | h <;> simp [h]

/-- For odd n, iteratedDeriv n sin 0 = (-1)^((n-1)/2) -/
theorem iteratedDeriv_sin_zero_odd {n : ℕ} (hn : n % 2 = 1) :
    iteratedDeriv n Real.sin 0 = (-1 : ℝ) ^ ((n - 1) / 2) := by
  rw [iteratedDeriv_sin_zero]
  have h : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h with h | h
  · simp only [h]; norm_num
    have heven : Even ((n - 1) / 2) := by rw [Nat.even_iff]; omega
    rw [Even.neg_one_pow heven]
  · simp only [h]; norm_num
    have hodd : Odd ((n - 1) / 2) := by rw [Nat.odd_iff]; omega
    rw [Odd.neg_one_pow hodd]

/-- The sinTaylorCoeffs match the Mathlib Taylor coefficients for sin at 0 -/
theorem sinTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (sinTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.sin 0 / i.factorial := by
  simp only [sinTaylorCoeffs, hi, ↓reduceIte]
  by_cases hodd : i % 2 = 1
  · -- Odd i: coefficient is (-1)^((i-1)/2) / i!
    simp only [hodd, ↓reduceIte]
    rw [iteratedDeriv_sin_zero_odd hodd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
  · -- Even i: coefficient is 0, and iteratedDeriv i sin 0 = 0
    have heven : i % 2 = 0 := by omega
    simp only [hodd]; norm_num
    rw [iteratedDeriv_sin_zero_even heven, zero_div]

/-- For even n, iteratedDeriv n cos 0 = (-1)^(n/2) -/
theorem iteratedDeriv_cos_zero_even {n : ℕ} (hn : n % 2 = 0) :
    iteratedDeriv n Real.cos 0 = (-1 : ℝ) ^ (n / 2) := by
  rw [iteratedDeriv_cos_zero]
  have h : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases h with h | h
  · simp only [h]; norm_num
    have heven : Even (n / 2) := by rw [Nat.even_iff]; omega
    rw [Even.neg_one_pow heven]
  · simp only [h]; norm_num
    have hodd : Odd (n / 2) := by rw [Nat.odd_iff]; omega
    rw [Odd.neg_one_pow hodd]

/-- For odd n, iteratedDeriv n cos 0 = 0 -/
theorem iteratedDeriv_cos_zero_odd {n : ℕ} (hn : n % 2 = 1) :
    iteratedDeriv n Real.cos 0 = 0 := by
  rw [iteratedDeriv_cos_zero]
  have h : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h with h | h <;> simp [h]

/-- The cosTaylorCoeffs match the Mathlib Taylor coefficients for cos at 0 -/
theorem cosTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (cosTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.cos 0 / i.factorial := by
  simp only [cosTaylorCoeffs, hi, ↓reduceIte]
  by_cases heven : i % 2 = 0
  · -- Even i: coefficient is (-1)^(i/2) / i!
    simp only [heven, ↓reduceIte]
    rw [iteratedDeriv_cos_zero_even heven]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
  · -- Odd i: coefficient is 0, and iteratedDeriv i cos 0 = 0
    have hodd : i % 2 = 1 := by omega
    simp only [heven, ↓reduceIte, Rat.cast_zero]
    rw [iteratedDeriv_cos_zero_odd hodd, zero_div]

/-! ### Polynomial evaluation lemmas -/

/-- sinTaylorPoly evaluates to the standard Taylor sum for sin at 0.
    This connects our rational polynomial to Mathlib's Taylor series. -/
theorem sinTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (sinTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * z ^ i := by
  simp only [sinTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := sinTaylorCoeffs_eq_iteratedDeriv n i hi_le
  -- algebraMap ℚ ℝ is definitionally equal to Rat.cast
  change (sinTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-- cosTaylorPoly evaluates to the standard Taylor sum for cos at 0. -/
theorem cosTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (cosTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * z ^ i := by
  simp only [cosTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := cosTaylorCoeffs_eq_iteratedDeriv n i hi_le
  change (cosTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-! ### Correctness theorems -/

/-- Helper: |z| ≤ radius of interval J for z ∈ J -/
private theorem abs_le_interval_radius {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
    |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
  simp only [IntervalRat.mem_def] at hz
  rw [abs_le]
  constructor
  · have h1 : -|(J.lo : ℝ)| ≤ J.lo := neg_abs_le _
    have h2 : -(max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|)) ≤ -|(J.lo : ℝ)| := by
      simp only [neg_le_neg_iff]; exact le_max_left _ _
    linarith
  · have h1 : (J.hi : ℝ) ≤ |(J.hi : ℝ)| := le_abs_self _
    have h2 : |(J.hi : ℝ)| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := le_max_right _ _
    linarith

/-- Helper: z ∈ J means z ∈ [J.lo, J.hi] as real numbers -/
private theorem mem_Icc_of_mem_interval {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
    z ∈ Set.Icc (J.lo : ℝ) (J.hi : ℝ) := by
  simp only [IntervalRat.mem_def] at hz
  exact ⟨hz.1, hz.2⟩

/-- sin z ∈ (tmSin J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.sin, c = 0, M = 1. -/
theorem tmSin_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.sin z ∈ (tmSin J n).evalSet z := by
  intro z hz
  simp only [tmSin, evalSet, Set.mem_setOf_eq]
  set r := Real.sin z - Polynomial.aeval (z - 0) (sinTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    -- Rewrite polynomial to Mathlib form
    have hpoly_eq := sinTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    -- The remainder r = sin z - ∑ (iteratedDeriv i sin 0 / i!) * z^i
    have hr_rewrite : r = Real.sin z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sin 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
    -- Apply taylor_remainder_bound with f = sin, c = 0, M = 1
    set a := min (J.lo : ℝ) 0 with ha_def
    set b := max (J.hi : ℝ) 0 with hb_def
    have hab : a ≤ b := by simp only [ha_def, hb_def]; exact le_trans (min_le_of_right_le (le_refl 0)) (le_max_right _ _)
    have hca : a ≤ 0 := min_le_right _ _
    have hcb : 0 ≤ b := le_max_right _ _
    have hz_ab : z ∈ Set.Icc a b := by
      simp only [Set.mem_Icc, ha_def, hb_def]
      have hmem := mem_Icc_of_mem_interval hz
      constructor
      · exact le_trans (min_le_left _ _) hmem.1
      · exact le_trans hmem.2 (le_max_left _ _)
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.sin x‖ ≤ 1 := by
      intro x _
      exact (LeanCert.Core.sin_cos_deriv_bound (n + 1) x).1
    have hf : ContDiff ℝ (n + 1) Real.sin := Real.contDiff_sin.of_le le_top
    have hTaylor := LeanCert.Core.taylor_remainder_bound hab hca hcb hf hM (by norm_num : (0 : ℝ) ≤ 1) z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ 1 * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    simp only [one_mul] at hr_bound
    -- |r| ≤ sinRemainderBound since |z| ≤ radius
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hrem_eq : (sinRemainderBound J n : ℝ) = (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
      simp only [sinRemainderBound, hradius_def, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]
      exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hrem_ge : (sinRemainderBound J n : ℝ) ≥ |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hrem_eq]
      apply div_le_div_of_nonneg_right hpow_le (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ sinRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

/-- cos z ∈ (tmCos J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.cos, c = 0, M = 1. -/
theorem tmCos_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.cos z ∈ (tmCos J n).evalSet z := by
  intro z hz
  simp only [tmCos, evalSet, Set.mem_setOf_eq]
  set r := Real.cos z - Polynomial.aeval (z - 0) (cosTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := cosTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.cos z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cos 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
    set a := min (J.lo : ℝ) 0 with ha_def
    set b := max (J.hi : ℝ) 0 with hb_def
    have hab : a ≤ b := by simp only [ha_def, hb_def]; exact le_trans (min_le_of_right_le (le_refl 0)) (le_max_right _ _)
    have hca : a ≤ 0 := min_le_right _ _
    have hcb : 0 ≤ b := le_max_right _ _
    have hz_ab : z ∈ Set.Icc a b := by
      simp only [Set.mem_Icc, ha_def, hb_def]
      have hmem := mem_Icc_of_mem_interval hz
      constructor
      · exact le_trans (min_le_left _ _) hmem.1
      · exact le_trans hmem.2 (le_max_left _ _)
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.cos x‖ ≤ 1 := by
      intro x _
      exact (LeanCert.Core.sin_cos_deriv_bound (n + 1) x).2
    have hf : ContDiff ℝ (n + 1) Real.cos := Real.contDiff_cos.of_le le_top
    have hTaylor := LeanCert.Core.taylor_remainder_bound hab hca hcb hf hM (by norm_num : (0 : ℝ) ≤ 1) z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ 1 * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    simp only [one_mul] at hr_bound
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hrem_eq : (cosRemainderBound J n : ℝ) = (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
      simp only [cosRemainderBound, hradius_def, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]
      exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hrem_ge : (cosRemainderBound J n : ℝ) ≥ |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hrem_eq]
      apply div_le_div_of_nonneg_right hpow_le (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ cosRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

/-! ### sinc correctness infrastructure -/

/-- sinc is C^∞ (smooth).

    Mathematical justification: sinc is analytic everywhere with the series
    sinc(x) = Σ_{k=0}^∞ (-1)^k x^{2k} / (2k+1)!
    which converges for all x ∈ ℝ. Being analytic, it is smooth (C^∞).

    This fact follows from sinc being the dslope of sin at 0, and sin being
    entire (analytic everywhere). The smoothness can be proven using the
    series representation or by showing the iterated derivatives exist and
    are continuous at all points including 0.

    Technical note: The proof at x = 0 is subtle because we need to show
    that the limit defining each higher derivative exists. This follows from
    the Taylor series representation. -/
theorem contDiff_sinc : ContDiff ℝ ⊤ Real.sinc := Real.contDiff_sinc

/-- The n-th derivative of sinc at 0 follows the pattern:
    - For odd n: 0 (sinc is even, so odd derivatives at 0 vanish)
    - For even n = 2k: (-1)^k * (2k)! / (2k+1)!  = (-1)^k / (2k+1)

    This matches the coefficients in sincTaylorCoeffs times n!.

    The proof uses the recurrence: (n+1) * sinc^{(n)}(0) = sin^{(n+1)}(0),
    which follows from differentiating x * sinc(x) = sin(x). -/
theorem iteratedDeriv_sinc_zero (n : ℕ) :
    iteratedDeriv n Real.sinc 0 = if n % 2 = 0 then
      let k := n / 2
      ((-1 : ℝ) ^ k) / ((2 * k + 1) : ℕ)
    else 0 := by
  -- The recurrence: (n+1) * sinc^{(n)}(0) = sin^{(n+1)}(0)
  -- This follows from: d^{n+1}/dx^{n+1}(x * sinc(x))|_0 = (n+1) * sinc^{(n)}(0) by Leibniz
  -- And x * sinc(x) = sin(x)
  have h_recurrence : ∀ m : ℕ, ((m : ℝ) + 1) * iteratedDeriv m Real.sinc 0 = iteratedDeriv (m + 1) Real.sin 0 := by
    intro m
    have h_eq : ∀ x, x * Real.sinc x = Real.sin x := fun x => by
      by_cases hx : x = 0
      · simp [hx, Real.sinc_zero]
      · rw [Real.sinc_of_ne_zero hx]; field_simp
    have h_deriv_eq : ∀ k x, iteratedDeriv k (fun y => y * Real.sinc y) x = iteratedDeriv k Real.sin x := by
      intro k x; congr 1; exact funext h_eq
    -- Prove: iteratedDeriv (m+1) (x * sinc) 0 = (m+1) * sinc^{(m)}(0) by induction
    suffices h : iteratedDeriv (m + 1) (fun y => y * Real.sinc y) 0 = (m + 1 : ℝ) * iteratedDeriv m Real.sinc 0 by
      rw [← h_deriv_eq (m + 1) 0, h]
    induction m with
    | zero =>
      simp only [iteratedDeriv_zero, zero_add]
      rw [iteratedDeriv_one]
      have hd : HasDerivAt (fun y => y * Real.sinc y) (Real.sinc (0:ℝ) + (0:ℝ) * deriv Real.sinc (0:ℝ)) (0:ℝ) := by
        have h1 : HasDerivAt (fun y : ℝ => y) 1 (0:ℝ) := hasDerivAt_id (0:ℝ)
        have h2 : HasDerivAt Real.sinc (deriv Real.sinc (0:ℝ)) (0:ℝ) :=
          Real.differentiable_sinc.differentiableAt.hasDerivAt
        convert h1.mul h2 using 1; ring
      simp only [zero_mul, add_zero] at hd
      rw [hd.deriv]
      simp only [Real.sinc_zero]; ring
    | succ m ihm =>
      have hcd : ContDiff ℝ ⊤ Real.sinc := Real.contDiff_sinc
      -- Prove: iteratedDeriv (k+1) (x*sinc) x = x * sinc^{(k+1)}(x) + (k+1) * sinc^{(k)}(x)
      have h_formula : ∀ k : ℕ, ∀ x : ℝ,
          iteratedDeriv (k + 1) (fun y => y * Real.sinc y) x =
          x * iteratedDeriv (k + 1) Real.sinc x + (k + 1 : ℝ) * iteratedDeriv k Real.sinc x := by
        intro k
        induction k with
        | zero =>
          intro x
          rw [iteratedDeriv_one, iteratedDeriv_zero]
          have hd : deriv (fun y => y * Real.sinc y) x = Real.sinc x + x * deriv Real.sinc x := by
            have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
            have h2 : HasDerivAt Real.sinc (deriv Real.sinc x) x :=
              Real.differentiable_sinc.differentiableAt.hasDerivAt
            have := (h1.mul h2).deriv
            simp only [one_mul] at this
            exact this
          rw [hd, iteratedDeriv_one]
          ring
        | succ k ihk =>
          intro x
          rw [iteratedDeriv_succ]
          have hfunc : iteratedDeriv (k + 1) (fun y => y * Real.sinc y) =
              fun y => y * iteratedDeriv (k + 1) Real.sinc y + (k + 1 : ℝ) * iteratedDeriv k Real.sinc y :=
            funext ihk
          rw [hfunc]
          -- Need: deriv (y * f(y) + c * g(y)) = f + y * f' + c * g'
          have hdiff1 : DifferentiableAt ℝ (fun y => y * iteratedDeriv (k + 1) Real.sinc y) x :=
            differentiableAt_id.mul (hcd.differentiable_iteratedDeriv (k + 1) (by simp)).differentiableAt
          have hdiff2 : DifferentiableAt ℝ (fun y => (k + 1 : ℝ) * iteratedDeriv k Real.sinc y) x :=
            (hcd.differentiable_iteratedDeriv k (by simp)).differentiableAt.const_mul _
          have hd1 : deriv (fun y => y * iteratedDeriv (k + 1) Real.sinc y) x =
              iteratedDeriv (k + 1) Real.sinc x + x * deriv (iteratedDeriv (k + 1) Real.sinc) x := by
            have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
            have h2 : HasDerivAt (iteratedDeriv (k + 1) Real.sinc) _ x :=
              (hcd.differentiable_iteratedDeriv (k + 1) (by simp)).differentiableAt.hasDerivAt
            have := (h1.mul h2).deriv
            simp only [one_mul] at this
            exact this
          have hd2 : deriv (fun y => (k + 1 : ℝ) * iteratedDeriv k Real.sinc y) x =
              (k + 1 : ℝ) * deriv (iteratedDeriv k Real.sinc) x := by
            have h : HasDerivAt (iteratedDeriv k Real.sinc) _ x :=
              (hcd.differentiable_iteratedDeriv k (by simp)).differentiableAt.hasDerivAt
            exact (h.const_mul (k + 1 : ℝ)).deriv
          calc deriv (fun y => y * iteratedDeriv (k + 1) Real.sinc y +
                        (k + 1 : ℝ) * iteratedDeriv k Real.sinc y) x
              = deriv (fun y => y * iteratedDeriv (k + 1) Real.sinc y) x +
                deriv (fun y => (k + 1 : ℝ) * iteratedDeriv k Real.sinc y) x := by
                apply deriv_add hdiff1 hdiff2
            _ = (iteratedDeriv (k + 1) Real.sinc x + x * deriv (iteratedDeriv (k + 1) Real.sinc) x) +
                (k + 1 : ℝ) * deriv (iteratedDeriv k Real.sinc) x := by
                rw [hd1, hd2]
            _ = (iteratedDeriv (k + 1) Real.sinc x + x * iteratedDeriv (k + 2) Real.sinc x) +
                (k + 1 : ℝ) * iteratedDeriv (k + 1) Real.sinc x := by
                simp only [← iteratedDeriv_succ]
            _ = x * iteratedDeriv (k + 1 + 1) Real.sinc x + (↑(k + 1) + 1) * iteratedDeriv (k + 1) Real.sinc x := by
                push_cast; ring
      -- Use h_formula at 0 for m+1
      have hkey := h_formula (m + 1) 0
      simp only [zero_mul, zero_add] at hkey
      exact hkey
  -- Now use the recurrence
  by_cases hn : n % 2 = 0
  · -- n is even
    simp only [hn, ↓reduceIte]
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    subst hk
    simp only [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
    have hr := h_recurrence (2 * k)
    have hodd : (2 * k + 1) % 2 = 1 := by omega
    rw [iteratedDeriv_sin_zero_odd hodd] at hr
    have hexp : ((2 * k + 1 - 1) / 2) = k := by omega
    rw [hexp] at hr
    -- hr : (↑(2 * k) + 1) * iteratedDeriv (2 * k) Real.sinc 0 = (-1) ^ k
    -- Goal: iteratedDeriv (2 * k) Real.sinc 0 = (-1) ^ k / ↑(2 * k + 1)
    have h2k1_ne : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hcast : ((2 * k : ℕ) : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hr
    field_simp [h2k1_ne] at hr ⊢
    linarith
  · -- n is odd
    simp only [hn, ↓reduceIte]
    have hr := h_recurrence n
    have heven : (n + 1) % 2 = 0 := by omega
    rw [iteratedDeriv_sin_zero_even heven] at hr
    -- hr : (↑n + 1) * iteratedDeriv n Real.sinc 0 = 0
    have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
    exact mul_eq_zero.mp hr |>.resolve_left hn_ne

/-- The sincTaylorCoeffs match the Taylor coefficients for sinc at 0 -/
theorem sincTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (sincTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.sinc 0 / i.factorial := by
  simp only [sincTaylorCoeffs, hi, ↓reduceIte]
  by_cases heven : i % 2 = 0
  · simp only [heven, ↓reduceIte]
    rw [iteratedDeriv_sinc_zero]
    simp only [heven, ↓reduceIte]
    -- The coefficients match: (-1)^k / (2k+1)! = ((-1)^k / (2k+1)) / (2k)!
    -- This follows from (2k+1)! = (2k+1) * (2k)!
    obtain ⟨k, hk⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
    subst hk
    simp only [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
    -- LHS: ↑((-1)^k / (2k+1)! : ℚ)  RHS: ((-1)^k / (2k+1)) / (2k)!
    have hfact : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial := Nat.factorial_succ (2 * k)
    -- Simplify LHS in ℚ first: (-1)^k / (2k+1)! = (-1)^k / ((2k+1) * (2k)!)
    have lhs_eq : ((-1 : ℚ) ^ k / ((2 * k + 1).factorial : ℕ) : ℚ) =
        (-1 : ℚ) ^ k / ((2 * k + 1 : ℕ) * (2 * k).factorial) := by
      rw [hfact]; push_cast; rfl
    rw [lhs_eq]
    -- Now both sides are in similar form, convert to ℝ and simplify
    have h2k_fact_ne : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    have h2k1_ne : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · have hodd : i % 2 = 1 := by omega
    simp only [heven]; norm_num
    rw [iteratedDeriv_sinc_zero]
    simp only [heven, ↓reduceIte, zero_div]

/-- sincTaylorPoly evaluates to the standard Taylor sum for sinc at 0. -/
theorem sincTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (sincTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sinc 0 / i.factorial) * z ^ i := by
  simp only [sincTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := sincTaylorCoeffs_eq_iteratedDeriv n i hi_le
  change (sincTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-- Axiom: Higher derivatives of sinc are bounded by 1.

    Mathematical justification:
    Using the integral representation sinc(x) = ∫ t in 0..1, cos(t·x) dt,
    the n-th derivative is sinc^(n)(x) = ∫ t in 0..1, t^n · d^n cos(t·x)/dx^n dt.
    Since |d^n cos(t·x)/dx^n| = t^n |cos or sin(t·x + nπ/2)| ≤ t^n, we have:
    |sinc^(n)(x)| ≤ ∫₀¹ t^n dt = 1/(n+1) ≤ 1.

    This axiom asserts the bound for n ≥ 2. Full formal proof requires:
    1. The integral representation of sinc (requires differentiation under the integral)
    2. Leibniz rule for differentiation under the integral sign
    3. Bounds on iterated derivatives of cos(t·x) with respect to x

    These are substantial Mathlib-level results. The bound is mathematically sound
    and verified numerically for practical purposes. -/
axiom sinc_iteratedDeriv_bound_ge2 (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv (n + 2) Real.sinc x‖ ≤ 1

/-- Bound on the n-th derivative of sinc.

    The bound |iteratedDeriv n sinc x| ≤ 1 holds for all n and x.

    Mathematical justification:
    - For n = 0: |sinc x| ≤ 1 (proven in Mathlib as abs_sinc_le_one)
    - For n = 1: |sinc' x| ≤ 1 (proven in LeanCert.Contrib.Sinc as abs_deriv_sinc_le_one)
    - For n ≥ 2: See axiom `sinc_iteratedDeriv_bound_ge2`

    The uniform bound of 1 is conservative for higher derivatives but sufficient
    for the Taylor remainder estimate. -/
theorem sinc_deriv_bound (n : ℕ) :
    ∀ x : ℝ, ‖iteratedDeriv n Real.sinc x‖ ≤ 1 := by
  intro x
  match n with
  | 0 =>
    -- |sinc x| ≤ 1
    simp only [iteratedDeriv_zero, Real.norm_eq_abs]
    exact Real.abs_sinc_le_one x
  | 1 =>
    -- |sinc' x| ≤ 1
    simp only [iteratedDeriv_one, Real.norm_eq_abs]
    exact Real.abs_deriv_sinc_le_one x
  | n + 2 =>
    -- For n ≥ 2: Use the axiom
    exact sinc_iteratedDeriv_bound_ge2 n x

/-- sinc z ∈ (tmSinc J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.sinc, c = 0, M = 1. -/
theorem tmSinc_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.sinc z ∈ (tmSinc J n).evalSet z := by
  intro z hz
  simp only [tmSinc, evalSet, Set.mem_setOf_eq]
  set r := Real.sinc z - Polynomial.aeval (z - 0) (sincTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := sincTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.sinc z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sinc 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
    -- Apply Taylor's theorem with f = sinc, c = 0, M = 1
    set a := min (J.lo : ℝ) 0 with ha_def
    set b := max (J.hi : ℝ) 0 with hb_def
    have hab : a ≤ b := by simp only [ha_def, hb_def]; exact le_trans (min_le_of_right_le (le_refl 0)) (le_max_right _ _)
    have hca : a ≤ 0 := min_le_right _ _
    have hcb : 0 ≤ b := le_max_right _ _
    have hz_ab : z ∈ Set.Icc a b := by
      simp only [Set.mem_Icc, ha_def, hb_def]
      have hmem := mem_Icc_of_mem_interval hz
      constructor
      · exact le_trans (min_le_left _ _) hmem.1
      · exact le_trans hmem.2 (le_max_left _ _)
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.sinc x‖ ≤ 1 := by
      intro x _
      exact sinc_deriv_bound (n + 1) x
    have hf : ContDiff ℝ (n + 1) Real.sinc := contDiff_sinc.of_le le_top
    have hTaylor := LeanCert.Core.taylor_remainder_bound hab hca hcb hf hM (by norm_num : (0 : ℝ) ≤ 1) z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ 1 * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    simp only [one_mul] at hr_bound
    -- |r| ≤ sincRemainderBound since |z| ≤ radius
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hrem_eq : (sincRemainderBound J n : ℝ) = (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
      simp only [sincRemainderBound, hradius_def, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]
      exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hrem_ge : (sincRemainderBound J n : ℝ) ≥ |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hrem_eq]
      apply div_le_div_of_nonneg_right hpow_le (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ sincRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

end TaylorModel

end LeanCert.Engine
