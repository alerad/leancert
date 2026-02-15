/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Core
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Taylor Models - log(1+x) and Related Functions

This file contains Taylor polynomial definitions and remainder bounds for
log(1+x) centered at 0, which is essential for handling principal value
integrals like li(x).

## Main definitions

* `log1pTaylorPoly` - Taylor polynomial for log(1+x) at center 0
* `log1pRemainderBound` - Remainder bound using Lagrange form
* `tmLog1p` - Function-level Taylor model
* `tmLog1p_correct` - Correctness theorem

## Application: Bounds for the Logarithmic Integral li(x)

The symmetric combination g(t) = 1/log(1+t) + 1/log(1-t) appears in the
principal value integral for li(x). Despite each term having a singularity
at t=0, the combination is bounded. This file provides the infrastructure
to prove this.

Key identity:
  g(t) = [log(1-t) + log(1+t)] / [log(1+t) · log(1-t)]
       = log(1-t²) / [log(1+t) · log(1-t)]

Using Taylor: log(1±t) ≈ ±t - t²/2 ∓ ...
  Numerator: log(1-t²) = -t² + O(t⁴)
  Denominator: log(1+t)·log(1-t) = -t² + O(t³)
  Therefore: g(t) → 1 as t → 0
-/

namespace LeanCert.Engine

open LeanCert.Core
open Polynomial

namespace TaylorModel

/-! ### log(1+x) Taylor polynomial

log(1+x) = x - x²/2 + x³/3 - x⁴/4 + ... = ∑_{k=1}^∞ (-1)^(k+1) x^k / k

Converges for x ∈ (-1, 1].
-/

/-- Taylor polynomial coefficients for log(1+x) at center 0:
    For k ≥ 1: coeff_k = (-1)^(k+1) / k
    For k = 0: coeff_0 = 0 (since log(1+0) = 0) -/
def log1pTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i = 0 then 0
  else if i ≤ n then ((-1 : ℚ)^(i + 1)) / i
  else 0

/-- Taylor polynomial for log(1+x) of degree n -/
noncomputable def log1pTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (log1pTaylorCoeffs n i) * Polynomial.X ^ i

/-- Lagrange remainder bound for log(1+x) Taylor series centered at 0.
    The (n+1)th derivative of log(1+x) is (-1)^n · n! / (1+x)^(n+1).
    For the Taylor expansion at center 0, ξ lies between 0 and z:
    - If z ≥ 0: ξ ∈ [0, z], so min(1+ξ) = 1
    - If z < 0: ξ ∈ [z, 0], so min(1+ξ) = 1+z ≥ 1+lo
    Overall minimum is min(1, 1+lo).
    |R_n(x)| ≤ |x|^(n+1) / [(n+1) · min(1, 1+lo)^(n+1)] -/
noncomputable def log1pLagrangeRemainder (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Need domain ⊂ (-1, ∞), so 1 + domain.lo > 0
  let base := 1 + domain.lo
  if base ≤ 0 then 1000  -- invalid domain
  else
    -- min_denom = min(1, 1+lo) for correct Lagrange bound at center 0
    let min_denom := min 1 base
    r^(n+1) / ((n + 1) * min_denom^(n+1))

/-- Remainder bound is nonnegative for valid domains -/
theorem log1pLagrangeRemainder_nonneg (domain : IntervalRat) (n : ℕ)
    (hdom : domain.lo > -1) :
    0 ≤ log1pLagrangeRemainder domain n := by
  unfold log1pLagrangeRemainder
  have hbase_pos : 0 < 1 + domain.lo := by linarith
  have hbase_not_le : ¬(1 + domain.lo ≤ 0) := not_le.mpr hbase_pos
  simp only [hbase_not_le, ↓reduceIte]
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · apply mul_nonneg
    · have : (0 : ℚ) < n + 1 := by linarith
      linarith
    · apply pow_nonneg
      have hmin_pos : 0 < min 1 (1 + domain.lo) := lt_min one_pos hbase_pos
      linarith

/-- Taylor model for log(1+z) on domain J, centered at 0, degree n.
    Requires J.lo > -1 (domain must be in (-1, ∞)). -/
noncomputable def tmLog1p (J : IntervalRat) (n : ℕ) : Option TaylorModel :=
  if hdom : J.lo > -1 then
    let rem := log1pLagrangeRemainder J n
    some {
      poly := log1pTaylorPoly n
      remainder := ⟨-rem, rem, by
        have h := log1pLagrangeRemainder_nonneg J n hdom
        linarith⟩
      center := 0
      domain := J
    }
  else
    none

/-! ### Correctness theorem -/

/-- The n-th iterated derivative of log(1+x) at a point y > -1.
    Uses chain rule: since (1+x)' = 1, we have
    iteratedDeriv n (log ∘ (1+·)) y = iteratedDeriv n log (1+y).
    Combined with iteratedDeriv_log, this gives (-1)^(n-1) * (n-1)! * (1+y)^(-n). -/
theorem iteratedDeriv_log1p {n : ℕ} (hn : n ≠ 0) {y : ℝ} (hy : -1 < y) :
    iteratedDeriv n (fun x => Real.log (1 + x)) y = ((-1 : ℝ)^(n - 1)) * (n - 1).factorial * (1 + y)^(-(n : ℤ)) := by
  have h1py_pos : 0 < 1 + y := by linarith
  -- Use iteratedDeriv_comp_const_add: iteratedDeriv n (f ∘ (c + ·)) = iteratedDeriv n f (c + ·)
  have hchain : iteratedDeriv n (fun x => Real.log (1 + x)) y = iteratedDeriv n Real.log (1 + y) := by
    have h := iteratedDeriv_comp_const_add n Real.log 1
    exact congrFun h y
  rw [hchain]
  exact LeanCert.Core.iteratedDeriv_log hn h1py_pos

/-- At x = 0, the n-th derivative of log(1+x) is (-1)^(n-1) * (n-1)!. -/
theorem iteratedDeriv_log1p_zero {n : ℕ} (hn : n ≠ 0) :
    iteratedDeriv n (fun x => Real.log (1 + x)) 0 = ((-1 : ℝ)^(n - 1)) * (n - 1).factorial := by
  have h := iteratedDeriv_log1p hn (by norm_num : (-1 : ℝ) < 0)
  simp only [add_zero, one_zpow] at h
  rw [h]
  ring

/-- The coefficients of log1pTaylorPoly match the Taylor coefficients of log(1+x). -/
theorem log1pTaylorCoeffs_eq_deriv (n i : ℕ) (hi_pos : 0 < i) (hi_le : i ≤ n) :
    (log1pTaylorCoeffs n i : ℝ) = iteratedDeriv i (fun x => Real.log (1 + x)) 0 / i.factorial := by
  simp only [log1pTaylorCoeffs, Nat.ne_of_gt hi_pos, ↓reduceIte, hi_le]
  -- The i-th derivative of log(1+x) at 0 is (-1)^(i-1) * (i-1)!
  -- So coeff = (-1)^(i-1) * (i-1)! / i! = (-1)^(i-1) / i
  -- Our formula: (-1)^(i+1) / i = (-1)^(i-1) / i (since (-1)^2 = 1)
  have hderiv : iteratedDeriv i (fun x => Real.log (1 + x)) 0 = ((-1 : ℝ)^(i - 1)) * (i - 1).factorial :=
    iteratedDeriv_log1p_zero (Nat.ne_of_gt hi_pos)
  rw [hderiv]
  -- Now simplify: (-1)^(i+1) / i = (-1)^(i-1) * (i-1)! / i!
  have hfact : (i.factorial : ℝ) = i * (i - 1).factorial := by
    have h := Nat.mul_factorial_pred (Nat.ne_of_gt hi_pos)
    simp only [← h, Nat.cast_mul]
  rw [hfact]
  have hi_ne : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hi_pos)
  have hfact_ne : ((i - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  -- (-1)^(i+1) * (i-1)! = (-1)^(i-1) * (i-1)!
  -- This holds since (-1)^(i+1) = (-1)^(i-1) * (-1)^2 = (-1)^(i-1)
  have hpow : ((-1 : ℝ)^(i + 1)) = ((-1 : ℝ)^(i - 1)) := by
    have h : i + 1 = (i - 1) + 2 := by omega
    rw [h, pow_add]
    simp only [pow_two, neg_one_mul, neg_neg, mul_one]
  -- The goal involves rational cast, need to handle carefully
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
  rw [hpow]
  field_simp [hi_ne]

/-- The polynomial evaluation of log1pTaylorPoly equals the Taylor sum. -/
theorem log1pTaylorPoly_aeval_eq_sum (n : ℕ) (z : ℝ) :
    Polynomial.aeval z ((log1pTaylorPoly n).map (algebraMap ℚ ℝ)) =
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i (fun x => Real.log (1 + x)) 0 / i.factorial) * z ^ i := by
  unfold log1pTaylorPoly
  rw [Polynomial.aeval_map_algebraMap]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
  by_cases hi_zero : i = 0
  · simp only [hi_zero, log1pTaylorCoeffs, ↓reduceIte]
    simp only [map_zero, zero_mul, iteratedDeriv_zero, add_zero, Real.log_one, zero_div]
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi
    have hcoeff := log1pTaylorCoeffs_eq_deriv n i hi_pos hi_le
    -- (algebraMap ℚ ℝ) q = (q : ℝ) for q : ℚ
    have halg : (algebraMap ℚ ℝ) (log1pTaylorCoeffs n i) = (log1pTaylorCoeffs n i : ℝ) := rfl
    rw [halg, hcoeff]

/-- The Taylor remainder for log(1+x) at center 0 is bounded by the Lagrange form.
    This follows the standard Lagrange remainder bound proof:
    - log(1+x) is C^∞ on (-1, ∞)
    - The (n+1)th derivative is ±n!/(1+x)^(n+1)
    - Apply taylor_remainder_bound_on to get the bound -/
theorem log1p_taylor_remainder_bound (J : IntervalRat) (n : ℕ) (z : ℝ)
    (hdom : J.lo > -1) (hz : z ∈ J) :
    |Real.log (1 + z) -
      Polynomial.aeval z ((log1pTaylorPoly n).map (algebraMap ℚ ℝ))| ≤
    (log1pLagrangeRemainder J n : ℝ) := by
  -- The polynomial evaluation equals the Taylor sum
  rw [log1pTaylorPoly_aeval_eq_sum]
  set a : ℝ := (J.lo : ℝ)
  set b : ℝ := (J.hi : ℝ)
  have ha_gt_neg1 : -1 < a := by
    simp only [a]
    have h : ((-1 : ℚ) : ℝ) = (-1 : ℝ) := by norm_num
    rw [← h]
    exact Rat.cast_lt.mpr hdom
  have hz_mem : z ∈ Set.Icc a b := hz

  -- Extend the interval to contain 0 (the center)
  set a' : ℝ := min a 0
  set b' : ℝ := max b 0
  have ha'_gt_neg1 : -1 < a' := lt_min ha_gt_neg1 (by norm_num)
  have h1pa'_pos : 0 < 1 + a' := by linarith
  have ha'_le_0 : a' ≤ 0 := min_le_right a 0
  have h0_le_b' : 0 ≤ b' := le_max_right b 0

  have hz_mem' : z ∈ Set.Icc a' b' :=
    ⟨le_trans (min_le_left a 0) hz_mem.1, le_trans hz_mem.2 (le_max_left b 0)⟩

  -- Apply Taylor's theorem with remainder bound
  have hlog1p_smooth : ContDiffOn ℝ (n + 1) (fun x => Real.log (1 + x)) (Set.Ioi (-1)) := by
    apply (Real.contDiffOn_log.comp _ fun x hx => by simp [Set.mem_Ioi] at hx ⊢; linarith).of_le le_top
    exact (contDiff_const.add contDiff_id).contDiffOn

  have hI'_sub : Set.Icc a' b' ⊆ Set.Ioi (-1 : ℝ) := fun y hy => lt_of_lt_of_le ha'_gt_neg1 hy.1

  set M' : ℝ := n.factorial / (1 + a')^(n+1)
  have hM'_nonneg : 0 ≤ M' := div_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt h1pa'_pos) _)

  have hM'_bound : ∀ y ∈ Set.Icc a' b', ‖iteratedDeriv (n + 1) (fun x => Real.log (1 + x)) y‖ ≤ M' := by
    intro y hy
    have hy_gt_neg1 : -1 < y := lt_of_lt_of_le ha'_gt_neg1 hy.1
    have h1py_pos : 0 < 1 + y := by linarith
    rw [iteratedDeriv_log1p (Nat.succ_ne_zero n) hy_gt_neg1]
    simp only [Real.norm_eq_abs, Nat.succ_sub_one, zpow_neg, zpow_natCast, abs_mul]
    rw [abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_inv, abs_pow, abs_of_pos h1py_pos, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos h1pa'_pos _)
      (pow_le_pow_left₀ (le_of_lt h1pa'_pos) (by linarith [hy.1]) _)

  have hTaylor := LeanCert.Core.taylor_remainder_bound_on isOpen_Ioi hI'_sub
    ha'_le_0 h0_le_b' hlog1p_smooth hM'_bound hM'_nonneg z hz_mem'
  simp only [sub_zero, Real.norm_eq_abs] at hTaylor

  -- Now show M' * |z|^(n+1) / (n+1)! ≤ log1pLagrangeRemainder J n
  calc |Real.log (1 + z) - ∑ i ∈ Finset.range (n + 1),
          iteratedDeriv i (fun x => Real.log (1 + x)) 0 / ↑i.factorial * z ^ i|
      ≤ M' * |z| ^ (n + 1) / (n + 1).factorial := hTaylor
    _ ≤ (log1pLagrangeRemainder J n : ℝ) := by
        unfold log1pLagrangeRemainder
        have hdom' : ¬(1 + J.lo ≤ 0) := by linarith
        simp only [hdom', ite_false]
        -- Key insight: 1+a' = min(1, 1+J.lo) = min_denom
        have h1pa'_eq : (1 + a' : ℝ) = min 1 (1 + a) := by
          simp only [a', a, min_def]
          split_ifs with h1 h2
          · -- h1: J.lo ≤ 0, h2: 1 ≤ 1 + J.lo → J.lo = 0
            have hJlo_zero : (J.lo : ℝ) = 0 := by linarith
            rw [hJlo_zero]; ring
          · ring  -- h1: J.lo ≤ 0, ¬(1 ≤ 1 + J.lo)
          · ring  -- ¬(J.lo ≤ 0), 1 ≤ 1 (true since 0 is the second arg)
          · -- ¬(J.lo ≤ 0), ¬(1 ≤ 1) - impossible
            exfalso; linarith
        -- M' * |z|^(n+1) / (n+1)! = |z|^(n+1) / ((n+1) * (1+a')^(n+1))
        have hstep : M' * |z|^(n+1) / (n+1).factorial = |z|^(n+1) / ((n+1) * (1 + a')^(n+1)) := by
          simp only [M', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          have h1pa'_pow_ne : (1 + a')^(n+1) ≠ 0 := pow_ne_zero _ (ne_of_gt h1pa'_pos)
          have hn1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
          have hnfact_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          field_simp [h1pa'_pow_ne, hn1_ne, hnfact_ne]
        rw [hstep]
        -- |z| ≤ radius = max |J.lo| |J.hi|
        set radius : ℚ := max (|J.lo|) (|J.hi|)
        have habs_z_le : |z| ≤ (radius : ℝ) := by
          simp only [radius, Rat.cast_max, Rat.cast_abs]
          have hz' := hz
          simp only [IntervalRat.mem_def] at hz'
          rcases le_or_gt 0 z with hz_nonneg | hz_neg
          · rw [abs_of_nonneg hz_nonneg]
            apply le_max_of_le_right
            have hhi_nonneg : 0 ≤ (J.hi : ℝ) := le_trans hz_nonneg hz'.2
            rw [abs_of_nonneg hhi_nonneg]
            exact hz'.2
          · rw [abs_of_neg hz_neg]
            apply le_max_of_le_left
            have hJlo_neg : (J.lo : ℝ) < 0 := lt_of_le_of_lt hz'.1 hz_neg
            rw [abs_of_neg hJlo_neg]
            linarith [hz'.1]
        -- Now the bound follows
        simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast,
          Rat.cast_min, Rat.cast_add, Rat.cast_one]
        rw [h1pa'_eq]
        have hmin_pos : (0 : ℝ) < min 1 (1 + a) := lt_min one_pos (by linarith)
        have hdenom_pos : 0 < (n + 1 : ℝ) * (min 1 (1 + a))^(n+1) := mul_pos (by positivity) (pow_pos hmin_pos _)
        apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
        exact pow_le_pow_left₀ (abs_nonneg _) habs_z_le _

/-- log(1+z) ∈ (tmLog1p J n).evalSet z for all z in J when J.lo > -1. -/
theorem tmLog1p_correct (J : IntervalRat) (n : ℕ)
    (tm : TaylorModel) (h : tmLog1p J n = some tm) :
    ∀ z : ℝ, z ∈ J → Real.log (1 + z) ∈ tm.evalSet z := by
  intro z hz
  simp only [tmLog1p] at h
  split_ifs at h with hdom
  simp only [Option.some.injEq] at h
  subst h
  simp only [evalSet, Set.mem_setOf_eq]
  -- For log(1+z) centered at 0:
  -- - Taylor polynomial: Σ_{k=1}^n (-1)^(k+1) z^k / k
  -- - Remainder: log(1+z) - Σ_{k=1}^n (-1)^(k+1) z^k / k
  -- - log(1+0) = log(1) = 0, so no center approximation error
  let poly := log1pTaylorPoly n
  let rem := log1pLagrangeRemainder J n
  let r := Real.log (1 + z) - Polynomial.aeval z (poly.map (algebraMap ℚ ℝ))
  refine ⟨r, ?_, ?_⟩
  · -- Show r ∈ [-rem, rem]
    simp only [IntervalRat.mem_def, Rat.cast_neg]
    -- Use log1p_taylor_remainder_bound to bound |r|
    have hbound := log1p_taylor_remainder_bound J n z hdom hz
    simp only [r, poly] at hbound ⊢
    rw [abs_le] at hbound
    exact hbound
  · -- Show log(1+z) = poly.aeval z + r
    simp only [r, poly]
    rw [Polynomial.aeval_map_algebraMap]
    ring_nf

/-! ### Symmetric combination bound for li(x)

The key insight: g(t) = 1/log(1+t) + 1/log(1-t) is bounded for t ∈ (0, 1).

Algebraically:
  g(t) = [log(1-t) + log(1+t)] / [log(1+t) · log(1-t)]
       = log(1-t²) / [log(1+t) · log(1-t)]

Using Taylor expansions:
  log(1+t) = t - t²/2 + t³/3 - ...
  log(1-t) = -t - t²/2 - t³/3 - ...
  log(1-t²) = -t² - t⁴/2 - t⁶/3 - ...

Numerator: log(1-t²) = -t² · (1 + t²/2 + t⁴/3 + ...)
Denominator: log(1+t) · log(1-t) = (t - t²/2 + ...)(-t - t²/2 - ...)
           = -t² + t⁴/4 + ... = -t² · (1 - t²/4 - ...)

So g(t) = [-t² · (1 + O(t²))] / [-t² · (1 + O(t²))] = 1 + O(t²)

More precisely: g(t) = [1 + t²/2 + O(t⁴)] / [1 - t²/4 + O(t⁴)] → 1 as t → 0
-/

/-- The symmetric combination g(t) = 1/log(1+t) + 1/log(1-t).
    This is well-defined for t ∈ (0, 1) despite the apparent singularity at t = 0. -/
noncomputable def symmetricLogCombination (t : ℝ) : ℝ :=
  1 / Real.log (1 + t) + 1 / Real.log (1 - t)

/-- Alternative form: g(t) = log(1-t²) / (log(1+t) · log(1-t)) -/
theorem symmetricLogCombination_alt (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    symmetricLogCombination t = Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) := by
  unfold symmetricLogCombination
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have hlog1p_pos : Real.log (1 + t) > 0 := Real.log_pos (by linarith : 1 < 1 + t)
  have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg (by linarith) (by linarith : 1 - t < 1)
  have hlog1p_ne : Real.log (1 + t) ≠ 0 := ne_of_gt hlog1p_pos
  have hlog1m_ne : Real.log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
  -- log(1-t²) = log((1-t)(1+t)) = log(1-t) + log(1+t)
  have hlog_prod : Real.log (1 - t^2) = Real.log (1 - t) + Real.log (1 + t) := by
    have h : 1 - t^2 = (1 - t) * (1 + t) := by ring
    rw [h, Real.log_mul (ne_of_gt h1mt_pos) (ne_of_gt h1pt_pos)]
  rw [hlog_prod]
  field_simp

/-- Helper: log(1+t)/t → 1 as t → 0.
    This follows from log'(1) = 1. -/
theorem tendsto_log_one_add_div_self :
    Filter.Tendsto (fun t => Real.log (1 + t) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- Follows from log'(1) = 1 via hasDerivAt_iff_tendsto_slope_zero
  -- (log(1+t) - log(1))/t = log(1+t)/t → 1 as t → 0
  have hderiv : HasDerivAt Real.log 1 1 := by
    have h := Real.hasDerivAt_log (one_ne_zero)
    simp only [inv_one] at h
    exact h
  have htendsto := hderiv.tendsto_slope_zero_right
  -- htendsto: Tendsto (fun t => t⁻¹ • (log(1 + t) - log 1)) (𝓝[>] 0) (𝓝 1)
  simp only [Real.log_one, sub_zero, smul_eq_mul, inv_mul_eq_div] at htendsto
  exact htendsto

/-- Helper: log(1-t)/t → -1 as t → 0⁺. -/
theorem tendsto_log_one_sub_div_self :
    Filter.Tendsto (fun t => Real.log (1 - t) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero)
    have hneg : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)
    have hlog' : HasDerivAt Real.log 1 (1 - 0) := by simp only [sub_zero]; exact hlog
    simpa using hlog'.comp 0 hneg
  have htendsto := hderiv.tendsto_slope_zero_right
  simp only [sub_zero, Real.log_one, smul_eq_mul, inv_mul_eq_div] at htendsto
  convert htendsto using 2 with t
  ring_nf

/-- Helper: log(1-t²)/t² → -1 as t → 0⁺. -/
theorem tendsto_log_one_sub_sq_div_sq :
    Filter.Tendsto (fun t => Real.log (1 - t^2) / t^2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  -- log(1-u)/u → -1 as u → 0⁺, with u = t²
  -- Compose tendsto_log_one_sub_div_self with t ↦ t²
  have h := tendsto_log_one_sub_div_self
  -- Need: t ↦ t² maps 𝓝[>]0 to 𝓝[>]0
  have hsq : Filter.Tendsto (fun t : ℝ => t^2) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Filter.Tendsto (fun t : ℝ => t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      simp only [sq]
      have hmul := h0.mul h0
      simp only [mul_zero] at hmul
      exact hmul
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sq_pos_of_pos (Set.mem_Ioi.mp ht)
  exact h.comp hsq

/-- The limit as t → 0⁺ of g(t) is 1.

    Proof using the key identity and limits:
    g(t) = log(1-t²) / (log(1+t) · log(1-t))
         = [log(1-t²)/t²] / [(log(1+t)/t) · (log(1-t)/t)]

    As t → 0⁺:
    - log(1-t²)/t² → -1
    - log(1+t)/t → 1
    - log(1-t)/t → -1

    So g(t) → (-1) / (1 · (-1)) = 1
-/
theorem symmetricLogCombination_tendsto_one :
    Filter.Tendsto symmetricLogCombination (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- Use the alternative form for t ∈ (0, 1)
  have heventually : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), symmetricLogCombination t =
      Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) := by
    rw [Filter.eventually_iff_exists_mem]
    use Set.Ioo 0 1
    constructor
    · rw [mem_nhdsWithin]
      use Set.Iio 1
      refine ⟨isOpen_Iio, ?_, ?_⟩
      · norm_num
      · intro x ⟨hx1, hx2⟩
        exact ⟨hx2, hx1⟩  -- hx2 : x ∈ Ioi 0 = (0 < x), hx1 : x ∈ Iio 1 = (x < 1)
    · intro t ht
      exact symmetricLogCombination_alt t ht.1 ht.2
  apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm heventually)
  -- Rewrite as ratio: [log(1-t²)/t²] / [(log(1+t)/t) · (log(1-t)/t)]
  have hrewrite : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) =
      (Real.log (1 - t^2) / t^2) / ((Real.log (1 + t) / t) * (Real.log (1 - t) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_ne : t ≠ 0 := ne_of_gt ht
    field_simp
  apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm hrewrite)
  -- Apply the limits
  have h1 := tendsto_log_one_sub_sq_div_sq  -- log(1-t²)/t² → -1
  have h2 := tendsto_log_one_add_div_self   -- log(1+t)/t → 1
  have h3 := tendsto_log_one_sub_div_self   -- log(1-t)/t → -1
  -- The product (log(1+t)/t) * (log(1-t)/t) → 1 * (-1) = -1
  have hprod : Filter.Tendsto (fun t => (Real.log (1 + t) / t) * (Real.log (1 - t) / t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
    have := h2.mul h3
    simp only [one_mul] at this
    exact this
  -- The ratio (-1) / (-1) = 1
  have hdiv : Filter.Tendsto (fun t => (Real.log (1 - t^2) / t^2) /
      ((Real.log (1 + t) / t) * (Real.log (1 - t) / t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hne : (-1 : ℝ) ≠ 0 := by norm_num
    have := h1.div hprod hne
    simp only [neg_div_neg_eq, div_one] at this
    exact this
  exact hdiv

/-- Symmetric combination bound: |g(t)| ≤ C for t ∈ (0, δ) where δ < 1.

For small t, using Taylor analysis:
  g(t) = 1 + t²/2 · (1/log(1-t²) - 1/log(1+t) - 1/log(1-t)) + O(t⁴)

A crude but sufficient bound: for t ∈ (0, 1/2), |g(t)| ≤ 2.
This can be refined using Taylor model arithmetic.
-/
theorem symmetricLogCombination_bounded (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1/2) :
    |symmetricLogCombination t| ≤ 2 := by
  -- Use the limit g(t) → 1 to show |g(t) - 1| < 1 near 0, hence |g(t)| < 2.
  -- By symmetricLogCombination_tendsto_one, we have g(t) → 1 as t → 0⁺
  -- Use Metric.tendsto_nhds: ∀ ε > 0, ∃ δ > 0, 0 < t < δ → |g(t) - 1| < ε
  have hlim := symmetricLogCombination_tendsto_one
  rw [Metric.tendsto_nhds] at hlim
  specialize hlim 1 one_pos
  -- hlim : ∀ᶠ t in 𝓝[>]0, dist (g t) 1 < 1
  rw [Filter.eventually_iff_exists_mem] at hlim
  obtain ⟨s, hs_mem, hs⟩ := hlim
  -- s is a neighborhood of 0 in (0, ∞) where |g(t) - 1| < 1
  rw [mem_nhdsWithin] at hs_mem
  obtain ⟨U, hU_open, hU_zero, hU_sub⟩ := hs_mem
  -- U is an open set containing 0, and s ⊇ U ∩ (0, ∞)
  rw [Metric.isOpen_iff] at hU_open
  specialize hU_open 0 hU_zero
  obtain ⟨ε, hε_pos, hε_ball⟩ := hU_open
  -- For t ∈ (0, ε), t is in U ∩ (0, ∞) ⊆ s, so |g(t) - 1| < 1
  by_cases ht_small : t < ε
  · -- Case 1: t < ε, use the limit
    have ht_in_U : t ∈ U := hε_ball (by simp [abs_of_pos ht_pos, ht_small])
    have ht_in_s : t ∈ s := hU_sub ⟨ht_in_U, Set.mem_Ioi.mpr ht_pos⟩
    have hdist := hs t ht_in_s
    rw [Real.dist_eq] at hdist
    have h1 : |symmetricLogCombination t| = |(symmetricLogCombination t - 1) + 1| := by ring_nf
    have h2 : |(symmetricLogCombination t - 1) + 1| ≤ |symmetricLogCombination t - 1| + |1| := abs_add_le _ _
    have h3 : |symmetricLogCombination t - 1| + |1| < 1 + 1 := by simp only [abs_one]; linarith
    linarith
  · -- Case 2: t ∈ [ε, 1/2), bound using explicit log inequalities
    push_neg at ht_small
    -- Strategy: Show g(t) ∈ (0, 2) for t ∈ (0, 1/2] using:
    -- 1. g(t) > 0 (ratio of two negatives)
    -- 2. g(t) < 2 using log bounds
    have halt := symmetricLogCombination_alt t ht_pos (by linarith : t < 1)
    rw [halt]
    have ht2_lt : t^2 < 1 := by nlinarith
    have h1mt2_pos : 0 < 1 - t^2 := by linarith [sq_nonneg t]
    have h1pt_gt1 : 1 < 1 + t := by linarith
    have h1mt_lt1 : 1 - t < 1 := by linarith
    have h1mt_pos : 0 < 1 - t := by linarith
    have hlog1p_pos : 0 < Real.log (1 + t) := Real.log_pos h1pt_gt1
    have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg h1mt_pos h1mt_lt1
    have h1mt2_lt1 : 1 - t^2 < 1 := by nlinarith [sq_nonneg t]
    have hlog1mt2_neg : Real.log (1 - t^2) < 0 := Real.log_neg h1mt2_pos h1mt2_lt1
    have hdenom_neg : Real.log (1 + t) * Real.log (1 - t) < 0 := mul_neg_of_pos_of_neg hlog1p_pos hlog1m_neg
    have hdenom_ne : Real.log (1 + t) * Real.log (1 - t) ≠ 0 := ne_of_lt hdenom_neg
    -- g(t) = log(1-t²)/(log(1+t)·log(1-t)) = (neg)/(neg) > 0
    have hg_pos : 0 < Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) := by
      apply div_pos_of_neg_of_neg hlog1mt2_neg hdenom_neg
    -- For |g| ≤ 2, since g > 0, we need g ≤ 2
    -- Using log(1-t²) = log(1+t) + log(1-t) and explicit bounds:
    -- g = (log(1+t) + log(1-t))/(log(1+t)·log(1-t))
    --   = 1/log(1-t) + 1/log(1+t)
    --   = 1/log(1-t) + 1/log(1+t)
    -- For t ∈ (0, 1/2]:
    --   1/log(1+t) ∈ (1/log(3/2), ∞) ≈ (2.47, ∞)  [positive]
    --   1/log(1-t) ∈ (-∞, 1/log(1/2)) ≈ (-∞, -1.44)  [negative]
    -- Sum: bounded above by 2.47 - 1.44 = 1.03 at t = 1/2
    -- The function is continuous and numerically verified to be < 2
    -- This requires interval arithmetic for a rigorous proof
    rw [abs_of_pos hg_pos]
    -- Use log bounds to show g(t) ≤ 2:
    -- From one_sub_inv_le_log_of_pos with x = 1+t: t/(1+t) ≤ log(1+t), so 1/log(1+t) ≤ (1+t)/t
    -- From one_sub_inv_le_log_of_pos with x = 1-t: -t/(1-t) ≤ log(1-t), so 1/log(1-t) ≤ -(1-t)/t
    -- Thus g(t) = 1/log(1+t) + 1/log(1-t) ≤ (1+t)/t - (1-t)/t = 2
    have h1pt_pos : 0 < 1 + t := by linarith
    have h1pt_ne : 1 + t ≠ 0 := ne_of_gt h1pt_pos
    have h1mt_ne : 1 - t ≠ 0 := ne_of_gt h1mt_pos
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have hlog1p_lb : t / (1 + t) ≤ Real.log (1 + t) := by
      have h := Real.one_sub_inv_le_log_of_pos h1pt_pos
      simp only [inv_eq_one_div] at h
      convert h using 1
      field_simp; ring
    have hlog1m_ub : Real.log (1 - t) ≥ -t / (1 - t) := by
      have h := Real.one_sub_inv_le_log_of_pos h1mt_pos
      simp only [inv_eq_one_div] at h
      have heq : 1 - 1 / (1 - t) = -t / (1 - t) := by field_simp; ring
      rw [← heq]; exact h
    -- Bound 1/log(1+t)
    have hlog1p_inv_ub : 1 / Real.log (1 + t) ≤ (1 + t) / t := by
      rw [one_div, le_div_iff₀ ht_pos, inv_mul_le_iff₀ hlog1p_pos]
      have h1 : t = t / (1 + t) * (1 + t) := by field_simp
      calc t = t / (1 + t) * (1 + t) := h1
        _ ≤ Real.log (1 + t) * (1 + t) := by
            apply mul_le_mul_of_nonneg_right hlog1p_lb (le_of_lt h1pt_pos)
    -- Bound 1/log(1-t)
    have hlog1m_inv_ub : 1 / Real.log (1 - t) ≤ -(1 - t) / t := by
      have hneg_log : -Real.log (1 - t) > 0 := neg_pos.mpr hlog1m_neg
      -- From log(1-t) ≥ -t/(1-t), we get -log(1-t) ≤ t/(1-t)
      have hneg_log_ub : -Real.log (1 - t) ≤ t / (1 - t) := by
        have h := hlog1m_ub
        have hdiv_neg : -t / (1 - t) = -(t / (1 - t)) := by ring
        rw [hdiv_neg] at h
        linarith
      -- So 1/(-log(1-t)) ≥ (1-t)/t
      have hinv_lb : (1 - t) / t ≤ 1 / (-Real.log (1 - t)) := by
        rw [div_le_div_iff₀ ht_pos hneg_log]
        calc (1 - t) * -Real.log (1 - t) = -Real.log (1 - t) * (1 - t) := by ring
          _ ≤ t / (1 - t) * (1 - t) := mul_le_mul_of_nonneg_right hneg_log_ub (le_of_lt h1mt_pos)
          _ = t := by field_simp
          _ = 1 * t := by ring
      -- Thus 1/log(1-t) = -1/(-log(1-t)) ≤ -(1-t)/t
      have hlog1m_ne : Real.log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
      calc 1 / Real.log (1 - t) = -(1 / -Real.log (1 - t)) := by field_simp [hlog1m_ne]
        _ ≤ -((1 - t) / t) := neg_le_neg hinv_lb
        _ = -(1 - t) / t := by ring
    -- Combine bounds
    have halt' : Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) =
        1 / Real.log (1 + t) + 1 / Real.log (1 - t) := by
      have hlog_prod : Real.log (1 - t^2) = Real.log (1 - t) + Real.log (1 + t) := by
        have h : 1 - t^2 = (1 - t) * (1 + t) := by ring
        rw [h, Real.log_mul (ne_of_gt h1mt_pos) (ne_of_gt h1pt_pos)]
      rw [hlog_prod]
      field_simp [ne_of_gt hlog1p_pos, ne_of_lt hlog1m_neg]
    rw [halt']
    calc 1 / Real.log (1 + t) + 1 / Real.log (1 - t)
        ≤ (1 + t) / t + (-(1 - t) / t) := add_le_add hlog1p_inv_ub hlog1m_inv_ub
      _ = ((1 + t) - (1 - t)) / t := by ring
      _ = 2 * t / t := by ring
      _ = 2 := by field_simp

/-! ### Summary of proven results for the li(2) computation

**All proofs complete (no sorry):**
- `log1pTaylorPoly_aeval_eq_sum`: Polynomial evaluation equals Taylor sum
- `log1p_taylor_remainder_bound`: Taylor remainder is bounded by Lagrange form
- `tmLog1p_correct`: Taylor model correctness for log(1+x)
- `symmetricLogCombination_alt`: g(t) = log(1-t²)/(log(1+t)·log(1-t))
- `tendsto_log_one_add_div_self`: log(1+t)/t → 1 as t → 0⁺
- `tendsto_log_one_sub_div_self`: log(1-t)/t → -1 as t → 0⁺
- `tendsto_log_one_sub_sq_div_sq`: log(1-t²)/t² → -1 as t → 0⁺
- `symmetricLogCombination_tendsto_one`: g(t) → 1 as t → 0⁺ (KEY RESULT)
- `symmetricLogCombination_bounded`: |g(t)| ≤ 2 for t ∈ (0, 1/2]
  - Case 1: near 0, uses continuity and limit → 1
  - Case 2: on [ε, 1/2], uses log bounds: log(1+t) ≥ t/(1+t), -log(1-t) ≤ t/(1-t)

The key insight for the li(2) computation is `symmetricLogCombination_tendsto_one`:
the symmetric combination g(t) = 1/log(1+t) + 1/log(1-t) has a REMOVABLE
SINGULARITY at t=0, with limit 1. This makes the principal value integral
for li(2) = ∫₀¹ g(t) dt absolutely convergent.
-/

end TaylorModel

end LeanCert.Engine
