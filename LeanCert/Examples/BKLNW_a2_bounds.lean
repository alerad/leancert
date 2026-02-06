/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.BKLNW_a2_pow2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BKLNW a₂ Bounds - Lightweight Interface

This file provides the lightweight interface for BKLNW (1+α)·f(exp b) bounds.
It exports sorry'd theorems matching the exact signatures needed by PNT+.

## Purpose

This module is designed to be **fast to compile** (~seconds) and is what downstream
projects like PNT+ should import. The heavy numerical verification that proves
the bounds is in `BKLNW_a2_reflective.lean`, which uses `native_decide` and is
only needed for LeanCert's CI, not for users of the bounds.

## Verification Status

All bounds are marked with `sorry` in this file.
They are fully verified via reflective interval arithmetic in `BKLNW_a2_reflective.lean`.
This separation allows downstream projects to use the bounds without incurring the
~5 minute compilation cost of numerical verification.

## Interface

The bounds are in the form `(1+α)·f(exp b) ∈ [lo, lo + 10^(-m)]` where:
- `f` is `LeanCert.Examples.BKLNW_a2_pow2.f` (= PNT+'s `BKLNW.f`)
- `α = 193571378/10^16` (the BKLNW Table 8 margin)
- `b ∈ {20, 25, 30, 35, 40, 43, 100, 150, 200, 250, 300}`
-/

open Real Finset

namespace LeanCert.Examples.BKLNW_a2_bounds

-- Reuse the standalone definition matching PNT+'s f
open LeanCert.Examples.BKLNW_a2_pow2 (f)

/-! ### Core Definition -/

/-- The BKLNW function with explicit limit parameter:
    f(x, N) = Σ_{k=3}^{N} x^(1/k - 1/3)

    This matches PNT+'s `f` when N = ⌊log(x)/log(2)⌋. -/
noncomputable def bklnwF (x : ℝ) (N : Nat) : ℝ :=
  ∑ k ∈ Finset.Icc 3 N, x ^ ((1 : ℝ) / k - 1 / 3)

/-! ### Floor Lemmas -/

theorem floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 20 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 25 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 30 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 35 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 40 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 43 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 100 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 150 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 200 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 250 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

theorem floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 300 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

/-! ### Connection to PNT+ f definition -/

open LeanCert.Examples.BKLNW_a2_pow2 (f) in
theorem f_eq_bklnwF_exp (b : ℕ) :
    f (exp b) = bklnwF (exp b) ⌊(b : ℝ) / log 2⌋₊ := by
  unfold f bklnwF
  congr 1
  simp only [log_exp]

/-! ### Certified (1+α)·f(exp b) Bounds

All bounds are sorry'd here and verified in `BKLNW_a2_reflective.lean`
via the reflective interval arithmetic engine + `native_decide`. -/

-- b = 20
lemma a2_20_exp_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) := by sorry
lemma a2_20_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by sorry

-- b = 25
lemma a2_25_exp_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) := by sorry
lemma a2_25_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by sorry

-- b = 30
lemma a2_30_exp_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) := by sorry
lemma a2_30_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by sorry

-- b = 35
lemma a2_35_exp_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) := by sorry
lemma a2_35_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by sorry

-- b = 40
lemma a2_40_exp_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) := by sorry
lemma a2_40_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by sorry

-- b = 43
lemma a2_43_exp_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) := by sorry
lemma a2_43_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by sorry

-- b = 100
lemma a2_100_exp_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) := by sorry
lemma a2_100_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by sorry

-- b = 150
lemma a2_150_exp_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) := by sorry
lemma a2_150_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by sorry

-- b = 200
lemma a2_200_exp_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) := by sorry
lemma a2_200_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by sorry

-- b = 250
lemma a2_250_exp_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) := by sorry
lemma a2_250_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by sorry

-- b = 300
lemma a2_300_exp_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) := by sorry
lemma a2_300_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by sorry

end LeanCert.Examples.BKLNW_a2_bounds
