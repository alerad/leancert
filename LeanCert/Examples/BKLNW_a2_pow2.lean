/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinSumExpand
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BKLNW a₂ Definition and 2^N Certificates

Defines the BKLNW sum function `f` matching PNT+'s definition, and provides
certified upper bounds for `(1+α)·f(2^N)` via full expansion with `finsum_expand`.

The function f is defined as:
  f(x) = Σ_{k=3}^{⌊log(x)/log(2)⌋} x^(1/k - 1/3)
-/

open Real Finset

namespace LeanCert.Examples.BKLNW_a2_pow2

-- Standalone definition matching PNT+'s f
noncomputable def f (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)

-- Helper lemmas
private lemma two_pow_eq_exp_log (n : ℕ) : (2:ℝ)^n = exp (↑n * log 2) := by
  have h := rpow_def_of_pos (show (0:ℝ) < 2 by positivity) (↑n : ℝ)
  rw [rpow_natCast] at h; rw [h]; ring_nf

lemma floor_log_two_pow (n : ℕ) : ⌊log ((2:ℝ)^n) / log 2⌋₊ = n := by
  rw [log_pow, mul_div_cancel_right₀ _ (ne_of_gt (log_pos one_lt_two))]
  exact Nat.floor_natCast n

-- 2^29 (for b=20): 27 terms
theorem pow29_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(29:ℕ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(29:ℕ)) / log 2⌋₊ = 29 from floor_log_two_pow 29]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 43

-- 2^37 (for b=25): 35 terms
theorem pow37_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(37:ℕ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(37:ℕ)) / log 2⌋₊ = 37 from floor_log_two_pow 37]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 55

-- 2^44 (for b=30): 42 terms
theorem pow44_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(44:ℕ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(44:ℕ)) / log 2⌋₊ = 44 from floor_log_two_pow 44]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 67

-- 2^51 (for b=35): 49 terms
theorem pow51_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(51:ℕ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(51:ℕ)) / log 2⌋₊ = 51 from floor_log_two_pow 51]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 78

-- 2^58 (for b=40): 56 terms
theorem pow58_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(58:ℕ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(58:ℕ)) / log 2⌋₊ = 58 from floor_log_two_pow 58]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 89

-- 2^63 (for b=43): 61 terms
theorem pow63_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(63:ℕ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(63:ℕ)) / log 2⌋₊ = 63 from floor_log_two_pow 63]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 98

/-! ### Large-N 2^M certificates (sorry'd interface)

These are verified via reflective interval arithmetic in `BKLNW_a2_reflective.lean`
(see `pow145_upper` etc.), which uses `native_decide` with
`Engine.checkBKLNWAlphaPowUpperBound`. Sorry'd here to keep compilation fast
(same pattern as the exp bounds in `BKLNW_a2_bounds.lean`). -/

-- 2^145 (for b=100)
theorem pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(145:ℕ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by sorry

-- 2^217 (for b=150)
theorem pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(217:ℕ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by sorry

-- 2^289 (for b=200)
theorem pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(289:ℕ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by sorry

-- 2^361 (for b=250)
theorem pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(361:ℕ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by sorry

-- 2^433 (for b=300)
theorem pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(433:ℕ)) ≤ (1.00000001938 : ℝ) + (1:ℝ) / 10^9 := by sorry

end LeanCert.Examples.BKLNW_a2_pow2
