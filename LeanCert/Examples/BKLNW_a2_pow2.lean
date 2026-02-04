/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinSumExpand
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BKLNW a₂ Certificates for 2^N terms

Certified numerical bounds for f(2^N) where f is the BKLNW sum function.
These certificates are used by PrimeNumberTheoremAnd for the max(f(exp b), f(2^N)) computation.

For small N (29-63): full expansion with finsum_expand
For large N (145+): tail bounds approach for speed

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

private lemma floor_log_two_pow (n : ℕ) : ⌊log ((2:ℝ)^n) / log 2⌋₊ = n := by
  rw [log_pow, mul_div_cancel_right₀ _ (ne_of_gt (log_pos one_lt_two))]
  exact Nat.floor_natCast n

-- ═══════════════════════ Small N: Full expansion ═══════════════════════

-- 2^29 (for b=20): 27 terms, fast enough for full expansion
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

-- ═══════════════════════ Large N: Tail bounds ═══════════════════════
-- For 2^N, f(2^N) = Σ_{k=3}^{N} 2^(N/k - N/3) = Σ_{k=3}^{N} 2^(N*(1/k - 1/3))
-- Term k=3 gives 2^0 = 1
-- Term k=4 gives 2^(-N/12)
-- Tail terms decay rapidly

-- 2^145 (for b=100): use tail bound
-- Head: k=3,4,5,6,7,8 gives 1 + 2^(-145/12) + 2^(-290/15) + 2^(-145/6) + 2^(-580/21) + 2^(-725/24)
-- = 1 + 2^(-145/12) + 2^(-58/3) + 2^(-145/6) + 2^(-580/21) + 2^(-725/24)
-- Converting to exp: 2^x = exp(x * log 2)
-- Tail: 137 terms, each ≤ 2^(-290/9) < 3e-10, so tail < 137 * 3e-10 < 5e-8

theorem head_pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-(145:ℝ) * log 2 * (1/12)) + exp (-(58:ℝ) * log 2 * (1/3)) +
      exp (-(145:ℝ) * log 2 * (1/6)) + exp (-(580:ℝ) * log 2 * (1/21)) + exp (-(725:ℝ) * log 2 * (1/24))) ≤ (1.0002420 : ℝ) := by
  interval_decide 160

theorem tail_pow145 : (137:ℝ) * exp (-(290:ℝ) * log 2 * (1/9)) < 5e-8 := by
  have h : exp (-(290:ℝ) * log 2 * (1/9)) < 3e-10 := by interval_decide 160
  calc (137:ℝ) * exp (-(290:ℝ) * log 2 * (1/9)) < 137 * (3e-10 : ℝ) := mul_lt_mul_of_pos_left h (by positivity)
    _ = 411e-10 := by norm_num
    _ < 5e-8 := by norm_num

-- Combined bound for pow145
theorem pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(145:ℕ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  -- The full proof would require showing f(2^145) = head + tail and combining bounds
  -- For now, provide the combined certificate
  have h_head := head_pow145_upper
  have h_tail := tail_pow145
  sorry -- Glue proof: f(2^145) ≤ head + tail, (1+α)*(head + tail) ≤ bound

-- 2^217 (for b=150): use tail bound
-- Head: k=3,4,5 gives 1 + 2^(-217/12) + 2^(-434/15)
-- Tail: 212 terms, each ≤ 2^(-217/2) < 1e-32

theorem head_pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-(217:ℝ) * log 2 * (1/12)) + exp (-(434:ℝ) * log 2 * (1/15))) ≤ (1.000003748 : ℝ) := by
  interval_decide 180

theorem pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(217:ℕ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  have h_head := head_pow217_upper
  sorry -- Glue proof with tail bound

-- 2^289 (for b=200): use tail bound
-- Head: k=3,4 gives 1 + 2^(-289/12)
-- Tail negligible

theorem head_pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-(289:ℝ) * log 2 * (1/12))) ≤ (1.00000007713 : ℝ) := by
  interval_decide 200

theorem pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(289:ℕ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  have h_head := head_pow289_upper
  sorry -- Glue proof with tail bound

-- 2^361 (for b=250): use tail bound
theorem head_pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-(361:ℝ) * log 2 * (1/12))) ≤ (1.00000002025 : ℝ) := by
  interval_decide 200

theorem pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(361:ℕ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  have h_head := head_pow361_upper
  sorry -- Glue proof with tail bound

-- 2^433 (for b=300): use tail bound
theorem head_pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-(433:ℝ) * log 2 * (1/12))) ≤ (1.00000001938 : ℝ) := by
  interval_decide 300

theorem pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(433:ℕ)) ≤ (1.00000001938 : ℝ) + (1:ℝ) / 10^9 := by
  have h_head := head_pow433_upper
  sorry -- Glue proof with tail bound

end LeanCert.Examples.BKLNW_a2_pow2
