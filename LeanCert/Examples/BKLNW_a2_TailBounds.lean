/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BKLNW a₂ Tail Bound Certificates for b=100-300

For large b, the sum f(x) = Σ_{k=3}^N x^{1/k-1/3} has many terms but only the
first few are significant. We use:
- Head: explicit sum of first K-2 terms (k=3..K)
- Tail bound: (N-K) * x^{1/(K+1)-1/3}

This reduces b=100 from 144 terms to 6 terms, b=200-300 to just 2 terms.
-/

open Real

namespace LeanCert.Examples.BKLNW_a2_TailBounds

-- ═══════════════════════ b=100 ═══════════════════════
-- N = 144 terms, K_head = 8 (6 explicit head terms k=3..8)
-- Head: 1 + exp(-25/3) + exp(-40/3) + exp(-50/3) + exp(-400/21) + exp(-125/6)
-- Tail: 136 terms bounded by 136 * exp(-200/9) ≈ 3e-8

theorem head_100_lower : (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6)) := by
  interval_decide 160

theorem head_100_upper : (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6)) ≤ (1.0002421 : ℝ) := by
  interval_decide 160

theorem tail_100 : (136:ℝ) * exp (-200/9) < 5e-8 := by
  have h : exp (-200/9 : ℝ) < 3e-10 := by interval_decide 160
  calc (136:ℝ) * exp (-200/9) < 136 * (3e-10 : ℝ) := mul_lt_mul_of_pos_left h (by positivity)
    _ = 408e-10 := by norm_num
    _ < 5e-8 := by norm_num

-- ═══════════════════════ b=150 ═══════════════════════
-- N = 216 terms, K_head = 5 (3 explicit head terms k=3..5)
-- Head: 1 + exp(-25/2) + exp(-20)
-- Tail: 211 terms bounded by 211 * exp(-25) ≈ 3e-9
-- Note: with alpha factor, head ≈ 1.000003748

theorem head_150_lower : (1.000003747 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-25/2) + exp (-20)) := by
  interval_decide 150

theorem head_150_upper : (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-25/2) + exp (-20)) ≤ (1.000003749 : ℝ) := by
  interval_decide 150

theorem tail_150 : (211:ℝ) * exp (-25) < 5e-9 := by
  have h : exp (-25 : ℝ) < 2e-11 := by interval_decide 200
  calc (211:ℝ) * exp (-25) < 211 * (2e-11 : ℝ) := mul_lt_mul_of_pos_left h (by positivity)
    _ = 422e-11 := by norm_num
    _ < 5e-9 := by norm_num

-- ═══════════════════════ b=200 ═══════════════════════
-- N = 288 terms, K_head = 4 (2 explicit head terms k=3..4)
-- Head: 1 + exp(-50/3)
-- Tail: 284 terms bounded by 284 * exp(-80/3) ≈ 8e-10
-- Note: with alpha factor, head ≈ 1.000000077

theorem head_200_lower : (1.000000076 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-50/3)) := by
  interval_decide 150

theorem head_200_upper : (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-50/3)) ≤ (1.000000078 : ℝ) := by
  interval_decide 150

theorem tail_200 : (284:ℝ) * exp (-80/3) < 1e-9 := by
  have h : exp (-80/3 : ℝ) < 3e-12 := by interval_decide 200
  calc (284:ℝ) * exp (-80/3) < 284 * (3e-12 : ℝ) := mul_lt_mul_of_pos_left h (by positivity)
    _ = 852e-12 := by norm_num
    _ < 1e-9 := by norm_num

-- ═══════════════════════ b=250 ═══════════════════════
-- N = 360 terms, K_head = 4 (2 explicit head terms k=3..4)
-- Head: 1 + exp(-125/6)
-- Tail: 356 terms bounded by 356 * exp(-100/3) ≈ 1.2e-12
-- Note: with alpha factor, head ≈ 1.000000020

theorem head_250_lower : (1.000000019 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-125/6)) := by
  interval_decide 150

theorem head_250_upper : (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-125/6)) ≤ (1.000000021 : ℝ) := by
  interval_decide 150

theorem tail_250 : (356:ℝ) * exp (-100/3) < 2e-12 := by
  have h : exp (-100/3 : ℝ) < 4e-15 := by interval_decide 250
  calc (356:ℝ) * exp (-100/3) < 356 * (4e-15 : ℝ) := mul_lt_mul_of_pos_left h (by positivity)
    _ = 1424e-15 := by norm_num
    _ < 2e-12 := by norm_num

-- ═══════════════════════ b=300 ═══════════════════════
-- N = 432 terms, K_head = 4 (2 explicit head terms k=3..4)
-- Head: 1 + exp(-25)
-- Tail: 428 terms bounded by 428 * exp(-40) ≈ 2e-15
-- Note: with alpha factor, head ≈ 1.000000019

theorem head_300_lower : (1.000000018 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-25)) := by
  interval_decide 200

theorem head_300_upper : (1 + 193571378 / (10:ℝ)^16) *
    (1 + exp (-25)) ≤ (1.000000020 : ℝ) := by
  interval_decide 200

theorem tail_300 : (428:ℝ) * exp (-40) < 3e-15 := by
  have h : exp (-40 : ℝ) < 5e-18 := by interval_decide 300
  calc (428:ℝ) * exp (-40) < 428 * (5e-18 : ℝ) := mul_lt_mul_of_pos_left h (by positivity)
    _ = 2140e-18 := by norm_num
    _ < 3e-15 := by norm_num

end LeanCert.Examples.BKLNW_a2_TailBounds
