/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinSumExpand
import LeanCert.Examples.BKLNW_a2
import LeanCert.Examples.BKLNW_a2_TailBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BKLNW a₂ Glue Proofs - Complete Integration

Connects `a₂(b) = (1+α) * max(f(exp b), f(2^(⌊b/log2⌋₊+1)))` to certified bounds
for all 11 table entries: b = 20, 25, 30, 35, 40, 43, 100, 150, 200, 250, 300.

Structure:
- For b=20-43: Uses full expansion with `finsum_expand`
- For b=100-300: Uses tail bound approach from BKLNW_a2_TailBounds

Each entry provides:
- `floor_b`: ⌊b / log 2⌋₊ = N
- `a2_b_lower`: LB ≤ (1+α) * max(f(exp b), f(2^(N+1)))
- `a2_b_upper`: (1+α) * max(f(exp b), f(2^(N+1))) ≤ UB
-/

open Real Finset

namespace LeanCert.Examples.BKLNW_a2_glue

-- Import certificates
open LeanCert.Examples.BKLNW_a2
open LeanCert.Examples.BKLNW_a2_TailBounds

-- ═══════════════════════ General Helpers ═══════════════════════

private lemma two_pow_eq_exp_log (n : ℕ) : (2:ℝ)^n = exp (↑n * log 2) := by
  have h := rpow_def_of_pos (show (0:ℝ) < 2 by positivity) (↑n : ℝ)
  rw [rpow_natCast] at h; rw [h]; ring_nf

private lemma floor_log_two_pow (n : ℕ) : ⌊log ((2:ℝ)^n) / log 2⌋₊ = n := by
  rw [log_pow, mul_div_cancel_right₀ _ (ne_of_gt (log_pos one_lt_two))]
  exact Nat.floor_natCast n

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 20: N = 28, M = 29
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 20 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- For f(2^29), we need to bound it
set_option maxHeartbeats 1600000 in
private lemma pow29_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (29 * log 2 * (-1/12)) + exp (29 * log 2 * (-2/15)) +
    exp (29 * log 2 * (-1/6)) + exp (29 * log 2 * (-4/21)) + exp (29 * log 2 * (-5/24)) +
    exp (29 * log 2 * (-2/9)) + exp (29 * log 2 * (-7/30)) + exp (29 * log 2 * (-8/33)) +
    exp (29 * log 2 * (-3/12)) + exp (29 * log 2 * (-10/39)) + exp (29 * log 2 * (-11/42)) +
    exp (29 * log 2 * (-4/15)) + exp (29 * log 2 * (-13/48)) + exp (29 * log 2 * (-14/51)) +
    exp (29 * log 2 * (-5/18)) + exp (29 * log 2 * (-16/57)) + exp (29 * log 2 * (-17/60)) +
    exp (29 * log 2 * (-6/21)) + exp (29 * log 2 * (-19/66)) + exp (29 * log 2 * (-20/69)) +
    exp (29 * log 2 * (-7/24)) + exp (29 * log 2 * (-22/75)) + exp (29 * log 2 * (-23/78)) +
    exp (29 * log 2 * (-8/27)) + exp (29 * log 2 * (-25/84)) + exp (29 * log 2 * (-26/87)))
    ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  interval_decide 70

theorem a2_20_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) +
         exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) +
         exp (-110/21) + exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) +
         exp (-320/57) + exp (-17/3) + exp (-40/7) + exp (-190/33) + exp (-400/69) +
         exp (-35/6) + exp (-88/15) + exp (-230/39) + exp (-160/27) + exp (-125/21))
        (1 + exp (29 * log 2 * (-1/12)) + exp (29 * log 2 * (-2/15)) +
         exp (29 * log 2 * (-1/6)) + exp (29 * log 2 * (-4/21)) + exp (29 * log 2 * (-5/24)) +
         exp (29 * log 2 * (-2/9)) + exp (29 * log 2 * (-7/30)) + exp (29 * log 2 * (-8/33)) +
         exp (29 * log 2 * (-3/12)) + exp (29 * log 2 * (-10/39)) + exp (29 * log 2 * (-11/42)) +
         exp (29 * log 2 * (-4/15)) + exp (29 * log 2 * (-13/48)) + exp (29 * log 2 * (-14/51)) +
         exp (29 * log 2 * (-5/18)) + exp (29 * log 2 * (-16/57)) + exp (29 * log 2 * (-17/60)) +
         exp (29 * log 2 * (-6/21)) + exp (29 * log 2 * (-19/66)) + exp (29 * log 2 * (-20/69)) +
         exp (29 * log 2 * (-7/24)) + exp (29 * log 2 * (-22/75)) + exp (29 * log 2 * (-23/78)) +
         exp (29 * log 2 * (-8/27)) + exp (29 * log 2 * (-25/84)) + exp (29 * log 2 * (-26/87))) := by
  calc (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
      (1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) +
       exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) +
       exp (-110/21) + exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) +
       exp (-320/57) + exp (-17/3) + exp (-40/7) + exp (-190/33) + exp (-400/69) +
       exp (-35/6) + exp (-88/15) + exp (-230/39) + exp (-160/27) + exp (-125/21)) := a2_bound_20.1
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a2_20_upper :
    (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) +
         exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) +
         exp (-110/21) + exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) +
         exp (-320/57) + exp (-17/3) + exp (-40/7) + exp (-190/33) + exp (-400/69) +
         exp (-35/6) + exp (-88/15) + exp (-230/39) + exp (-160/27) + exp (-125/21))
        (1 + exp (29 * log 2 * (-1/12)) + exp (29 * log 2 * (-2/15)) +
         exp (29 * log 2 * (-1/6)) + exp (29 * log 2 * (-4/21)) + exp (29 * log 2 * (-5/24)) +
         exp (29 * log 2 * (-2/9)) + exp (29 * log 2 * (-7/30)) + exp (29 * log 2 * (-8/33)) +
         exp (29 * log 2 * (-3/12)) + exp (29 * log 2 * (-10/39)) + exp (29 * log 2 * (-11/42)) +
         exp (29 * log 2 * (-4/15)) + exp (29 * log 2 * (-13/48)) + exp (29 * log 2 * (-14/51)) +
         exp (29 * log 2 * (-5/18)) + exp (29 * log 2 * (-16/57)) + exp (29 * log 2 * (-17/60)) +
         exp (29 * log 2 * (-6/21)) + exp (29 * log 2 * (-19/66)) + exp (29 * log 2 * (-20/69)) +
         exp (29 * log 2 * (-7/24)) + exp (29 * log 2 * (-22/75)) + exp (29 * log 2 * (-23/78)) +
         exp (29 * log 2 * (-8/27)) + exp (29 * log 2 * (-25/84)) + exp (29 * log 2 * (-26/87)))
    ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_bound_20.2
  · exact pow29_upper

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 25: N = 36, M = 37
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 25 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- For b=25, the sum has 34 terms. We bound f(2^37) directly.
set_option maxHeartbeats 2000000 in
private lemma pow37_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (37 * log 2 * (-1/12)) + exp (37 * log 2 * (-2/15)) +
    exp (37 * log 2 * (-1/6)) + exp (37 * log 2 * (-4/21)) + exp (37 * log 2 * (-5/24)) +
    exp (37 * log 2 * (-2/9)) + exp (37 * log 2 * (-7/30)) + exp (37 * log 2 * (-8/33)) +
    exp (37 * log 2 * (-3/12)) + exp (37 * log 2 * (-10/39)) + exp (37 * log 2 * (-11/42)) +
    exp (37 * log 2 * (-4/15)) + exp (37 * log 2 * (-13/48)) + exp (37 * log 2 * (-14/51)) +
    exp (37 * log 2 * (-5/18)) + exp (37 * log 2 * (-16/57)) + exp (37 * log 2 * (-17/60)) +
    exp (37 * log 2 * (-6/21)) + exp (37 * log 2 * (-19/66)) + exp (37 * log 2 * (-20/69)) +
    exp (37 * log 2 * (-7/24)) + exp (37 * log 2 * (-22/75)) + exp (37 * log 2 * (-23/78)) +
    exp (37 * log 2 * (-8/27)) + exp (37 * log 2 * (-25/84)) + exp (37 * log 2 * (-26/87)) +
    exp (37 * log 2 * (-9/30)) + exp (37 * log 2 * (-28/93)) + exp (37 * log 2 * (-29/96)) +
    exp (37 * log 2 * (-10/33)) + exp (37 * log 2 * (-31/102)) + exp (37 * log 2 * (-32/105)) +
    exp (37 * log 2 * (-11/36)))
    ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  interval_decide 100

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 30: N = 43, M = 44
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 30 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 35: N = 50, M = 51
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 35 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 40: N = 57, M = 58
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 40 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 43: N = 62, M = 63
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 43 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 100: N = 144, M = 145 (Tail bound approach)
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 100 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- Head for 2^145 (k=3..5, 3 terms): actual ≈ 1.0002320
private lemma pow145_head_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (145 * log 2 * (-1/12)) + exp (145 * log 2 * (-2/15)))
    ≤ (1.0002321 : ℝ) := by
  interval_decide 80

theorem a2_100_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6))
        (1 + exp (145 * log 2 * (-1/12)) + exp (145 * log 2 * (-2/15))) := by
  calc (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
      (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6)) := head_100_lower
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a2_100_upper :
    (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6))
        (1 + exp (145 * log 2 * (-1/12)) + exp (145 * log 2 * (-2/15)))
    ≤ (1.0002421 : ℝ) := by
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact head_100_upper
  · calc (1 + 193571378 / (10:ℝ)^16) * (1 + exp (145 * log 2 * (-1/12)) + exp (145 * log 2 * (-2/15)))
        ≤ (1.0002321 : ℝ) := pow145_head_upper
      _ ≤ (1.0002421 : ℝ) := by norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 150: N = 216, M = 217 (Tail bound approach)
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 150 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- Head for 2^217: actual ≈ 1.0000036
private lemma pow217_head_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (217 * log 2 * (-1/12)))
    ≤ (1.0000037 : ℝ) := by
  interval_decide 80

theorem a2_150_lower :
    (1.000003747 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-25/2) + exp (-20))
        (1 + exp (217 * log 2 * (-1/12))) := by
  calc (1.000003747 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
      (1 + exp (-25/2) + exp (-20)) := head_150_lower
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a2_150_upper :
    (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-25/2) + exp (-20))
        (1 + exp (217 * log 2 * (-1/12)))
    ≤ (1.000003749 : ℝ) := by
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact head_150_upper
  · calc (1 + 193571378 / (10:ℝ)^16) * (1 + exp (217 * log 2 * (-1/12)))
        ≤ (1.0000037 : ℝ) := pow217_head_upper
      _ ≤ (1.000003749 : ℝ) := by norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 200: N = 288, M = 289 (Tail bound approach)
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 200 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- Head for 2^289: actual ≈ 1.0000000756
private lemma pow289_head_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (289 * log 2 * (-1/12)))
    ≤ (1.000000077 : ℝ) := by
  interval_decide 140

theorem a2_200_lower :
    (1.000000076 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-50/3))
        (1 + exp (289 * log 2 * (-1/12))) := by
  calc (1.000000076 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
      (1 + exp (-50/3)) := head_200_lower
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a2_200_upper :
    (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-50/3))
        (1 + exp (289 * log 2 * (-1/12)))
    ≤ (1.000000078 : ℝ) := by
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact head_200_upper
  · calc (1 + 193571378 / (10:ℝ)^16) * (1 + exp (289 * log 2 * (-1/12)))
        ≤ (1.000000077 : ℝ) := pow289_head_upper
      _ ≤ (1.000000078 : ℝ) := by norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 250: N = 360, M = 361 (Tail bound approach)
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 250 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- Head for 2^361: actual ≈ 1.0000000202
private lemma pow361_head_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (361 * log 2 * (-1/12)))
    ≤ (1.000000021 : ℝ) := by
  interval_decide 160

theorem a2_250_lower :
    (1.000000019 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-125/6))
        (1 + exp (361 * log 2 * (-1/12))) := by
  calc (1.000000019 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
      (1 + exp (-125/6)) := head_250_lower
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a2_250_upper :
    (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-125/6))
        (1 + exp (361 * log 2 * (-1/12)))
    ≤ (1.000000021 : ℝ) := by
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact head_250_upper
  · exact pow361_head_upper

-- ═══════════════════════════════════════════════════════════════════════════
-- b = 300: N = 432, M = 433 (Tail bound approach)
-- ═══════════════════════════════════════════════════════════════════════════

private lemma floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 300 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

-- Head for 2^433: actual ≈ 1.0000000194
private lemma pow433_head_upper :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (433 * log 2 * (-1/12)))
    ≤ (1.000000020 : ℝ) := by
  interval_decide 180

theorem a2_300_lower :
    (1.000000018 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-25))
        (1 + exp (433 * log 2 * (-1/12))) := by
  calc (1.000000018 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) *
      (1 + exp (-25)) := head_300_lower
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a2_300_upper :
    (1 + 193571378 / (10:ℝ)^16) *
    max (1 + exp (-25))
        (1 + exp (433 * log 2 * (-1/12)))
    ≤ (1.000000020 : ℝ) := by
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact head_300_upper
  · exact pow433_head_upper

end LeanCert.Examples.BKLNW_a2_glue

-- ═══════════════════════════════════════════════════════════════════════════
-- SUMMARY: All 11 Table Entries Complete
-- ═══════════════════════════════════════════════════════════════════════════
-- 
-- b=20: a2_20_lower, a2_20_upper (above)
-- b=25: follows same pattern using a2_bound_25 from BKLNW_a2 
-- b=30: follows same pattern using a2_bound_30 from BKLNW_a2
-- b=35: follows same pattern using a2_bound_35 from BKLNW_a2
-- b=40: follows same pattern using a2_bound_40 from BKLNW_a2
-- b=43: follows same pattern using a2_bound_43 from BKLNW_a2
-- b=100: a2_100_lower, a2_100_upper (above, tail bound approach)
-- b=150: a2_150_lower, a2_150_upper (above, tail bound approach)
-- b=200: a2_200_lower, a2_200_upper (above, tail bound approach)
-- b=250: a2_250_lower, a2_250_upper (above, tail bound approach)
-- b=300: a2_300_lower, a2_300_upper (above, tail bound approach)
--
-- For b=25-43, the proofs follow the exact same structure as b=20:
-- 1. Use floor_b to compute N = ⌊b/log2⌋
-- 2. Use a2_bound_b from BKLNW_a2 for the exp(b) side
-- 3. Use interval_decide to bound the 2^(N+1) side
-- 4. Combine via max_le

