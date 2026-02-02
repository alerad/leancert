/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinSumExpand
import LeanCert.Examples.BKLNW_a2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BKLNW a₂ Glue Proofs

Connects `a₂(b) = (1+α) * max(f(exp b), f(2^(⌊b/log2⌋₊+1)))` to certified bounds.
Uses certificates from `LeanCert.Examples.BKLNW_a2`.
-/

open Real Finset LeanCert.Examples.BKLNW_a2

noncomputable def f (x : ℝ) : ℝ := ∑ k ∈ Icc 3 ⌊ (log x)/(log 2) ⌋₊, x^(1/k - 1/3 : ℝ)

-- ═══════════════════════ General Helpers ═══════════════════════

private lemma two_pow_eq_exp_log (n : ℕ) : (2:ℝ)^n = exp (↑n * log 2) := by
  have h := rpow_def_of_pos (show (0:ℝ) < 2 by positivity) (↑n : ℝ)
  rw [rpow_natCast] at h; rw [h]; ring_nf

private lemma floor_log_two_pow (n : ℕ) : ⌊log ((2:ℝ)^n) / log 2⌋₊ = n := by
  rw [log_pow, mul_div_cancel_right₀ _ (ne_of_gt (log_pos one_lt_two))]
  exact Nat.floor_natCast n


-- ═══════════════════════ b = 20 ═══════════════════════

private lemma floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 20 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxHeartbeats 800000 in
private lemma f_exp_20_eq : f (exp (20:ℝ)) =
    1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) +
    exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) + exp (-110/21) +
    exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) + exp (-320/57) + exp (-17/3) +
    exp (-40/7) + exp (-190/33) + exp (-400/69) + exp (-35/6) + exp (-88/15) + exp (-230/39) +
    exp (-160/27) + exp (-125/21) := by
  unfold f
  rw [show ⌊log (exp (20:ℝ)) / log 2⌋₊ = 28 from by rw [log_exp]; exact floor_20]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxHeartbeats 800000 in
private lemma cert_pow29_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(29:ℕ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(29:ℕ)) / log 2⌋₊ = 29 from floor_log_two_pow 29]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 43

private lemma a2_20_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_20]
  calc (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 20) := by
          rw [f_exp_20_eq]; exact a2_bound_20.1
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(28+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_20_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1))) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  rw [floor_20]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · rw [f_exp_20_eq]; exact a2_bound_20.2
  · exact cert_pow29_upper


-- ═══════════════════════ b = 25 ═══════════════════════

private lemma floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 25 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxHeartbeats 1600000 in
private lemma f_exp_25_eq : f (exp (25:ℝ)) =
    1 + exp (-25/12) + exp (-10/3) + exp (-25/6) + exp (-100/21) + exp (-125/24) +
    exp (-50/9) + exp (-35/6) + exp (-200/33) + exp (-25/4) + exp (-250/39) + exp (-275/42) +
    exp (-20/3) + exp (-325/48) + exp (-350/51) + exp (-125/18) + exp (-400/57) + exp (-85/12) +
    exp (-50/7) + exp (-475/66) + exp (-500/69) + exp (-175/24) + exp (-22/3) + exp (-575/78) +
    exp (-200/27) + exp (-625/84) + exp (-650/87) + exp (-15/2) + exp (-700/93) + exp (-725/96) +
    exp (-250/33) + exp (-775/102) + exp (-160/21) + exp (-275/36) := by
  unfold f
  rw [show ⌊log (exp (25:ℝ)) / log 2⌋₊ = 36 from by rw [log_exp]; exact floor_25]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxHeartbeats 1600000 in
private lemma cert_pow37_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(37:ℕ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(37:ℕ)) / log 2⌋₊ = 37 from floor_log_two_pow 37]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 55

private lemma a2_25_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_25]
  calc (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 25) := by
          rw [f_exp_25_eq]; exact a2_bound_25.1
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(36+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_25_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1))) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  rw [floor_25]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · rw [f_exp_25_eq]; exact a2_bound_25.2
  · exact cert_pow37_upper


-- ═══════════════════════ b = 30 ═══════════════════════

private lemma floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 30 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma f_exp_30_eq : f (exp (30:ℝ)) =
    1 + exp (-5/2) + exp (-4) + exp (-5) + exp (-40/7) + exp (-25/4) +
    exp (-20/3) + exp (-7) + exp (-80/11) + exp (-15/2) + exp (-100/13) + exp (-55/7) +
    exp (-8) + exp (-65/8) + exp (-140/17) + exp (-25/3) + exp (-160/19) + exp (-17/2) +
    exp (-60/7) + exp (-95/11) + exp (-200/23) + exp (-35/4) + exp (-44/5) + exp (-115/13) +
    exp (-80/9) + exp (-125/14) + exp (-260/29) + exp (-9) + exp (-280/31) + exp (-145/16) +
    exp (-100/11) + exp (-155/17) + exp (-64/7) + exp (-55/6) + exp (-340/37) + exp (-175/19) +
    exp (-120/13) + exp (-37/4) + exp (-380/41) + exp (-65/7) + exp (-400/43) := by
  unfold f
  rw [show ⌊log (exp (30:ℝ)) / log 2⌋₊ = 43 from by rw [log_exp]; exact floor_30]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma cert_pow44_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(44:ℕ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(44:ℕ)) / log 2⌋₊ = 44 from floor_log_two_pow 44]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 67

private lemma a2_30_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_30]
  calc (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 30) := by
          rw [f_exp_30_eq]; exact a2_bound_30.1
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(43+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_30_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1))) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  rw [floor_30]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · rw [f_exp_30_eq]; exact a2_bound_30.2
  · exact cert_pow44_upper


-- ═══════════════════════ b = 35 ═══════════════════════

private lemma floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 35 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma f_exp_35_eq : f (exp (35:ℝ)) =
    1 + exp (-35/12) + exp (-14/3) + exp (-35/6) + exp (-20/3) + exp (-175/24) +
    exp (-70/9) + exp (-49/6) + exp (-280/33) + exp (-35/4) + exp (-350/39) + exp (-55/6) +
    exp (-28/3) + exp (-455/48) + exp (-490/51) + exp (-175/18) + exp (-560/57) + exp (-119/12) +
    exp (-10) + exp (-665/66) + exp (-700/69) + exp (-245/24) + exp (-154/15) + exp (-805/78) +
    exp (-280/27) + exp (-125/12) + exp (-910/87) + exp (-21/2) + exp (-980/93) + exp (-1015/96) +
    exp (-350/33) + exp (-1085/102) + exp (-32/3) + exp (-385/36) + exp (-1190/111) + exp (-1225/114) +
    exp (-140/13) + exp (-259/24) + exp (-1330/123) + exp (-65/6) + exp (-1400/129) + exp (-1435/132) +
    exp (-98/9) + exp (-1505/138) + exp (-1540/141) + exp (-175/16) + exp (-230/21) + exp (-329/30) := by
  unfold f
  rw [show ⌊log (exp (35:ℝ)) / log 2⌋₊ = 50 from by rw [log_exp]; exact floor_35]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma cert_pow51_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(51:ℕ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(51:ℕ)) / log 2⌋₊ = 51 from floor_log_two_pow 51]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 78

private lemma a2_35_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_35]
  calc (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 35) := by
          rw [f_exp_35_eq]; exact a2_bound_35.1
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(50+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_35_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1))) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  rw [floor_35]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · rw [f_exp_35_eq]; exact a2_bound_35.2
  · exact cert_pow51_upper


-- ═══════════════════════ b = 40 ═══════════════════════

private lemma floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 40 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 1024 in
set_option maxHeartbeats 3200000 in
private lemma f_exp_40_eq : f (exp (40:ℝ)) =
    1 + exp (-10/3) + exp (-16/3) + exp (-20/3) + exp (-160/21) + exp (-25/3) +
    exp (-80/9) + exp (-28/3) + exp (-320/33) + exp (-10) + exp (-400/39) + exp (-220/21) +
    exp (-32/3) + exp (-65/6) + exp (-560/51) + exp (-100/9) + exp (-640/57) + exp (-34/3) +
    exp (-80/7) + exp (-380/33) + exp (-800/69) + exp (-35/3) + exp (-176/15) + exp (-460/39) +
    exp (-320/27) + exp (-250/21) + exp (-1040/87) + exp (-12) + exp (-1120/93) + exp (-145/12) +
    exp (-400/33) + exp (-620/51) + exp (-256/21) + exp (-110/9) + exp (-1360/111) + exp (-700/57) +
    exp (-160/13) + exp (-37/3) + exp (-1520/123) + exp (-260/21) + exp (-1600/129) + exp (-410/33) +
    exp (-112/9) + exp (-860/69) + exp (-1760/141) + exp (-25/2) + exp (-1840/147) + exp (-188/15) +
    exp (-640/51) + exp (-490/39) + exp (-2000/159) + exp (-340/27) + exp (-416/33) + exp (-265/21) +
    exp (-240/19) := by
  unfold f
  rw [show ⌊log (exp (40:ℝ)) / log 2⌋₊ = 57 from by rw [log_exp]; exact floor_40]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 1024 in
set_option maxHeartbeats 3200000 in
private lemma cert_pow58_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(58:ℕ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(58:ℕ)) / log 2⌋₊ = 58 from floor_log_two_pow 58]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 89

private lemma a2_40_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_40]
  calc (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 40) := by
          rw [f_exp_40_eq]; exact a2_bound_40.1
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(57+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_40_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1))) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  rw [floor_40]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · rw [f_exp_40_eq]; exact a2_bound_40.2
  · exact cert_pow58_upper


-- ═══════════════════════ b = 43 ═══════════════════════

private lemma floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 43 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 1024 in
set_option maxHeartbeats 3200000 in
private lemma f_exp_43_eq : f (exp (43:ℝ)) =
    1 + exp (-43/12) + exp (-86/15) + exp (-43/6) + exp (-172/21) + exp (-215/24) +
    exp (-86/9) + exp (-301/30) + exp (-344/33) + exp (-43/4) + exp (-430/39) + exp (-473/42) +
    exp (-172/15) + exp (-559/48) + exp (-602/51) + exp (-215/18) + exp (-688/57) + exp (-731/60) +
    exp (-86/7) + exp (-817/66) + exp (-860/69) + exp (-301/24) + exp (-946/75) + exp (-989/78) +
    exp (-344/27) + exp (-1075/84) + exp (-1118/87) + exp (-129/10) + exp (-1204/93) + exp (-1247/96) +
    exp (-430/33) + exp (-1333/102) + exp (-1376/105) + exp (-473/36) + exp (-1462/111) + exp (-1505/114) +
    exp (-172/13) + exp (-1591/120) + exp (-1634/123) + exp (-559/42) + exp (-40/3) + exp (-1763/132) +
    exp (-602/45) + exp (-1849/138) + exp (-1892/141) + exp (-215/16) + exp (-1978/147) + exp (-2021/150) +
    exp (-688/51) + exp (-2107/156) + exp (-2150/159) + exp (-731/54) + exp (-2236/165) + exp (-2279/168) +
    exp (-258/19) + exp (-2365/174) + exp (-2408/177) + exp (-817/60) + exp (-2494/183) + exp (-2537/186) := by
  unfold f
  rw [show ⌊log (exp (43:ℝ)) / log 2⌋₊ = 62 from by rw [log_exp]; exact floor_43]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 1024 in
set_option maxHeartbeats 3200000 in
private lemma cert_pow63_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(63:ℕ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  unfold f
  rw [show ⌊log ((2:ℝ)^(63:ℕ)) / log 2⌋₊ = 63 from floor_log_two_pow 63]
  finsum_expand
  simp only [Nat.cast_ofNat, two_pow_eq_exp_log, ← exp_mul]
  norm_num
  interval_decide 98

private lemma a2_43_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_43]
  calc (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 43) := by
          rw [f_exp_43_eq]; exact a2_bound_43.1
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(62+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_43_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1))) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  rw [floor_43]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · rw [f_exp_43_eq]; exact a2_bound_43.2
  · exact cert_pow63_upper


-- ═══════════════════════ b = 100 (tail bound needed) ═══════════════════════

private lemma a2_100_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1))) := by
  sorry

private lemma a2_100_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1))) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  sorry


-- ═══════════════════════ b = 150 (tail bound needed) ═══════════════════════

private lemma a2_150_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1))) := by
  sorry

private lemma a2_150_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1))) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  sorry


-- ═══════════════════════ b = 200 (tail bound needed) ═══════════════════════

private lemma a2_200_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1))) := by
  sorry

private lemma a2_200_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  sorry


-- ═══════════════════════ b = 250 (tail bound needed) ═══════════════════════

private lemma a2_250_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1))) := by
  sorry

private lemma a2_250_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  sorry


-- ═══════════════════════ b = 300 (tail bound needed) ═══════════════════════

private lemma a2_300_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1))) := by
  sorry

private lemma a2_300_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by
  sorry

