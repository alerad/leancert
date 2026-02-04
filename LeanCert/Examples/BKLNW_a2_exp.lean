/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinSumExpand
import LeanCert.Examples.BKLNW_a2_pow2
import LeanCert.Examples.BKLNW_a2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BKLNW a₂ Certificates for exp(b)

Certified numerical bounds for f(exp b) used by PNT+ glue proofs.
These lemmas are moved here to keep PrimeNumberTheoremAnd lightweight.
-/

open Real Finset

namespace LeanCert.Examples.BKLNW_a2_exp

-- Reuse the standalone definition matching PNT+'s f
open LeanCert.Examples.BKLNW_a2_pow2 (f)

-- ═══════════════════════ b = 20 ═══════════════════════

private lemma floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 20 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma f_exp_20_eq : f (exp (20:ℝ)) =
    1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) + exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) + exp (-110/21) + exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) + exp (-320/57) + exp (-17/3) + exp (-40/7) + exp (-190/33) + exp (-400/69) + exp (-35/6) + exp (-88/15) + exp (-230/39) + exp (-160/27) + exp (-125/21) := by
  unfold f
  rw [show ⌊log (exp (20:ℝ)) / log 2⌋₊ = 28 from by rw [log_exp]; exact floor_20]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

lemma a2_20_exp_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) := by
  rw [f_exp_20_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_20.1

lemma a2_20_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  rw [f_exp_20_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_20.2


-- ═══════════════════════ b = 25 ═══════════════════════

private lemma floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 25 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma f_exp_25_eq : f (exp (25:ℝ)) =
    1 + exp (-25/12) + exp (-10/3) + exp (-25/6) + exp (-100/21) + exp (-125/24) + exp (-50/9) + exp (-35/6) + exp (-200/33) + exp (-25/4) + exp (-250/39) + exp (-275/42) + exp (-20/3) + exp (-325/48) + exp (-350/51) + exp (-125/18) + exp (-400/57) + exp (-85/12) + exp (-50/7) + exp (-475/66) + exp (-500/69) + exp (-175/24) + exp (-22/3) + exp (-575/78) + exp (-200/27) + exp (-625/84) + exp (-650/87) + exp (-15/2) + exp (-700/93) + exp (-725/96) + exp (-250/33) + exp (-775/102) + exp (-160/21) + exp (-275/36) := by
  unfold f
  rw [show ⌊log (exp (25:ℝ)) / log 2⌋₊ = 36 from by rw [log_exp]; exact floor_25]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

lemma a2_25_exp_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) := by
  rw [f_exp_25_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_25.1

lemma a2_25_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  rw [f_exp_25_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_25.2


-- ═══════════════════════ b = 30 ═══════════════════════

private lemma floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 30 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma f_exp_30_eq : f (exp (30:ℝ)) =
    1 + exp (-5/2) + exp (-4) + exp (-5) + exp (-40/7) + exp (-25/4) + exp (-20/3) + exp (-7) + exp (-80/11) + exp (-15/2) + exp (-100/13) + exp (-55/7) + exp (-8) + exp (-65/8) + exp (-140/17) + exp (-25/3) + exp (-160/19) + exp (-17/2) + exp (-60/7) + exp (-95/11) + exp (-200/23) + exp (-35/4) + exp (-44/5) + exp (-115/13) + exp (-80/9) + exp (-125/14) + exp (-260/29) + exp (-9) + exp (-280/31) + exp (-145/16) + exp (-100/11) + exp (-155/17) + exp (-64/7) + exp (-55/6) + exp (-340/37) + exp (-175/19) + exp (-120/13) + exp (-37/4) + exp (-380/41) + exp (-65/7) + exp (-400/43) := by
  unfold f
  rw [show ⌊log (exp (30:ℝ)) / log 2⌋₊ = 43 from by rw [log_exp]; exact floor_30]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

lemma a2_30_exp_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) := by
  rw [f_exp_30_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_30.1

lemma a2_30_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  rw [f_exp_30_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_30.2


-- ═══════════════════════ b = 35 ═══════════════════════

private lemma floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 35 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma f_exp_35_eq : f (exp (35:ℝ)) =
    1 + exp (-35/12) + exp (-14/3) + exp (-35/6) + exp (-20/3) + exp (-175/24) + exp (-70/9) + exp (-49/6) + exp (-280/33) + exp (-35/4) + exp (-350/39) + exp (-55/6) + exp (-28/3) + exp (-455/48) + exp (-490/51) + exp (-175/18) + exp (-560/57) + exp (-119/12) + exp (-10) + exp (-665/66) + exp (-700/69) + exp (-245/24) + exp (-154/15) + exp (-805/78) + exp (-280/27) + exp (-125/12) + exp (-910/87) + exp (-21/2) + exp (-980/93) + exp (-1015/96) + exp (-350/33) + exp (-1085/102) + exp (-32/3) + exp (-385/36) + exp (-1190/111) + exp (-1225/114) + exp (-140/13) + exp (-259/24) + exp (-1330/123) + exp (-65/6) + exp (-1400/129) + exp (-1435/132) + exp (-98/9) + exp (-1505/138) + exp (-1540/141) + exp (-175/16) + exp (-230/21) + exp (-329/30) := by
  unfold f
  rw [show ⌊log (exp (35:ℝ)) / log 2⌋₊ = 50 from by rw [log_exp]; exact floor_35]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

lemma a2_35_exp_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) := by
  rw [f_exp_35_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_35.1

lemma a2_35_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  rw [f_exp_35_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_35.2


-- ═══════════════════════ b = 40 ═══════════════════════

private lemma floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 40 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma f_exp_40_eq : f (exp (40:ℝ)) =
    1 + exp (-10/3) + exp (-16/3) + exp (-20/3) + exp (-160/21) + exp (-25/3) + exp (-80/9) + exp (-28/3) + exp (-320/33) + exp (-10) + exp (-400/39) + exp (-220/21) + exp (-32/3) + exp (-65/6) + exp (-560/51) + exp (-100/9) + exp (-640/57) + exp (-34/3) + exp (-80/7) + exp (-380/33) + exp (-800/69) + exp (-35/3) + exp (-176/15) + exp (-460/39) + exp (-320/27) + exp (-250/21) + exp (-1040/87) + exp (-12) + exp (-1120/93) + exp (-145/12) + exp (-400/33) + exp (-620/51) + exp (-256/21) + exp (-110/9) + exp (-1360/111) + exp (-700/57) + exp (-160/13) + exp (-37/3) + exp (-1520/123) + exp (-260/21) + exp (-1600/129) + exp (-410/33) + exp (-112/9) + exp (-860/69) + exp (-1760/141) + exp (-25/2) + exp (-1840/147) + exp (-188/15) + exp (-640/51) + exp (-490/39) + exp (-2000/159) + exp (-340/27) + exp (-416/33) + exp (-265/21) + exp (-240/19) := by
  unfold f
  rw [show ⌊log (exp (40:ℝ)) / log 2⌋₊ = 57 from by rw [log_exp]; exact floor_40]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

lemma a2_40_exp_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) := by
  rw [f_exp_40_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_40.1

lemma a2_40_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  rw [f_exp_40_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_40.2


-- ═══════════════════════ b = 43 ═══════════════════════

private lemma floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 43 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma f_exp_43_eq : f (exp (43:ℝ)) =
    1 + exp (-43/12) + exp (-86/15) + exp (-43/6) + exp (-172/21) + exp (-215/24) + exp (-86/9) + exp (-301/30) + exp (-344/33) + exp (-43/4) + exp (-430/39) + exp (-473/42) + exp (-172/15) + exp (-559/48) + exp (-602/51) + exp (-215/18) + exp (-688/57) + exp (-731/60) + exp (-86/7) + exp (-817/66) + exp (-860/69) + exp (-301/24) + exp (-946/75) + exp (-989/78) + exp (-344/27) + exp (-1075/84) + exp (-1118/87) + exp (-129/10) + exp (-1204/93) + exp (-1247/96) + exp (-430/33) + exp (-1333/102) + exp (-1376/105) + exp (-473/36) + exp (-1462/111) + exp (-1505/114) + exp (-172/13) + exp (-1591/120) + exp (-1634/123) + exp (-559/42) + exp (-40/3) + exp (-1763/132) + exp (-602/45) + exp (-1849/138) + exp (-1892/141) + exp (-215/16) + exp (-1978/147) + exp (-2021/150) + exp (-688/51) + exp (-2107/156) + exp (-2150/159) + exp (-731/54) + exp (-2236/165) + exp (-2279/168) + exp (-258/19) + exp (-2365/174) + exp (-2408/177) + exp (-817/60) + exp (-2494/183) + exp (-2537/186) := by
  unfold f
  rw [show ⌊log (exp (43:ℝ)) / log 2⌋₊ = 62 from by rw [log_exp]; exact floor_43]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

lemma a2_43_exp_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) := by
  rw [f_exp_43_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_43.1

lemma a2_43_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  rw [f_exp_43_eq]; exact LeanCert.Examples.BKLNW_a2.a2_bound_43.2




private lemma floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 100 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
private lemma f_exp_100_eq : f (exp (100:ℝ)) =
    1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6) +
    exp (-200/9) + exp (-70/3) + exp (-800/33) + exp (-25) + exp (-1000/39) + exp (-550/21) +
    exp (-80/3) + exp (-325/12) + exp (-1400/51) + exp (-250/9) + exp (-1600/57) + exp (-85/3) +
    exp (-200/7) + exp (-950/33) + exp (-2000/69) + exp (-175/6) + exp (-88/3) + exp (-1150/39) +
    exp (-800/27) + exp (-625/21) + exp (-2600/87) + exp (-30) + exp (-2800/93) + exp (-725/24) +
    exp (-1000/33) + exp (-1550/51) + exp (-640/21) + exp (-275/9) + exp (-3400/111) + exp (-1750/57) +
    exp (-400/13) + exp (-185/6) + exp (-3800/123) + exp (-650/21) + exp (-4000/129) + exp (-1025/33) +
    exp (-280/9) + exp (-2150/69) + exp (-4400/141) + exp (-125/4) + exp (-4600/147) + exp (-94/3) +
    exp (-1600/51) + exp (-1225/39) + exp (-5000/159) + exp (-850/27) + exp (-1040/33) + exp (-1325/42) +
    exp (-600/19) + exp (-2750/87) + exp (-5600/177) + exp (-95/3) + exp (-5800/183) + exp (-2950/93) +
    exp (-2000/63) + exp (-1525/48) + exp (-1240/39) + exp (-350/11) + exp (-6400/201) + exp (-1625/51) +
    exp (-2200/69) + exp (-670/21) + exp (-6800/213) + exp (-575/18) + exp (-7000/219) + exp (-3550/111) +
    exp (-32) + exp (-1825/57) + exp (-7400/231) + exp (-1250/39) + exp (-7600/237) + exp (-385/12) +
    exp (-2600/81) + exp (-3950/123) + exp (-8000/249) + exp (-225/7) + exp (-1640/51) + exp (-4150/129) +
    exp (-2800/87) + exp (-2125/66) + exp (-8600/267) + exp (-290/9) + exp (-8800/273) + exp (-2225/69) +
    exp (-1000/31) + exp (-4550/141) + exp (-1840/57) + exp (-775/24) + exp (-9400/291) + exp (-4750/147) +
    exp (-3200/99) + exp (-97/3) + exp (-9800/303) + exp (-550/17) + exp (-10000/309) + exp (-2525/78) +
    exp (-680/21) + exp (-5150/159) + exp (-10400/321) + exp (-875/27) + exp (-10600/327) + exp (-1070/33) +
    exp (-1200/37) + exp (-2725/84) + exp (-11000/339) + exp (-1850/57) + exp (-2240/69) + exp (-2825/87) +
    exp (-3800/117) + exp (-5750/177) + exp (-11600/357) + exp (-65/2) + exp (-11800/363) + exp (-5950/183) +
    exp (-4000/123) + exp (-3025/93) + exp (-488/15) + exp (-2050/63) + exp (-12400/381) + exp (-3125/96) +
    exp (-1400/43) + exp (-1270/39) + exp (-12800/393) + exp (-1075/33) + exp (-13000/399) + exp (-6550/201) +
    exp (-880/27) + exp (-3325/102) + exp (-13400/411) + exp (-750/23) + exp (-13600/417) + exp (-685/21) +
    exp (-4600/141) + exp (-6950/213) + exp (-14000/429) + exp (-1175/36) := by
  unfold f
  rw [show ⌊log (exp (100:ℝ)) / log 2⌋₊ = 144 from by rw [log_exp]; exact floor_100]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
lemma a2_100_exp_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) := by
  rw [f_exp_100_eq]
  interval_decide 30

set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
lemma a2_100_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  rw [f_exp_100_eq]
  interval_decide 30

set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
private lemma floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 150 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
private lemma f_exp_150_eq : f (exp (150:ℝ)) =
    1 + exp (-25/2) + exp (-20) + exp (-25) + exp (-200/7) + exp (-125/4) +
    exp (-100/3) + exp (-35) + exp (-400/11) + exp (-75/2) + exp (-500/13) + exp (-275/7) +
    exp (-40) + exp (-325/8) + exp (-700/17) + exp (-125/3) + exp (-800/19) + exp (-85/2) +
    exp (-300/7) + exp (-475/11) + exp (-1000/23) + exp (-175/4) + exp (-44) + exp (-575/13) +
    exp (-400/9) + exp (-625/14) + exp (-1300/29) + exp (-45) + exp (-1400/31) + exp (-725/16) +
    exp (-500/11) + exp (-775/17) + exp (-320/7) + exp (-275/6) + exp (-1700/37) + exp (-875/19) +
    exp (-600/13) + exp (-185/4) + exp (-1900/41) + exp (-325/7) + exp (-2000/43) + exp (-1025/22) +
    exp (-140/3) + exp (-1075/23) + exp (-2200/47) + exp (-375/8) + exp (-2300/49) + exp (-47) +
    exp (-800/17) + exp (-1225/26) + exp (-2500/53) + exp (-425/9) + exp (-520/11) + exp (-1325/28) +
    exp (-900/19) + exp (-1375/29) + exp (-2800/59) + exp (-95/2) + exp (-2900/61) + exp (-1475/31) +
    exp (-1000/21) + exp (-1525/32) + exp (-620/13) + exp (-525/11) + exp (-3200/67) + exp (-1625/34) +
    exp (-1100/23) + exp (-335/7) + exp (-3400/71) + exp (-575/12) + exp (-3500/73) + exp (-1775/37) +
    exp (-48) + exp (-1825/38) + exp (-3700/77) + exp (-625/13) + exp (-3800/79) + exp (-385/8) +
    exp (-1300/27) + exp (-1975/41) + exp (-4000/83) + exp (-675/14) + exp (-820/17) + exp (-2075/43) +
    exp (-1400/29) + exp (-2125/44) + exp (-4300/89) + exp (-145/3) + exp (-4400/91) + exp (-2225/46) +
    exp (-1500/31) + exp (-2275/47) + exp (-920/19) + exp (-775/16) + exp (-4700/97) + exp (-2375/49) +
    exp (-1600/33) + exp (-97/2) + exp (-4900/101) + exp (-825/17) + exp (-5000/103) + exp (-2525/52) +
    exp (-340/7) + exp (-2575/53) + exp (-5200/107) + exp (-875/18) + exp (-5300/109) + exp (-535/11) +
    exp (-1800/37) + exp (-2725/56) + exp (-5500/113) + exp (-925/19) + exp (-1120/23) + exp (-2825/58) +
    exp (-1900/39) + exp (-2875/59) + exp (-5800/119) + exp (-195/4) + exp (-5900/121) + exp (-2975/61) +
    exp (-2000/41) + exp (-3025/62) + exp (-244/5) + exp (-1025/21) + exp (-6200/127) + exp (-3125/64) +
    exp (-2100/43) + exp (-635/13) + exp (-6400/131) + exp (-1075/22) + exp (-6500/133) + exp (-3275/67) +
    exp (-440/9) + exp (-3325/68) + exp (-6700/137) + exp (-1125/23) + exp (-6800/139) + exp (-685/14) +
    exp (-2300/47) + exp (-3475/71) + exp (-7000/143) + exp (-1175/24) + exp (-1420/29) + exp (-3575/73) +
    exp (-2400/49) + exp (-3625/74) + exp (-7300/149) + exp (-49) + exp (-7400/151) + exp (-3725/76) +
    exp (-2500/51) + exp (-3775/77) + exp (-1520/31) + exp (-1275/26) + exp (-7700/157) + exp (-3875/79) +
    exp (-2600/53) + exp (-785/16) + exp (-7900/161) + exp (-1325/27) + exp (-8000/163) + exp (-4025/82) +
    exp (-540/11) + exp (-4075/83) + exp (-8200/167) + exp (-1375/28) + exp (-8300/169) + exp (-835/17) +
    exp (-2800/57) + exp (-4225/86) + exp (-8500/173) + exp (-1425/29) + exp (-344/7) + exp (-4325/88) +
    exp (-2900/59) + exp (-4375/89) + exp (-8800/179) + exp (-295/6) + exp (-8900/181) + exp (-4475/91) +
    exp (-3000/61) + exp (-4525/92) + exp (-1820/37) + exp (-1525/31) + exp (-9200/187) + exp (-4625/94) +
    exp (-3100/63) + exp (-935/19) + exp (-9400/191) + exp (-1575/32) + exp (-9500/193) + exp (-4775/97) +
    exp (-640/13) + exp (-4825/98) + exp (-9700/197) + exp (-1625/33) + exp (-9800/199) + exp (-197/4) +
    exp (-3300/67) + exp (-4975/101) + exp (-10000/203) + exp (-1675/34) + exp (-2020/41) + exp (-5075/103) +
    exp (-3400/69) + exp (-5125/104) + exp (-10300/209) + exp (-345/7) + exp (-10400/211) + exp (-5225/106) +
    exp (-3500/71) + exp (-5275/107) + exp (-2120/43) + exp (-1775/36) := by
  unfold f
  rw [show ⌊log (exp (150:ℝ)) / log 2⌋₊ = 216 from by rw [log_exp]; exact floor_150]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
lemma a2_150_exp_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) := by
  rw [f_exp_150_eq]
  interval_decide 30

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
lemma a2_150_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  rw [f_exp_150_eq]
  interval_decide 30

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
private lemma floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 200 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 128000000 in
private lemma f_exp_200_eq : f (exp (200:ℝ)) =
    1 + exp (-50/3) + exp (-80/3) + exp (-100/3) + exp (-800/21) + exp (-125/3) +
    exp (-400/9) + exp (-140/3) + exp (-1600/33) + exp (-50) + exp (-2000/39) + exp (-1100/21) +
    exp (-160/3) + exp (-325/6) + exp (-2800/51) + exp (-500/9) + exp (-3200/57) + exp (-170/3) +
    exp (-400/7) + exp (-1900/33) + exp (-4000/69) + exp (-175/3) + exp (-176/3) + exp (-2300/39) +
    exp (-1600/27) + exp (-1250/21) + exp (-5200/87) + exp (-60) + exp (-5600/93) + exp (-725/12) +
    exp (-2000/33) + exp (-3100/51) + exp (-1280/21) + exp (-550/9) + exp (-6800/111) + exp (-3500/57) +
    exp (-800/13) + exp (-185/3) + exp (-7600/123) + exp (-1300/21) + exp (-8000/129) + exp (-2050/33) +
    exp (-560/9) + exp (-4300/69) + exp (-8800/141) + exp (-125/2) + exp (-9200/147) + exp (-188/3) +
    exp (-3200/51) + exp (-2450/39) + exp (-10000/159) + exp (-1700/27) + exp (-2080/33) + exp (-1325/21) +
    exp (-1200/19) + exp (-5500/87) + exp (-11200/177) + exp (-190/3) + exp (-11600/183) + exp (-5900/93) +
    exp (-4000/63) + exp (-1525/24) + exp (-2480/39) + exp (-700/11) + exp (-12800/201) + exp (-3250/51) +
    exp (-4400/69) + exp (-1340/21) + exp (-13600/213) + exp (-575/9) + exp (-14000/219) + exp (-7100/111) +
    exp (-64) + exp (-3650/57) + exp (-14800/231) + exp (-2500/39) + exp (-15200/237) + exp (-385/6) +
    exp (-5200/81) + exp (-7900/123) + exp (-16000/249) + exp (-450/7) + exp (-3280/51) + exp (-8300/129) +
    exp (-5600/87) + exp (-2125/33) + exp (-17200/267) + exp (-580/9) + exp (-17600/273) + exp (-4450/69) +
    exp (-2000/31) + exp (-9100/141) + exp (-3680/57) + exp (-775/12) + exp (-18800/291) + exp (-9500/147) +
    exp (-6400/99) + exp (-194/3) + exp (-19600/303) + exp (-1100/17) + exp (-20000/309) + exp (-2525/39) +
    exp (-1360/21) + exp (-10300/159) + exp (-20800/321) + exp (-1750/27) + exp (-21200/327) + exp (-2140/33) +
    exp (-2400/37) + exp (-2725/42) + exp (-22000/339) + exp (-3700/57) + exp (-4480/69) + exp (-5650/87) +
    exp (-7600/117) + exp (-11500/177) + exp (-23200/357) + exp (-65) + exp (-23600/363) + exp (-11900/183) +
    exp (-8000/123) + exp (-6050/93) + exp (-976/15) + exp (-4100/63) + exp (-24800/381) + exp (-3125/48) +
    exp (-2800/43) + exp (-2540/39) + exp (-25600/393) + exp (-2150/33) + exp (-26000/399) + exp (-13100/201) +
    exp (-1760/27) + exp (-3325/51) + exp (-26800/411) + exp (-1500/23) + exp (-27200/417) + exp (-1370/21) +
    exp (-9200/141) + exp (-13900/213) + exp (-28000/429) + exp (-1175/18) + exp (-5680/87) + exp (-14300/219) +
    exp (-3200/49) + exp (-7250/111) + exp (-29200/447) + exp (-196/3) + exp (-29600/453) + exp (-3725/57) +
    exp (-10000/153) + exp (-15100/231) + exp (-6080/93) + exp (-850/13) + exp (-30800/471) + exp (-15500/237) +
    exp (-10400/159) + exp (-785/12) + exp (-31600/483) + exp (-5300/81) + exp (-32000/489) + exp (-8050/123) +
    exp (-720/11) + exp (-16300/249) + exp (-32800/501) + exp (-1375/21) + exp (-33200/507) + exp (-3340/51) +
    exp (-11200/171) + exp (-8450/129) + exp (-34000/519) + exp (-1900/29) + exp (-1376/21) + exp (-4325/66) +
    exp (-11600/177) + exp (-17500/267) + exp (-35200/537) + exp (-590/9) + exp (-35600/543) + exp (-17900/273) +
    exp (-4000/61) + exp (-4525/69) + exp (-7280/111) + exp (-6100/93) + exp (-36800/561) + exp (-9250/141) +
    exp (-12400/189) + exp (-3740/57) + exp (-37600/573) + exp (-525/8) + exp (-38000/579) + exp (-19100/291) +
    exp (-2560/39) + exp (-9650/147) + exp (-38800/591) + exp (-6500/99) + exp (-39200/597) + exp (-197/3) +
    exp (-4400/67) + exp (-19900/303) + exp (-40000/609) + exp (-3350/51) + exp (-8080/123) + exp (-20300/309) +
    exp (-13600/207) + exp (-5125/78) + exp (-41200/627) + exp (-460/7) + exp (-41600/633) + exp (-10450/159) +
    exp (-14000/213) + exp (-21100/321) + exp (-8480/129) + exp (-1775/27) + exp (-42800/651) + exp (-21500/327) +
    exp (-4800/73) + exp (-2170/33) + exp (-43600/663) + exp (-7300/111) + exp (-44000/669) + exp (-5525/84) +
    exp (-592/9) + exp (-22300/339) + exp (-44800/681) + exp (-1250/19) + exp (-45200/687) + exp (-4540/69) +
    exp (-15200/231) + exp (-5725/87) + exp (-46000/699) + exp (-7700/117) + exp (-9280/141) + exp (-11650/177) +
    exp (-5200/79) + exp (-23500/357) + exp (-47200/717) + exp (-395/6) + exp (-47600/723) + exp (-23900/363) +
    exp (-16000/243) + exp (-12050/183) + exp (-9680/147) + exp (-2700/41) + exp (-48800/741) + exp (-6125/93) +
    exp (-16400/249) + exp (-988/15) + exp (-49600/753) + exp (-4150/63) + exp (-50000/759) + exp (-25100/381) +
    exp (-1120/17) + exp (-6325/96) + exp (-50800/771) + exp (-8500/129) + exp (-51200/777) + exp (-2570/39) +
    exp (-17200/261) + exp (-25900/393) + exp (-52000/789) + exp (-725/11) + exp (-10480/159) + exp (-26300/399) +
    exp (-17600/267) + exp (-13250/201) + exp (-53200/807) + exp (-1780/27) + exp (-53600/813) + exp (-6725/102) +
    exp (-6000/91) + exp (-27100/411) + exp (-2176/33) + exp (-4550/69) + exp (-54800/831) + exp (-27500/417) +
    exp (-18400/279) + exp (-1385/21) + exp (-55600/843) + exp (-3100/47) + exp (-56000/849) + exp (-14050/213) +
    exp (-3760/57) + exp (-28300/429) + exp (-56800/861) + exp (-2375/36) := by
  unfold f
  rw [show ⌊log (exp (200:ℝ)) / log 2⌋₊ = 288 from by rw [log_exp]; exact floor_200]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 16384 in
set_option maxHeartbeats 128000000 in
lemma a2_200_exp_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) := by
  rw [f_exp_200_eq]
  interval_decide 30

set_option maxRecDepth 16384 in
set_option maxHeartbeats 128000000 in
lemma a2_200_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  rw [f_exp_200_eq]
  interval_decide 30

set_option maxRecDepth 16384 in
set_option maxHeartbeats 128000000 in
private lemma floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 250 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 256000000 in
private lemma f_exp_250_eq : f (exp (250:ℝ)) =
    1 + exp (-125/6) + exp (-100/3) + exp (-125/3) + exp (-1000/21) + exp (-625/12) +
    exp (-500/9) + exp (-175/3) + exp (-2000/33) + exp (-125/2) + exp (-2500/39) + exp (-1375/21) +
    exp (-200/3) + exp (-1625/24) + exp (-3500/51) + exp (-625/9) + exp (-4000/57) + exp (-425/6) +
    exp (-500/7) + exp (-2375/33) + exp (-5000/69) + exp (-875/12) + exp (-220/3) + exp (-2875/39) +
    exp (-2000/27) + exp (-3125/42) + exp (-6500/87) + exp (-75) + exp (-7000/93) + exp (-3625/48) +
    exp (-2500/33) + exp (-3875/51) + exp (-1600/21) + exp (-1375/18) + exp (-8500/111) + exp (-4375/57) +
    exp (-1000/13) + exp (-925/12) + exp (-9500/123) + exp (-1625/21) + exp (-10000/129) + exp (-5125/66) +
    exp (-700/9) + exp (-5375/69) + exp (-11000/141) + exp (-625/8) + exp (-11500/147) + exp (-235/3) +
    exp (-4000/51) + exp (-6125/78) + exp (-12500/159) + exp (-2125/27) + exp (-2600/33) + exp (-6625/84) +
    exp (-1500/19) + exp (-6875/87) + exp (-14000/177) + exp (-475/6) + exp (-14500/183) + exp (-7375/93) +
    exp (-5000/63) + exp (-7625/96) + exp (-3100/39) + exp (-875/11) + exp (-16000/201) + exp (-8125/102) +
    exp (-5500/69) + exp (-1675/21) + exp (-17000/213) + exp (-2875/36) + exp (-17500/219) + exp (-8875/111) +
    exp (-80) + exp (-9125/114) + exp (-18500/231) + exp (-3125/39) + exp (-19000/237) + exp (-1925/24) +
    exp (-6500/81) + exp (-9875/123) + exp (-20000/249) + exp (-1125/14) + exp (-4100/51) + exp (-10375/129) +
    exp (-7000/87) + exp (-10625/132) + exp (-21500/267) + exp (-725/9) + exp (-22000/273) + exp (-11125/138) +
    exp (-2500/31) + exp (-11375/141) + exp (-4600/57) + exp (-3875/48) + exp (-23500/291) + exp (-11875/147) +
    exp (-8000/99) + exp (-485/6) + exp (-24500/303) + exp (-1375/17) + exp (-25000/309) + exp (-12625/156) +
    exp (-1700/21) + exp (-12875/159) + exp (-26000/321) + exp (-4375/54) + exp (-26500/327) + exp (-2675/33) +
    exp (-3000/37) + exp (-13625/168) + exp (-27500/339) + exp (-4625/57) + exp (-5600/69) + exp (-14125/174) +
    exp (-9500/117) + exp (-14375/177) + exp (-29000/357) + exp (-325/4) + exp (-29500/363) + exp (-14875/183) +
    exp (-10000/123) + exp (-15125/186) + exp (-244/3) + exp (-5125/63) + exp (-31000/381) + exp (-15625/192) +
    exp (-3500/43) + exp (-3175/39) + exp (-32000/393) + exp (-5375/66) + exp (-32500/399) + exp (-16375/201) +
    exp (-2200/27) + exp (-16625/204) + exp (-33500/411) + exp (-1875/23) + exp (-34000/417) + exp (-3425/42) +
    exp (-11500/141) + exp (-17375/213) + exp (-35000/429) + exp (-5875/72) + exp (-7100/87) + exp (-17875/219) +
    exp (-4000/49) + exp (-18125/222) + exp (-36500/447) + exp (-245/3) + exp (-37000/453) + exp (-18625/228) +
    exp (-12500/153) + exp (-18875/231) + exp (-7600/93) + exp (-2125/26) + exp (-38500/471) + exp (-19375/237) +
    exp (-13000/159) + exp (-3925/48) + exp (-39500/483) + exp (-6625/81) + exp (-40000/489) + exp (-20125/246) +
    exp (-900/11) + exp (-20375/249) + exp (-41000/501) + exp (-6875/84) + exp (-41500/507) + exp (-4175/51) +
    exp (-14000/171) + exp (-21125/258) + exp (-42500/519) + exp (-2375/29) + exp (-1720/21) + exp (-21625/264) +
    exp (-14500/177) + exp (-21875/267) + exp (-44000/537) + exp (-1475/18) + exp (-44500/543) + exp (-22375/273) +
    exp (-5000/61) + exp (-22625/276) + exp (-9100/111) + exp (-7625/93) + exp (-46000/561) + exp (-23125/282) +
    exp (-15500/189) + exp (-4675/57) + exp (-47000/573) + exp (-2625/32) + exp (-47500/579) + exp (-23875/291) +
    exp (-3200/39) + exp (-24125/294) + exp (-48500/591) + exp (-8125/99) + exp (-49000/597) + exp (-985/12) +
    exp (-5500/67) + exp (-24875/303) + exp (-50000/609) + exp (-8375/102) + exp (-10100/123) + exp (-25375/309) +
    exp (-17000/207) + exp (-25625/312) + exp (-51500/627) + exp (-575/7) + exp (-52000/633) + exp (-26125/318) +
    exp (-17500/213) + exp (-26375/321) + exp (-10600/129) + exp (-8875/108) + exp (-53500/651) + exp (-26875/327) +
    exp (-6000/73) + exp (-5425/66) + exp (-54500/663) + exp (-9125/111) + exp (-55000/669) + exp (-27625/336) +
    exp (-740/9) + exp (-27875/339) + exp (-56000/681) + exp (-3125/38) + exp (-56500/687) + exp (-5675/69) +
    exp (-19000/231) + exp (-28625/348) + exp (-57500/699) + exp (-9625/117) + exp (-11600/141) + exp (-29125/354) +
    exp (-6500/79) + exp (-29375/357) + exp (-59000/717) + exp (-1975/24) + exp (-59500/723) + exp (-29875/363) +
    exp (-20000/243) + exp (-30125/366) + exp (-12100/147) + exp (-3375/41) + exp (-61000/741) + exp (-30625/372) +
    exp (-20500/249) + exp (-247/3) + exp (-62000/753) + exp (-10375/126) + exp (-62500/759) + exp (-31375/381) +
    exp (-1400/17) + exp (-31625/384) + exp (-63500/771) + exp (-10625/129) + exp (-64000/777) + exp (-6425/78) +
    exp (-21500/261) + exp (-32375/393) + exp (-65000/789) + exp (-3625/44) + exp (-13100/159) + exp (-32875/399) +
    exp (-22000/267) + exp (-33125/402) + exp (-66500/807) + exp (-2225/27) + exp (-67000/813) + exp (-33625/408) +
    exp (-7500/91) + exp (-33875/411) + exp (-2720/33) + exp (-11375/138) + exp (-68500/831) + exp (-34375/417) +
    exp (-23000/279) + exp (-6925/84) + exp (-69500/843) + exp (-3875/47) + exp (-70000/849) + exp (-35125/426) +
    exp (-4700/57) + exp (-35375/429) + exp (-71000/861) + exp (-11875/144) + exp (-71500/867) + exp (-7175/87) +
    exp (-8000/97) + exp (-36125/438) + exp (-72500/879) + exp (-12125/147) + exp (-14600/177) + exp (-36625/444) +
    exp (-24500/297) + exp (-36875/447) + exp (-74000/897) + exp (-165/2) + exp (-74500/903) + exp (-37375/453) +
    exp (-25000/303) + exp (-37625/456) + exp (-15100/183) + exp (-12625/153) + exp (-76000/921) + exp (-38125/462) +
    exp (-8500/103) + exp (-7675/93) + exp (-77000/933) + exp (-12875/156) + exp (-77500/939) + exp (-38875/471) +
    exp (-5200/63) + exp (-39125/474) + exp (-78500/951) + exp (-4375/53) + exp (-79000/957) + exp (-7925/96) +
    exp (-26500/321) + exp (-39875/483) + exp (-80000/969) + exp (-13375/162) + exp (-3220/39) + exp (-40375/489) +
    exp (-9000/109) + exp (-40625/492) + exp (-81500/987) + exp (-2725/33) + exp (-82000/993) + exp (-41125/498) +
    exp (-27500/333) + exp (-41375/501) + exp (-16600/201) + exp (-4625/56) + exp (-83500/1011) + exp (-41875/507) +
    exp (-28000/339) + exp (-8425/102) + exp (-84500/1023) + exp (-14125/171) + exp (-85000/1029) + exp (-42625/516) +
    exp (-1900/23) + exp (-42875/519) + exp (-86000/1041) + exp (-14375/174) + exp (-86500/1047) + exp (-1735/21) +
    exp (-29000/351) + exp (-43625/528) + exp (-87500/1059) + exp (-4875/59) + exp (-17600/213) + exp (-44125/534) +
    exp (-29500/357) + exp (-44375/537) + exp (-89000/1077) + exp (-2975/36) := by
  unfold f
  rw [show ⌊log (exp (250:ℝ)) / log 2⌋₊ = 360 from by rw [log_exp]; exact floor_250]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 32768 in
set_option maxHeartbeats 256000000 in
lemma a2_250_exp_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) := by
  rw [f_exp_250_eq]
  interval_decide 30

set_option maxRecDepth 32768 in
set_option maxHeartbeats 256000000 in
lemma a2_250_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  rw [f_exp_250_eq]
  interval_decide 30

set_option maxRecDepth 32768 in
set_option maxHeartbeats 256000000 in
private lemma floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 300 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 512000000 in
private lemma f_exp_300_eq : f (exp (300:ℝ)) =
    1 + exp (-25) + exp (-40) + exp (-50) + exp (-400/7) + exp (-125/2) +
    exp (-200/3) + exp (-70) + exp (-800/11) + exp (-75) + exp (-1000/13) + exp (-550/7) +
    exp (-80) + exp (-325/4) + exp (-1400/17) + exp (-250/3) + exp (-1600/19) + exp (-85) +
    exp (-600/7) + exp (-950/11) + exp (-2000/23) + exp (-175/2) + exp (-88) + exp (-1150/13) +
    exp (-800/9) + exp (-625/7) + exp (-2600/29) + exp (-90) + exp (-2800/31) + exp (-725/8) +
    exp (-1000/11) + exp (-1550/17) + exp (-640/7) + exp (-275/3) + exp (-3400/37) + exp (-1750/19) +
    exp (-1200/13) + exp (-185/2) + exp (-3800/41) + exp (-650/7) + exp (-4000/43) + exp (-1025/11) +
    exp (-280/3) + exp (-2150/23) + exp (-4400/47) + exp (-375/4) + exp (-4600/49) + exp (-94) +
    exp (-1600/17) + exp (-1225/13) + exp (-5000/53) + exp (-850/9) + exp (-1040/11) + exp (-1325/14) +
    exp (-1800/19) + exp (-2750/29) + exp (-5600/59) + exp (-95) + exp (-5800/61) + exp (-2950/31) +
    exp (-2000/21) + exp (-1525/16) + exp (-1240/13) + exp (-1050/11) + exp (-6400/67) + exp (-1625/17) +
    exp (-2200/23) + exp (-670/7) + exp (-6800/71) + exp (-575/6) + exp (-7000/73) + exp (-3550/37) +
    exp (-96) + exp (-1825/19) + exp (-7400/77) + exp (-1250/13) + exp (-7600/79) + exp (-385/4) +
    exp (-2600/27) + exp (-3950/41) + exp (-8000/83) + exp (-675/7) + exp (-1640/17) + exp (-4150/43) +
    exp (-2800/29) + exp (-2125/22) + exp (-8600/89) + exp (-290/3) + exp (-8800/91) + exp (-2225/23) +
    exp (-3000/31) + exp (-4550/47) + exp (-1840/19) + exp (-775/8) + exp (-9400/97) + exp (-4750/49) +
    exp (-3200/33) + exp (-97) + exp (-9800/101) + exp (-1650/17) + exp (-10000/103) + exp (-2525/26) +
    exp (-680/7) + exp (-5150/53) + exp (-10400/107) + exp (-875/9) + exp (-10600/109) + exp (-1070/11) +
    exp (-3600/37) + exp (-2725/28) + exp (-11000/113) + exp (-1850/19) + exp (-2240/23) + exp (-2825/29) +
    exp (-3800/39) + exp (-5750/59) + exp (-11600/119) + exp (-195/2) + exp (-11800/121) + exp (-5950/61) +
    exp (-4000/41) + exp (-3025/31) + exp (-488/5) + exp (-2050/21) + exp (-12400/127) + exp (-3125/32) +
    exp (-4200/43) + exp (-1270/13) + exp (-12800/131) + exp (-1075/11) + exp (-13000/133) + exp (-6550/67) +
    exp (-880/9) + exp (-3325/34) + exp (-13400/137) + exp (-2250/23) + exp (-13600/139) + exp (-685/7) +
    exp (-4600/47) + exp (-6950/71) + exp (-14000/143) + exp (-1175/12) + exp (-2840/29) + exp (-7150/73) +
    exp (-4800/49) + exp (-3625/37) + exp (-14600/149) + exp (-98) + exp (-14800/151) + exp (-3725/38) +
    exp (-5000/51) + exp (-7550/77) + exp (-3040/31) + exp (-1275/13) + exp (-15400/157) + exp (-7750/79) +
    exp (-5200/53) + exp (-785/8) + exp (-15800/161) + exp (-2650/27) + exp (-16000/163) + exp (-4025/41) +
    exp (-1080/11) + exp (-8150/83) + exp (-16400/167) + exp (-1375/14) + exp (-16600/169) + exp (-1670/17) +
    exp (-5600/57) + exp (-4225/43) + exp (-17000/173) + exp (-2850/29) + exp (-688/7) + exp (-4325/44) +
    exp (-5800/59) + exp (-8750/89) + exp (-17600/179) + exp (-295/3) + exp (-17800/181) + exp (-8950/91) +
    exp (-6000/61) + exp (-4525/46) + exp (-3640/37) + exp (-3050/31) + exp (-18400/187) + exp (-4625/47) +
    exp (-6200/63) + exp (-1870/19) + exp (-18800/191) + exp (-1575/16) + exp (-19000/193) + exp (-9550/97) +
    exp (-1280/13) + exp (-4825/49) + exp (-19400/197) + exp (-3250/33) + exp (-19600/199) + exp (-197/2) +
    exp (-6600/67) + exp (-9950/101) + exp (-20000/203) + exp (-1675/17) + exp (-4040/41) + exp (-10150/103) +
    exp (-6800/69) + exp (-5125/52) + exp (-20600/209) + exp (-690/7) + exp (-20800/211) + exp (-5225/53) +
    exp (-7000/71) + exp (-10550/107) + exp (-4240/43) + exp (-1775/18) + exp (-21400/217) + exp (-10750/109) +
    exp (-7200/73) + exp (-1085/11) + exp (-21800/221) + exp (-3650/37) + exp (-22000/223) + exp (-5525/56) +
    exp (-296/3) + exp (-11150/113) + exp (-22400/227) + exp (-1875/19) + exp (-22600/229) + exp (-2270/23) +
    exp (-7600/77) + exp (-5725/58) + exp (-23000/233) + exp (-3850/39) + exp (-4640/47) + exp (-5825/59) +
    exp (-7800/79) + exp (-11750/119) + exp (-23600/239) + exp (-395/4) + exp (-23800/241) + exp (-11950/121) +
    exp (-8000/81) + exp (-6025/61) + exp (-4840/49) + exp (-4050/41) + exp (-24400/247) + exp (-6125/62) +
    exp (-8200/83) + exp (-494/5) + exp (-24800/251) + exp (-2075/21) + exp (-25000/253) + exp (-12550/127) +
    exp (-1680/17) + exp (-6325/64) + exp (-25400/257) + exp (-4250/43) + exp (-25600/259) + exp (-1285/13) +
    exp (-8600/87) + exp (-12950/131) + exp (-26000/263) + exp (-2175/22) + exp (-5240/53) + exp (-13150/133) +
    exp (-8800/89) + exp (-6625/67) + exp (-26600/269) + exp (-890/9) + exp (-26800/271) + exp (-6725/68) +
    exp (-9000/91) + exp (-13550/137) + exp (-1088/11) + exp (-2275/23) + exp (-27400/277) + exp (-13750/139) +
    exp (-9200/93) + exp (-1385/14) + exp (-27800/281) + exp (-4650/47) + exp (-28000/283) + exp (-7025/71) +
    exp (-1880/19) + exp (-14150/143) + exp (-28400/287) + exp (-2375/24) + exp (-28600/289) + exp (-2870/29) +
    exp (-9600/97) + exp (-7225/73) + exp (-29000/293) + exp (-4850/49) + exp (-5840/59) + exp (-7325/74) +
    exp (-9800/99) + exp (-14750/149) + exp (-29600/299) + exp (-99) + exp (-29800/301) + exp (-14950/151) +
    exp (-10000/101) + exp (-7525/76) + exp (-6040/61) + exp (-5050/51) + exp (-30400/307) + exp (-7625/77) +
    exp (-10200/103) + exp (-3070/31) + exp (-30800/311) + exp (-2575/26) + exp (-31000/313) + exp (-15550/157) +
    exp (-2080/21) + exp (-7825/79) + exp (-31400/317) + exp (-5250/53) + exp (-31600/319) + exp (-1585/16) +
    exp (-10600/107) + exp (-15950/161) + exp (-32000/323) + exp (-2675/27) + exp (-1288/13) + exp (-16150/163) +
    exp (-10800/109) + exp (-8125/82) + exp (-32600/329) + exp (-1090/11) + exp (-32800/331) + exp (-8225/83) +
    exp (-11000/111) + exp (-16550/167) + exp (-6640/67) + exp (-2775/28) + exp (-33400/337) + exp (-16750/169) +
    exp (-11200/113) + exp (-1685/17) + exp (-33800/341) + exp (-5650/57) + exp (-34000/343) + exp (-8525/86) +
    exp (-2280/23) + exp (-17150/173) + exp (-34400/347) + exp (-2875/29) + exp (-34600/349) + exp (-694/7) +
    exp (-11600/117) + exp (-8725/88) + exp (-35000/353) + exp (-5850/59) + exp (-7040/71) + exp (-8825/89) +
    exp (-11800/119) + exp (-17750/179) + exp (-35600/359) + exp (-595/6) + exp (-35800/361) + exp (-17950/181) +
    exp (-12000/121) + exp (-9025/91) + exp (-7240/73) + exp (-6050/61) + exp (-36400/367) + exp (-9125/92) +
    exp (-12200/123) + exp (-3670/37) + exp (-36800/371) + exp (-3075/31) + exp (-37000/373) + exp (-18550/187) +
    exp (-496/5) + exp (-9325/94) + exp (-37400/377) + exp (-6250/63) + exp (-37600/379) + exp (-1885/19) +
    exp (-12600/127) + exp (-18950/191) + exp (-38000/383) + exp (-3175/32) + exp (-7640/77) + exp (-19150/193) +
    exp (-12800/129) + exp (-9625/97) + exp (-38600/389) + exp (-1290/13) + exp (-38800/391) + exp (-9725/98) +
    exp (-13000/131) + exp (-19550/197) + exp (-7840/79) + exp (-3275/33) + exp (-39400/397) + exp (-19750/199) +
    exp (-13200/133) + exp (-397/4) + exp (-39800/401) + exp (-6650/67) + exp (-40000/403) + exp (-10025/101) +
    exp (-2680/27) + exp (-20150/203) + exp (-40400/407) + exp (-3375/34) + exp (-40600/409) + exp (-4070/41) +
    exp (-13600/137) + exp (-10225/103) + exp (-41000/413) + exp (-6850/69) + exp (-8240/83) + exp (-10325/104) +
    exp (-13800/139) + exp (-20750/209) + exp (-41600/419) + exp (-695/7) + exp (-41800/421) + exp (-20950/211) +
    exp (-14000/141) + exp (-10525/106) + exp (-1688/17) + exp (-7050/71) + exp (-42400/427) + exp (-10625/107) +
    exp (-14200/143) + exp (-4270/43) + exp (-42800/431) + exp (-3575/36) := by
  unfold f
  rw [show ⌊log (exp (300:ℝ)) / log 2⌋₊ = 432 from by rw [log_exp]; exact floor_300]
  finsum_expand
  simp only [Nat.cast_ofNat, ← exp_mul]
  norm_num

set_option maxRecDepth 65536 in
set_option maxHeartbeats 512000000 in
lemma a2_300_exp_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) := by
  rw [f_exp_300_eq]
  interval_decide 30

set_option maxRecDepth 65536 in
set_option maxHeartbeats 512000000 in
lemma a2_300_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by
  rw [f_exp_300_eq]
  interval_decide 30

set_option maxRecDepth 65536 in
set_option maxHeartbeats 512000000 in

end LeanCert.Examples.BKLNW_a2_exp
