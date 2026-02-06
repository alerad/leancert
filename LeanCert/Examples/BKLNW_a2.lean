/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BKLNW a₂ Numerical Certificates

Certified numerical bounds for the a₂ parameter from BKLNW Corollary 5.1.
Used by `cor_5_1_rem` in PrimeNumberTheoremAnd.

For each value of b, we certify that (1+α) * S(b) lies in a specified interval,
where α = 1.93378×10⁻⁸ × 1.001 and S(b) = Σ_{k=3}^{⌊b/log2⌋} exp(b/k - b/3).
-/

open Real

namespace LeanCert.Examples.BKLNW_a2

theorem a2_bound_20 :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) + exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) + exp (-110/21) + exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) + exp (-320/57) + exp (-17/3) + exp (-40/7) + exp (-190/33) + exp (-400/69) + exp (-35/6) + exp (-88/15) + exp (-230/39) + exp (-160/27) + exp (-125/21)) ∧
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-5/3) + exp (-8/3) + exp (-10/3) + exp (-80/21) + exp (-25/6) + exp (-40/9) + exp (-14/3) + exp (-160/33) + exp (-5) + exp (-200/39) + exp (-110/21) + exp (-16/3) + exp (-65/12) + exp (-280/51) + exp (-50/9) + exp (-320/57) + exp (-17/3) + exp (-40/7) + exp (-190/33) + exp (-400/69) + exp (-35/6) + exp (-88/15) + exp (-230/39) + exp (-160/27) + exp (-125/21)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  constructor <;> interval_decide 50

theorem a2_lower_25_part1 :
    (1.20241469 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/12) + exp (-10/3) + exp (-25/6) + exp (-100/21) + exp (-125/24) + exp (-50/9) + exp (-35/6) + exp (-200/33) + exp (-25/4) + exp (-250/39)) := by
  interval_decide 50

theorem a2_upper_25_part1 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/12) + exp (-10/3) + exp (-25/6) + exp (-100/21) + exp (-125/24) + exp (-50/9) + exp (-35/6) + exp (-200/33) + exp (-25/4) + exp (-250/39)) ≤ (1.2024147 : ℝ) := by
  interval_decide 50

theorem a2_lower_25_part2 :
    (0.01053119 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-275/42) + exp (-20/3) + exp (-325/48) + exp (-350/51) + exp (-125/18) + exp (-400/57) + exp (-85/12) + exp (-50/7) + exp (-475/66) + exp (-500/69) + exp (-175/24)) := by
  interval_decide 60

theorem a2_upper_25_part2 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-275/42) + exp (-20/3) + exp (-325/48) + exp (-350/51) + exp (-125/18) + exp (-400/57) + exp (-85/12) + exp (-50/7) + exp (-475/66) + exp (-500/69) + exp (-175/24)) ≤ (0.0105312 : ℝ) := by
  interval_decide 60

theorem a2_lower_25_part3 :
    (0.00664813 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-22/3) + exp (-575/78) + exp (-200/27) + exp (-625/84) + exp (-650/87) + exp (-15/2) + exp (-700/93) + exp (-725/96) + exp (-250/33) + exp (-775/102) + exp (-160/21) + exp (-275/36)) := by
  interval_decide 60

theorem a2_upper_25_part3 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-22/3) + exp (-575/78) + exp (-200/27) + exp (-625/84) + exp (-650/87) + exp (-15/2) + exp (-700/93) + exp (-725/96) + exp (-250/33) + exp (-775/102) + exp (-160/21) + exp (-275/36)) ≤ (0.00664814 : ℝ) := by
  interval_decide 60

theorem a2_bound_25 :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/12) + exp (-10/3) + exp (-25/6) + exp (-100/21) + exp (-125/24) + exp (-50/9) + exp (-35/6) + exp (-200/33) + exp (-25/4) + exp (-250/39) + exp (-275/42) + exp (-20/3) + exp (-325/48) + exp (-350/51) + exp (-125/18) + exp (-400/57) + exp (-85/12) + exp (-50/7) + exp (-475/66) + exp (-500/69) + exp (-175/24) + exp (-22/3) + exp (-575/78) + exp (-200/27) + exp (-625/84) + exp (-650/87) + exp (-15/2) + exp (-700/93) + exp (-725/96) + exp (-250/33) + exp (-775/102) + exp (-160/21) + exp (-275/36)) ∧
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/12) + exp (-10/3) + exp (-25/6) + exp (-100/21) + exp (-125/24) + exp (-50/9) + exp (-35/6) + exp (-200/33) + exp (-25/4) + exp (-250/39) + exp (-275/42) + exp (-20/3) + exp (-325/48) + exp (-350/51) + exp (-125/18) + exp (-400/57) + exp (-85/12) + exp (-50/7) + exp (-475/66) + exp (-500/69) + exp (-175/24) + exp (-22/3) + exp (-575/78) + exp (-200/27) + exp (-625/84) + exp (-650/87) + exp (-15/2) + exp (-700/93) + exp (-725/96) + exp (-250/33) + exp (-775/102) + exp (-160/21) + exp (-275/36)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  constructor
  · have h1 := a2_lower_25_part1
    have h2 := a2_lower_25_part2
    have h3 := a2_lower_25_part3
    linarith
  · have h1 := a2_upper_25_part1
    have h2 := a2_upper_25_part2
    have h3 := a2_upper_25_part3
    linarith

theorem a2_lower_30_part1 :
    (1.11579938 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-5/2) + exp (-4) + exp (-5) + exp (-40/7) + exp (-25/4) + exp (-20/3) + exp (-7) + exp (-80/11) + exp (-15/2)) := by
  interval_decide 60

theorem a2_upper_30_part1 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-5/2) + exp (-4) + exp (-5) + exp (-40/7) + exp (-25/4) + exp (-20/3) + exp (-7) + exp (-80/11) + exp (-15/2)) ≤ (1.11579939 : ℝ) := by
  interval_decide 60

theorem a2_lower_30_part2 :
    (0.00277093 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-100/13) + exp (-55/7) + exp (-8) + exp (-65/8) + exp (-140/17) + exp (-25/3) + exp (-160/19) + exp (-17/2) + exp (-60/7) + exp (-95/11)) := by
  interval_decide 70

theorem a2_upper_30_part2 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-100/13) + exp (-55/7) + exp (-8) + exp (-65/8) + exp (-140/17) + exp (-25/3) + exp (-160/19) + exp (-17/2) + exp (-60/7) + exp (-95/11)) ≤ (0.00277094 : ℝ) := by
  interval_decide 70

theorem a2_lower_30_part3 :
    (0.00137747 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-200/23) + exp (-35/4) + exp (-44/5) + exp (-115/13) + exp (-80/9) + exp (-125/14) + exp (-260/29) + exp (-9) + exp (-280/31) + exp (-145/16)) := by
  interval_decide 70

theorem a2_upper_30_part3 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-200/23) + exp (-35/4) + exp (-44/5) + exp (-115/13) + exp (-80/9) + exp (-125/14) + exp (-260/29) + exp (-9) + exp (-280/31) + exp (-145/16)) ≤ (0.00137748 : ℝ) := by
  interval_decide 70

theorem a2_lower_30_part4 :
    (0.00110837 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-100/11) + exp (-155/17) + exp (-64/7) + exp (-55/6) + exp (-340/37) + exp (-175/19) + exp (-120/13) + exp (-37/4) + exp (-380/41) + exp (-65/7) + exp (-400/43)) := by
  interval_decide 70

theorem a2_upper_30_part4 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-100/11) + exp (-155/17) + exp (-64/7) + exp (-55/6) + exp (-340/37) + exp (-175/19) + exp (-120/13) + exp (-37/4) + exp (-380/41) + exp (-65/7) + exp (-400/43)) ≤ (0.00110838 : ℝ) := by
  interval_decide 70

theorem a2_bound_30 :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-5/2) + exp (-4) + exp (-5) + exp (-40/7) + exp (-25/4) + exp (-20/3) + exp (-7) + exp (-80/11) + exp (-15/2) + exp (-100/13) + exp (-55/7) + exp (-8) + exp (-65/8) + exp (-140/17) + exp (-25/3) + exp (-160/19) + exp (-17/2) + exp (-60/7) + exp (-95/11) + exp (-200/23) + exp (-35/4) + exp (-44/5) + exp (-115/13) + exp (-80/9) + exp (-125/14) + exp (-260/29) + exp (-9) + exp (-280/31) + exp (-145/16) + exp (-100/11) + exp (-155/17) + exp (-64/7) + exp (-55/6) + exp (-340/37) + exp (-175/19) + exp (-120/13) + exp (-37/4) + exp (-380/41) + exp (-65/7) + exp (-400/43)) ∧
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-5/2) + exp (-4) + exp (-5) + exp (-40/7) + exp (-25/4) + exp (-20/3) + exp (-7) + exp (-80/11) + exp (-15/2) + exp (-100/13) + exp (-55/7) + exp (-8) + exp (-65/8) + exp (-140/17) + exp (-25/3) + exp (-160/19) + exp (-17/2) + exp (-60/7) + exp (-95/11) + exp (-200/23) + exp (-35/4) + exp (-44/5) + exp (-115/13) + exp (-80/9) + exp (-125/14) + exp (-260/29) + exp (-9) + exp (-280/31) + exp (-145/16) + exp (-100/11) + exp (-155/17) + exp (-64/7) + exp (-55/6) + exp (-340/37) + exp (-175/19) + exp (-120/13) + exp (-37/4) + exp (-380/41) + exp (-65/7) + exp (-400/43)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  constructor
  · have h1 := a2_lower_30_part1
    have h2 := a2_lower_30_part2
    have h3 := a2_lower_30_part3
    have h4 := a2_lower_30_part4
    linarith
  · have h1 := a2_upper_30_part1
    have h2 := a2_upper_30_part2
    have h3 := a2_upper_30_part3
    have h4 := a2_upper_30_part4
    linarith

theorem a2_lower_35_part1 :
    (1.069698495 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-35/12) + exp (-14/3) + exp (-35/6) + exp (-20/3) + exp (-175/24) + exp (-70/9) + exp (-49/6) + exp (-280/33) + exp (-35/4) + exp (-350/39) + exp (-55/6)) := by
  interval_decide 70

theorem a2_upper_35_part1 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-35/12) + exp (-14/3) + exp (-35/6) + exp (-20/3) + exp (-175/24) + exp (-70/9) + exp (-49/6) + exp (-280/33) + exp (-35/4) + exp (-350/39) + exp (-55/6)) ≤ (1.069698496 : ℝ) := by
  interval_decide 70

theorem a2_lower_35_part2 :
    (0.000626789 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-28/3) + exp (-455/48) + exp (-490/51) + exp (-175/18) + exp (-560/57) + exp (-119/12) + exp (-10) + exp (-665/66) + exp (-700/69) + exp (-245/24) + exp (-154/15) + exp (-805/78)) := by
  interval_decide 80

theorem a2_upper_35_part2 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-28/3) + exp (-455/48) + exp (-490/51) + exp (-175/18) + exp (-560/57) + exp (-119/12) + exp (-10) + exp (-665/66) + exp (-700/69) + exp (-245/24) + exp (-154/15) + exp (-805/78)) ≤ (0.00062679 : ℝ) := by
  interval_decide 80

theorem a2_lower_35_part3 :
    (0.000307972 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-280/27) + exp (-125/12) + exp (-910/87) + exp (-21/2) + exp (-980/93) + exp (-1015/96) + exp (-350/33) + exp (-1085/102) + exp (-32/3) + exp (-385/36) + exp (-1190/111) + exp (-1225/114)) := by
  interval_decide 80

theorem a2_upper_35_part3 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-280/27) + exp (-125/12) + exp (-910/87) + exp (-21/2) + exp (-980/93) + exp (-1015/96) + exp (-350/33) + exp (-1085/102) + exp (-32/3) + exp (-385/36) + exp (-1190/111) + exp (-1225/114)) ≤ (0.000307973 : ℝ) := by
  interval_decide 80

theorem a2_lower_35_part4 :
    (0.000227458 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-140/13) + exp (-259/24) + exp (-1330/123) + exp (-65/6) + exp (-1400/129) + exp (-1435/132) + exp (-98/9) + exp (-1505/138) + exp (-1540/141) + exp (-175/16) + exp (-230/21) + exp (-329/30)) := by
  interval_decide 80

theorem a2_upper_35_part4 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-140/13) + exp (-259/24) + exp (-1330/123) + exp (-65/6) + exp (-1400/129) + exp (-1435/132) + exp (-98/9) + exp (-1505/138) + exp (-1540/141) + exp (-175/16) + exp (-230/21) + exp (-329/30)) ≤ (0.000227459 : ℝ) := by
  interval_decide 80

theorem a2_bound_35 :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-35/12) + exp (-14/3) + exp (-35/6) + exp (-20/3) + exp (-175/24) + exp (-70/9) + exp (-49/6) + exp (-280/33) + exp (-35/4) + exp (-350/39) + exp (-55/6) + exp (-28/3) + exp (-455/48) + exp (-490/51) + exp (-175/18) + exp (-560/57) + exp (-119/12) + exp (-10) + exp (-665/66) + exp (-700/69) + exp (-245/24) + exp (-154/15) + exp (-805/78) + exp (-280/27) + exp (-125/12) + exp (-910/87) + exp (-21/2) + exp (-980/93) + exp (-1015/96) + exp (-350/33) + exp (-1085/102) + exp (-32/3) + exp (-385/36) + exp (-1190/111) + exp (-1225/114) + exp (-140/13) + exp (-259/24) + exp (-1330/123) + exp (-65/6) + exp (-1400/129) + exp (-1435/132) + exp (-98/9) + exp (-1505/138) + exp (-1540/141) + exp (-175/16) + exp (-230/21) + exp (-329/30)) ∧
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-35/12) + exp (-14/3) + exp (-35/6) + exp (-20/3) + exp (-175/24) + exp (-70/9) + exp (-49/6) + exp (-280/33) + exp (-35/4) + exp (-350/39) + exp (-55/6) + exp (-28/3) + exp (-455/48) + exp (-490/51) + exp (-175/18) + exp (-560/57) + exp (-119/12) + exp (-10) + exp (-665/66) + exp (-700/69) + exp (-245/24) + exp (-154/15) + exp (-805/78) + exp (-280/27) + exp (-125/12) + exp (-910/87) + exp (-21/2) + exp (-980/93) + exp (-1015/96) + exp (-350/33) + exp (-1085/102) + exp (-32/3) + exp (-385/36) + exp (-1190/111) + exp (-1225/114) + exp (-140/13) + exp (-259/24) + exp (-1330/123) + exp (-65/6) + exp (-1400/129) + exp (-1435/132) + exp (-98/9) + exp (-1505/138) + exp (-1540/141) + exp (-175/16) + exp (-230/21) + exp (-329/30)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  constructor
  · have h1 := a2_lower_35_part1
    have h2 := a2_lower_35_part2
    have h3 := a2_lower_35_part3
    have h4 := a2_lower_35_part4
    linarith
  · have h1 := a2_upper_35_part1
    have h2 := a2_upper_35_part2
    have h3 := a2_upper_35_part3
    have h4 := a2_upper_35_part4
    linarith

theorem a2_lower_40_part1 :
    (1.042874316 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-10/3) + exp (-16/3) + exp (-20/3) + exp (-160/21) + exp (-25/3) + exp (-80/9) + exp (-28/3) + exp (-320/33) + exp (-10) + exp (-400/39)) := by
  interval_decide 80

theorem a2_upper_40_part1 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-10/3) + exp (-16/3) + exp (-20/3) + exp (-160/21) + exp (-25/3) + exp (-80/9) + exp (-28/3) + exp (-320/33) + exp (-10) + exp (-400/39)) ≤ (1.042874317 : ℝ) := by
  interval_decide 80

theorem a2_lower_40_part2 :
    (0.000167132 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-220/21) + exp (-32/3) + exp (-65/6) + exp (-560/51) + exp (-100/9) + exp (-640/57) + exp (-34/3) + exp (-80/7) + exp (-380/33) + exp (-800/69) + exp (-35/3)) := by
  interval_decide 90

theorem a2_upper_40_part2 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-220/21) + exp (-32/3) + exp (-65/6) + exp (-560/51) + exp (-100/9) + exp (-640/57) + exp (-34/3) + exp (-80/7) + exp (-380/33) + exp (-800/69) + exp (-35/3)) ≤ (0.000167133 : ℝ) := by
  interval_decide 90

theorem a2_lower_40_part3 :
    (6.9338e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-176/15) + exp (-460/39) + exp (-320/27) + exp (-250/21) + exp (-1040/87) + exp (-12) + exp (-1120/93) + exp (-145/12) + exp (-400/33) + exp (-620/51) + exp (-256/21)) := by
  interval_decide 90

theorem a2_upper_40_part3 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-176/15) + exp (-460/39) + exp (-320/27) + exp (-250/21) + exp (-1040/87) + exp (-12) + exp (-1120/93) + exp (-145/12) + exp (-400/33) + exp (-620/51) + exp (-256/21)) ≤ (6.9339e-5 : ℝ) := by
  interval_decide 90

theorem a2_lower_40_part4 :
    (4.7677e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-110/9) + exp (-1360/111) + exp (-700/57) + exp (-160/13) + exp (-37/3) + exp (-1520/123) + exp (-260/21) + exp (-1600/129) + exp (-410/33) + exp (-112/9) + exp (-860/69)) := by
  interval_decide 90

theorem a2_upper_40_part4 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-110/9) + exp (-1360/111) + exp (-700/57) + exp (-160/13) + exp (-37/3) + exp (-1520/123) + exp (-260/21) + exp (-1600/129) + exp (-410/33) + exp (-112/9) + exp (-860/69)) ≤ (4.7678e-5 : ℝ) := by
  interval_decide 90

theorem a2_lower_40_part5 :
    (3.8601e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-1760/141) + exp (-25/2) + exp (-1840/147) + exp (-188/15) + exp (-640/51) + exp (-490/39) + exp (-2000/159) + exp (-340/27) + exp (-416/33) + exp (-265/21) + exp (-240/19)) := by
  interval_decide 90

theorem a2_upper_40_part5 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-1760/141) + exp (-25/2) + exp (-1840/147) + exp (-188/15) + exp (-640/51) + exp (-490/39) + exp (-2000/159) + exp (-340/27) + exp (-416/33) + exp (-265/21) + exp (-240/19)) ≤ (3.8602e-5 : ℝ) := by
  interval_decide 90

theorem a2_bound_40 :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-10/3) + exp (-16/3) + exp (-20/3) + exp (-160/21) + exp (-25/3) + exp (-80/9) + exp (-28/3) + exp (-320/33) + exp (-10) + exp (-400/39) + exp (-220/21) + exp (-32/3) + exp (-65/6) + exp (-560/51) + exp (-100/9) + exp (-640/57) + exp (-34/3) + exp (-80/7) + exp (-380/33) + exp (-800/69) + exp (-35/3) + exp (-176/15) + exp (-460/39) + exp (-320/27) + exp (-250/21) + exp (-1040/87) + exp (-12) + exp (-1120/93) + exp (-145/12) + exp (-400/33) + exp (-620/51) + exp (-256/21) + exp (-110/9) + exp (-1360/111) + exp (-700/57) + exp (-160/13) + exp (-37/3) + exp (-1520/123) + exp (-260/21) + exp (-1600/129) + exp (-410/33) + exp (-112/9) + exp (-860/69) + exp (-1760/141) + exp (-25/2) + exp (-1840/147) + exp (-188/15) + exp (-640/51) + exp (-490/39) + exp (-2000/159) + exp (-340/27) + exp (-416/33) + exp (-265/21) + exp (-240/19)) ∧
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-10/3) + exp (-16/3) + exp (-20/3) + exp (-160/21) + exp (-25/3) + exp (-80/9) + exp (-28/3) + exp (-320/33) + exp (-10) + exp (-400/39) + exp (-220/21) + exp (-32/3) + exp (-65/6) + exp (-560/51) + exp (-100/9) + exp (-640/57) + exp (-34/3) + exp (-80/7) + exp (-380/33) + exp (-800/69) + exp (-35/3) + exp (-176/15) + exp (-460/39) + exp (-320/27) + exp (-250/21) + exp (-1040/87) + exp (-12) + exp (-1120/93) + exp (-145/12) + exp (-400/33) + exp (-620/51) + exp (-256/21) + exp (-110/9) + exp (-1360/111) + exp (-700/57) + exp (-160/13) + exp (-37/3) + exp (-1520/123) + exp (-260/21) + exp (-1600/129) + exp (-410/33) + exp (-112/9) + exp (-860/69) + exp (-1760/141) + exp (-25/2) + exp (-1840/147) + exp (-188/15) + exp (-640/51) + exp (-490/39) + exp (-2000/159) + exp (-340/27) + exp (-416/33) + exp (-265/21) + exp (-240/19)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  constructor
  · have h1 := a2_lower_40_part1
    have h2 := a2_lower_40_part2
    have h3 := a2_lower_40_part3
    have h4 := a2_lower_40_part4
    have h5 := a2_lower_40_part5
    linarith
  · have h1 := a2_upper_40_part1
    have h2 := a2_upper_40_part2
    have h3 := a2_upper_40_part3
    have h4 := a2_upper_40_part4
    have h5 := a2_upper_40_part5
    linarith

theorem a2_lower_43_part1 :
    (1.032392058 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-43/12) + exp (-86/15) + exp (-43/6) + exp (-172/21) + exp (-215/24) + exp (-86/9) + exp (-301/30) + exp (-344/33) + exp (-43/4) + exp (-430/39) + exp (-473/42)) := by
  interval_decide 80

theorem a2_upper_43_part1 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-43/12) + exp (-86/15) + exp (-43/6) + exp (-172/21) + exp (-215/24) + exp (-86/9) + exp (-301/30) + exp (-344/33) + exp (-43/4) + exp (-430/39) + exp (-473/42)) ≤ (1.032392059 : ℝ) := by
  interval_decide 80

theorem a2_lower_43_part2 :
    (6.6746e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-172/15) + exp (-559/48) + exp (-602/51) + exp (-215/18) + exp (-688/57) + exp (-731/60) + exp (-86/7) + exp (-817/66) + exp (-860/69) + exp (-301/24) + exp (-946/75) + exp (-989/78)) := by
  interval_decide 90

theorem a2_upper_43_part2 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-172/15) + exp (-559/48) + exp (-602/51) + exp (-215/18) + exp (-688/57) + exp (-731/60) + exp (-86/7) + exp (-817/66) + exp (-860/69) + exp (-301/24) + exp (-946/75) + exp (-989/78)) ≤ (6.6747e-5 : ℝ) := by
  interval_decide 90

theorem a2_lower_43_part3 :
    (2.7546e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-344/27) + exp (-1075/84) + exp (-1118/87) + exp (-129/10) + exp (-1204/93) + exp (-1247/96) + exp (-430/33) + exp (-1333/102) + exp (-1376/105) + exp (-473/36) + exp (-1462/111) + exp (-1505/114)) := by
  interval_decide 100

theorem a2_upper_43_part3 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-344/27) + exp (-1075/84) + exp (-1118/87) + exp (-129/10) + exp (-1204/93) + exp (-1247/96) + exp (-430/33) + exp (-1333/102) + exp (-1376/105) + exp (-473/36) + exp (-1462/111) + exp (-1505/114)) ≤ (2.7547e-5 : ℝ) := by
  interval_decide 100

theorem a2_lower_43_part4 :
    (1.8956e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-172/13) + exp (-1591/120) + exp (-1634/123) + exp (-559/42) + exp (-40/3) + exp (-1763/132) + exp (-602/45) + exp (-1849/138) + exp (-1892/141) + exp (-215/16) + exp (-1978/147) + exp (-2021/150)) := by
  interval_decide 100

theorem a2_upper_43_part4 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-172/13) + exp (-1591/120) + exp (-1634/123) + exp (-559/42) + exp (-40/3) + exp (-1763/132) + exp (-602/45) + exp (-1849/138) + exp (-1892/141) + exp (-215/16) + exp (-1978/147) + exp (-2021/150)) ≤ (1.8957e-5 : ℝ) := by
  interval_decide 100

theorem a2_lower_43_part5 :
    (1.5365e-5 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (exp (-688/51) + exp (-2107/156) + exp (-2150/159) + exp (-731/54) + exp (-2236/165) + exp (-2279/168) + exp (-258/19) + exp (-2365/174) + exp (-2408/177) + exp (-817/60) + exp (-2494/183) + exp (-2537/186)) := by
  interval_decide 100

theorem a2_upper_43_part5 :
    (1 + 193571378 / (10:ℝ)^16) * (exp (-688/51) + exp (-2107/156) + exp (-2150/159) + exp (-731/54) + exp (-2236/165) + exp (-2279/168) + exp (-258/19) + exp (-2365/174) + exp (-2408/177) + exp (-817/60) + exp (-2494/183) + exp (-2537/186)) ≤ (1.5366e-5 : ℝ) := by
  interval_decide 100

theorem a2_bound_43 :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-43/12) + exp (-86/15) + exp (-43/6) + exp (-172/21) + exp (-215/24) + exp (-86/9) + exp (-301/30) + exp (-344/33) + exp (-43/4) + exp (-430/39) + exp (-473/42) + exp (-172/15) + exp (-559/48) + exp (-602/51) + exp (-215/18) + exp (-688/57) + exp (-731/60) + exp (-86/7) + exp (-817/66) + exp (-860/69) + exp (-301/24) + exp (-946/75) + exp (-989/78) + exp (-344/27) + exp (-1075/84) + exp (-1118/87) + exp (-129/10) + exp (-1204/93) + exp (-1247/96) + exp (-430/33) + exp (-1333/102) + exp (-1376/105) + exp (-473/36) + exp (-1462/111) + exp (-1505/114) + exp (-172/13) + exp (-1591/120) + exp (-1634/123) + exp (-559/42) + exp (-40/3) + exp (-1763/132) + exp (-602/45) + exp (-1849/138) + exp (-1892/141) + exp (-215/16) + exp (-1978/147) + exp (-2021/150) + exp (-688/51) + exp (-2107/156) + exp (-2150/159) + exp (-731/54) + exp (-2236/165) + exp (-2279/168) + exp (-258/19) + exp (-2365/174) + exp (-2408/177) + exp (-817/60) + exp (-2494/183) + exp (-2537/186)) ∧
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-43/12) + exp (-86/15) + exp (-43/6) + exp (-172/21) + exp (-215/24) + exp (-86/9) + exp (-301/30) + exp (-344/33) + exp (-43/4) + exp (-430/39) + exp (-473/42) + exp (-172/15) + exp (-559/48) + exp (-602/51) + exp (-215/18) + exp (-688/57) + exp (-731/60) + exp (-86/7) + exp (-817/66) + exp (-860/69) + exp (-301/24) + exp (-946/75) + exp (-989/78) + exp (-344/27) + exp (-1075/84) + exp (-1118/87) + exp (-129/10) + exp (-1204/93) + exp (-1247/96) + exp (-430/33) + exp (-1333/102) + exp (-1376/105) + exp (-473/36) + exp (-1462/111) + exp (-1505/114) + exp (-172/13) + exp (-1591/120) + exp (-1634/123) + exp (-559/42) + exp (-40/3) + exp (-1763/132) + exp (-602/45) + exp (-1849/138) + exp (-1892/141) + exp (-215/16) + exp (-1978/147) + exp (-2021/150) + exp (-688/51) + exp (-2107/156) + exp (-2150/159) + exp (-731/54) + exp (-2236/165) + exp (-2279/168) + exp (-258/19) + exp (-2365/174) + exp (-2408/177) + exp (-817/60) + exp (-2494/183) + exp (-2537/186)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  constructor
  · have h1 := a2_lower_43_part1
    have h2 := a2_lower_43_part2
    have h3 := a2_lower_43_part3
    have h4 := a2_lower_43_part4
    have h5 := a2_lower_43_part5
    linarith
  · have h1 := a2_upper_43_part1
    have h2 := a2_upper_43_part2
    have h3 := a2_upper_43_part3
    have h4 := a2_upper_43_part4
    have h5 := a2_upper_43_part5
    linarith

private theorem a2_lower_100 :
    (1 + 2420 / (10:ℝ)^7 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6) + exp (-200/9)) := by
  interval_decide 160

private theorem a2_upper_100 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/3) + exp (-40/3) + exp (-50/3) + exp (-400/21) + exp (-125/6) + exp (-200/9) + 135 * exp (-70/3)) ≤
    (1 + 2420 / (10:ℝ)^7 : ℝ) + (1:ℝ) / 10^7 := by
  interval_decide 170

private theorem a2_lower_150 :
    (1 + 3748 / (10:ℝ)^9 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/2) + exp (-20)) := by
  interval_decide 140

private theorem a2_upper_150 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25/2) + exp (-20) + 211 * exp (-25)) ≤
    (1 + 3748 / (10:ℝ)^9 : ℝ) + (1:ℝ) / 10^8 := by
  interval_decide 180

private theorem a2_lower_200 :
    (1 + 7713 / (10:ℝ)^11 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-50/3)) := by
  interval_decide 120

private theorem a2_upper_200 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-50/3) + 284 * exp (-80/3)) ≤
    (1 + 7713 / (10:ℝ)^11 : ℝ) + (1:ℝ) / 10^9 := by
  interval_decide 190

private theorem a2_lower_250 :
    (1 + 2025 / (10:ℝ)^11 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-125/6)) := by
  interval_decide 150

private theorem a2_upper_250 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-125/6) + 356 * exp (-100/3)) ≤
    (1 + 2025 / (10:ℝ)^11 : ℝ) + (1:ℝ) / 10^9 := by
  interval_decide 240

private theorem a2_lower_300 :
    (1 + 1937 / (10:ℝ)^11 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25)) := by
  interval_decide 180

private theorem a2_upper_300 :
    (1 + 193571378 / (10:ℝ)^16) * (1 + exp (-25) + 428 * exp (-40)) ≤
    (1 + 1937 / (10:ℝ)^11 : ℝ) + (1:ℝ) / 10^9 := by
  interval_decide 280

end LeanCert.Examples.BKLNW_a2
