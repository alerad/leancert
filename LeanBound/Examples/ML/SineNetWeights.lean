/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
/-!
# Trained Sine Approximator Network

This file contains the weights for a neural network trained to approximate sin(x).

- Architecture: 1 → 8 → 8 → 1 with ReLU activations
- Training domain: x ∈ [0, π]
- Weights exported as exact rational numbers
-/

import LeanBound.ML.Network

namespace LeanBound.Examples.ML.SineApprox

open LeanBound.ML

/-- Layer 1: 1 → 8 -/
def layer1Weights : List (List ℚ) := [
  [(1480 : ℚ) / 2361],
  [((-1927) : ℚ) / 9855],
  [(13784 : ℚ) / 8087],
  [(11302 : ℚ) / 7963],
  [((-2570) : ℚ) / 7761],
  [((-2842) : ℚ) / 8583],
  [(15557 : ℚ) / 6552],
  [((-8587) : ℚ) / 8380]
]

def layer1Bias : List ℚ := [
  ((-63) : ℚ) / 1639, 0, (1385 : ℚ) / 3863, ((-1459) : ℚ) / 4189, 0, 0, (26 : ℚ) / 237, ((-2971) : ℚ) / 2884
]

/-- Layer 2: 8 → 8 -/
def layer2Weights : List (List ℚ) := [
  [((-719) : ℚ) / 3063, (2113 : ℚ) / 7789, ((-1840) : ℚ) / 7941, ((-1077) : ℚ) / 4625, (873 : ℚ) / 7216, ((-9487) : ℚ) / 9917, ((-6559) : ℚ) / 7605, ((-1406) : ℚ) / 5001],
  [((-2447) : ℚ) / 4832, (1287 : ℚ) / 8191, ((-3095) : ℚ) / 6817, ((-1079) : ℚ) / 1528, (96 : ℚ) / 131, ((-1087) : ℚ) / 9629, (290 : ℚ) / 8589, ((-4951) : ℚ) / 6950],
  [((-10516) : ℚ) / 8615, (523 : ℚ) / 9430, ((-3639) : ℚ) / 2008, ((-15419) : ℚ) / 5668, ((-94) : ℚ) / 313, ((-1122) : ℚ) / 7693, ((-30905) : ℚ) / 9319, ((-3955) : ℚ) / 7334],
  [((-2) : ℚ) / 295, ((-4921) : ℚ) / 9305, (607 : ℚ) / 1574, ((-246) : ℚ) / 403, (919 : ℚ) / 8800, ((-1069) : ℚ) / 1091, ((-3067) : ℚ) / 4564, (715 : ℚ) / 7264],
  [(2249 : ℚ) / 6091, (325 : ℚ) / 3793, ((-194) : ℚ) / 3355, ((-1255) : ℚ) / 8336, ((-5662) : ℚ) / 7659, ((-185) : ℚ) / 514, ((-512) : ℚ) / 2223, (731 : ℚ) / 1383],
  [(487 : ℚ) / 8143, ((-8467) : ℚ) / 9605, ((-31) : ℚ) / 8040, ((-175) : ℚ) / 333, ((-22) : ℚ) / 65, (1954 : ℚ) / 6389, (997 : ℚ) / 6615, (2456 : ℚ) / 8231],
  [((-3625) : ℚ) / 8639, ((-1111) : ℚ) / 7186, (935 : ℚ) / 5697, (4049 : ℚ) / 8301, ((-1973) : ℚ) / 8235, ((-791) : ℚ) / 8521, ((-512) : ℚ) / 925, ((-4667) : ℚ) / 7803],
  [((-2501) : ℚ) / 7982, (5526 : ℚ) / 8149, ((-7473) : ℚ) / 7670, ((-5235) : ℚ) / 3071, (1397 : ℚ) / 7726, ((-2505) : ℚ) / 7766, ((-20989) : ℚ) / 9961, ((-557) : ℚ) / 1625]
]

def layer2Bias : List ℚ := [
  0, 0, ((-3035) : ℚ) / 4604, ((-270) : ℚ) / 4181, 0, ((-365) : ℚ) / 3467, ((-33) : ℚ) / 8146, ((-3727) : ℚ) / 7452
]

/-- Layer 3: 8 → 1 -/
def layer3Weights : List (List ℚ) := [
  [((-166) : ℚ) / 9267, (7231 : ℚ) / 9243, ((-11426) : ℚ) / 8859, (3482 : ℚ) / 8621, (209 : ℚ) / 4802, (13014 : ℚ) / 9245, (413 : ℚ) / 9221, (14475 : ℚ) / 8737]
]

def layer3Bias : List ℚ := [
  (6054 : ℚ) / 9707
]

def layer1 : Layer where
  weights := layer1Weights
  bias := layer1Bias

def layer2 : Layer where
  weights := layer2Weights
  bias := layer2Bias

def layer3 : Layer where
  weights := layer3Weights
  bias := layer3Bias

end LeanBound.Examples.ML.SineApprox