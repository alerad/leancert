/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.BKLNW_a2_reflective

/-!
# BKLNW a₂ Bounds

Public interface for BKLNW `(1+α)·f(exp b)` bounds. Historical downstream
names are preserved, but the theorem bodies now re-export the verified
reflective certificates rather than placeholder interfaces.
-/

open Real Finset

namespace LeanCert.Examples.BKLNW_a2_bounds

noncomputable abbrev f : ℝ → ℝ := LeanCert.Examples.BKLNW_a2_base.f
noncomputable abbrev bklnwF : ℝ → Nat → ℝ := LeanCert.Examples.BKLNW_a2_base.bklnwF

theorem floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := LeanCert.Examples.BKLNW_a2_base.floor_20
theorem floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := LeanCert.Examples.BKLNW_a2_base.floor_25
theorem floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := LeanCert.Examples.BKLNW_a2_base.floor_30
theorem floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := LeanCert.Examples.BKLNW_a2_base.floor_35
theorem floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := LeanCert.Examples.BKLNW_a2_base.floor_40
theorem floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := LeanCert.Examples.BKLNW_a2_base.floor_43
theorem floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := LeanCert.Examples.BKLNW_a2_base.floor_100
theorem floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := LeanCert.Examples.BKLNW_a2_base.floor_150
theorem floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := LeanCert.Examples.BKLNW_a2_base.floor_200
theorem floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := LeanCert.Examples.BKLNW_a2_base.floor_250
theorem floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := LeanCert.Examples.BKLNW_a2_base.floor_300

theorem f_eq_bklnwF_exp (b : ℕ) :
    f (exp b) = bklnwF (exp b) ⌊(b : ℝ) / log 2⌋₊ :=
  LeanCert.Examples.BKLNW_a2_base.f_eq_bklnwF_exp b

lemma a2_20_exp_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_20_exp_lower
lemma a2_20_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_20_exp_upper

lemma a2_25_exp_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_25_exp_lower
lemma a2_25_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_25_exp_upper

lemma a2_30_exp_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_30_exp_lower
lemma a2_30_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_30_exp_upper

lemma a2_35_exp_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_35_exp_lower
lemma a2_35_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_35_exp_upper

lemma a2_40_exp_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_40_exp_lower
lemma a2_40_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_40_exp_upper

lemma a2_43_exp_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_43_exp_lower
lemma a2_43_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_43_exp_upper

lemma a2_100_exp_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_100_exp_lower
lemma a2_100_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_100_exp_upper

lemma a2_150_exp_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_150_exp_lower
lemma a2_150_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_150_exp_upper

lemma a2_200_exp_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_200_exp_lower
lemma a2_200_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_200_exp_upper

lemma a2_250_exp_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_250_exp_lower
lemma a2_250_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_250_exp_upper

lemma a2_300_exp_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_300_exp_lower
lemma a2_300_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 :=
  LeanCert.Examples.BKLNW_a2_reflective.a2_300_exp_upper

end LeanCert.Examples.BKLNW_a2_bounds
