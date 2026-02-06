/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.ReflectiveSum
import LeanCert.Examples.BKLNW_a2_bounds

/-!
# BKLNW a₂ Verified Bounds via Reflective Sum Evaluator

This module verifies the bounds stated in `BKLNW_a2_bounds.lean` using
reflective interval arithmetic with `native_decide`.

**Downstream projects should import `BKLNW_a2_bounds`, not this file.**

This file is only needed for LeanCert's CI to verify that the sorry'd bounds
in `BKLNW_a2_bounds.lean` are correct. Build time: ~5-10 minutes.

## How it works

1. `bklnwAlphaSumExpDyadic b limit cfg` computes an interval for (1+α)·f(exp(b))
2. `checkBKLNWAlphaExpUpperBound b limit target` verifies the bound via native computation
3. `native_decide` creates O(1) proof term by running the computation
4. Bridge theorems connect this to the mathematical statement
-/

namespace LeanCert.Examples.BKLNW_a2_reflective

open Real
open LeanCert.Engine
open LeanCert.Core
open LeanCert.Examples.BKLNW_a2_bounds (bklnwF f_eq_bklnwF_exp)
open LeanCert.Examples.BKLNW_a2_pow2 (f)

/-! ### Definition Compatibility -/

theorem bklnwF_eq_engine :
    BKLNW_a2_bounds.bklnwF = LeanCert.Engine.bklnwF := rfl

/-- The engine's alpha matches the PNT+ alpha -/
private lemma one_plus_alpha_eq :
    (1 + bklnwAlpha : ℝ) = 1 + 193571378 / (10:ℝ)^16 := by
  simp only [bklnwAlpha]
  push_cast
  ring

/-- Convert f(exp b) to Engine.bklnwF for a given floor value -/
private lemma f_to_engine (b N : ℕ) (hfloor : ⌊(b : ℝ) / log 2⌋₊ = N) :
    f (exp (b : ℝ)) = LeanCert.Engine.bklnwF (exp (b : ℝ)) N := by
  have h := f_eq_bklnwF_exp b
  rw [hfloor] at h
  rw [h, bklnwF_eq_engine]

/-! ### High-precision config -/

def proofConfig : BKLNWSumConfig := { precision := -100, taylorDepth := 18 }

/-! ### Verified Bounds

Each proof:
1. Rewrites f(exp b) to Engine.bklnwF(exp b, N) via floor lemma
2. Rewrites (1+α) to match Engine.bklnwAlpha
3. Applies the α bridge theorem with native_decide
4. Handles ℚ ↔ ℝ coercion via norm_num -/

private lemma alpha_lower_bridge (b N : ℕ) (target : ℚ)
    (hfloor : ⌊(b : ℝ) / log 2⌋₊ = N)
    (hb : b ≥ 1 := by norm_num)
    (hexppos : checkExpBLoGe1 b proofConfig.precision proofConfig.taylorDepth = true)
    (h_check : checkBKLNWAlphaExpLowerBound b N target proofConfig = true) :
    (target : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (b : ℝ)) := by
  rw [f_to_engine b N hfloor]
  rw [← one_plus_alpha_eq]
  exact verify_bklnwAlpha_exp_lower b N target proofConfig
    (by simp only [proofConfig]; norm_num) hb hexppos h_check

private lemma alpha_upper_bridge (b N : ℕ) (target : ℚ)
    (hfloor : ⌊(b : ℝ) / log 2⌋₊ = N)
    (hb : b ≥ 1 := by norm_num)
    (hexppos : checkExpBLoGe1 b proofConfig.precision proofConfig.taylorDepth = true)
    (h_check : checkBKLNWAlphaExpUpperBound b N target proofConfig = true) :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (b : ℝ)) ≤ (target : ℝ) := by
  rw [f_to_engine b N hfloor]
  rw [← one_plus_alpha_eq]
  exact verify_bklnwAlpha_exp_upper b N target proofConfig
    (by simp only [proofConfig]; norm_num) hb hexppos h_check

-- ═══════════════════════ b = 20 ═══════════════════════

theorem a2_20_exp_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) := by
  have h := alpha_lower_bridge 20 28 (14262/10000) BKLNW_a2_bounds.floor_20
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.4262 : ℝ) = ↑(14262 / 10000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_20_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  have h := alpha_upper_bridge 20 28 (14263/10000) BKLNW_a2_bounds.floor_20
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(14263 / 10000 : ℚ) := h
    _ = (1.4262 : ℝ) + (1:ℝ) / 10^4 := by push_cast; norm_num

-- ═══════════════════════ b = 25 ═══════════════════════

theorem a2_25_exp_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) := by
  have h := alpha_lower_bridge 25 36 (12195/10000) BKLNW_a2_bounds.floor_25
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.2195 : ℝ) = ↑(12195 / 10000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_25_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  have h := alpha_upper_bridge 25 36 (12196/10000) BKLNW_a2_bounds.floor_25
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(12196 / 10000 : ℚ) := h
    _ = (1.2195 : ℝ) + (1:ℝ) / 10^4 := by push_cast; norm_num

-- ═══════════════════════ b = 30 ═══════════════════════

theorem a2_30_exp_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) := by
  have h := alpha_lower_bridge 30 43 (11210/10000) BKLNW_a2_bounds.floor_30
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.1210 : ℝ) = ↑(11210 / 10000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_30_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  have h := alpha_upper_bridge 30 43 (11211/10000) BKLNW_a2_bounds.floor_30
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(11211 / 10000 : ℚ) := h
    _ = (1.1210 : ℝ) + (1:ℝ) / 10^4 := by push_cast; norm_num

-- ═══════════════════════ b = 35 ═══════════════════════

theorem a2_35_exp_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) := by
  have h := alpha_lower_bridge 35 50 (107086/100000) BKLNW_a2_bounds.floor_35
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.07086 : ℝ) = ↑(107086 / 100000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_35_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  have h := alpha_upper_bridge 35 50 (107087/100000) BKLNW_a2_bounds.floor_35
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(107087 / 100000 : ℚ) := h
    _ = (1.07086 : ℝ) + (1:ℝ) / 10^5 := by push_cast; norm_num

-- ═══════════════════════ b = 40 ═══════════════════════

theorem a2_40_exp_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) := by
  have h := alpha_lower_bridge 40 57 (104319/100000) BKLNW_a2_bounds.floor_40
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.04319 : ℝ) = ↑(104319 / 100000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_40_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  have h := alpha_upper_bridge 40 57 (104320/100000) BKLNW_a2_bounds.floor_40
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(104320 / 100000 : ℚ) := h
    _ = (1.04319 : ℝ) + (1:ℝ) / 10^5 := by push_cast; norm_num

-- ═══════════════════════ b = 43 ═══════════════════════

theorem a2_43_exp_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) := by
  have h := alpha_lower_bridge 43 62 (103252/100000) BKLNW_a2_bounds.floor_43
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.03252 : ℝ) = ↑(103252 / 100000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_43_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  have h := alpha_upper_bridge 43 62 (103253/100000) BKLNW_a2_bounds.floor_43
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(103253 / 100000 : ℚ) := h
    _ = (1.03252 : ℝ) + (1:ℝ) / 10^5 := by push_cast; norm_num

-- ═══════════════════════ b = 100 ═══════════════════════

theorem a2_100_exp_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) := by
  have h := alpha_lower_bridge 100 144 (10002420/10000000) BKLNW_a2_bounds.floor_100
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.0002420 : ℝ) = ↑(10002420 / 10000000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_100_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  have h := alpha_upper_bridge 100 144 (10002421/10000000) BKLNW_a2_bounds.floor_100
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(10002421 / 10000000 : ℚ) := h
    _ = (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by push_cast; norm_num

-- ═══════════════════════ b = 150 ═══════════════════════

theorem a2_150_exp_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) := by
  have h := alpha_lower_bridge 150 216 (1000003748/1000000000) BKLNW_a2_bounds.floor_150
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.000003748 : ℝ) = ↑(1000003748 / 1000000000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_150_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  have h := alpha_upper_bridge 150 216 (1000003758/1000000000) BKLNW_a2_bounds.floor_150
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(1000003758 / 1000000000 : ℚ) := h
    _ = (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by push_cast; norm_num

-- ═══════════════════════ b = 200 ═══════════════════════

theorem a2_200_exp_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) := by
  have h := alpha_lower_bridge 200 288 (100000007713/100000000000) BKLNW_a2_bounds.floor_200
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.00000007713 : ℝ) = ↑(100000007713 / 100000000000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_200_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  have h := alpha_upper_bridge 200 288 (100000007813/100000000000) BKLNW_a2_bounds.floor_200
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(100000007813 / 100000000000 : ℚ) := h
    _ = (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by push_cast; norm_num

-- ═══════════════════════ b = 250 ═══════════════════════

theorem a2_250_exp_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) := by
  have h := alpha_lower_bridge 250 360 (100000002025/100000000000) BKLNW_a2_bounds.floor_250
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.00000002025 : ℝ) = ↑(100000002025 / 100000000000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_250_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  have h := alpha_upper_bridge 250 360 (100000002125/100000000000) BKLNW_a2_bounds.floor_250
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(100000002125 / 100000000000 : ℚ) := h
    _ = (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by push_cast; norm_num

-- ═══════════════════════ b = 300 ═══════════════════════

theorem a2_300_exp_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) := by
  have h := alpha_lower_bridge 300 432 (100000001937/100000000000) BKLNW_a2_bounds.floor_300
    (by norm_num) (by native_decide) (by native_decide)
  calc (1.00000001937 : ℝ) = ↑(100000001937 / 100000000000 : ℚ) := by norm_num
    _ ≤ _ := h

theorem a2_300_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by
  have h := alpha_upper_bridge 300 432 (100000002037/100000000000) BKLNW_a2_bounds.floor_300
    (by norm_num) (by native_decide) (by native_decide)
  calc _ ≤ ↑(100000002037 / 100000000000 : ℚ) := h
    _ = (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by push_cast; norm_num

/-! ### Verified 2^M Bounds (pow certificates)

These verify (1+α)·f(2^M) ≤ target for the large-b entries (b=100,150,200,250,300)
where M = ⌊b/log2⌋₊ + 1. Same O(1) proof terms via native_decide. -/

/-- Convert f(2^M) to Engine.bklnwF for verification -/
private lemma f_pow_to_engine (M : Nat) :
    f ((2:ℝ)^(M:ℕ)) = LeanCert.Engine.bklnwF ((2:ℝ)^M) M := by
  have hfb := f_eq_bklnwF_exp M -- f(exp M) = bklnwF(exp M, ⌊M/log2⌋₊)
  -- Actually we need f(2^M) = bklnwF(2^M, M) directly
  unfold f
  rw [BKLNW_a2_pow2.floor_log_two_pow M]
  rfl

private lemma alpha_pow_upper_bridge (M : Nat) (target : ℚ)
    (h_check : LeanCert.Engine.checkBKLNWAlphaPowUpperBound M target proofConfig = true) :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(M:ℕ)) ≤ (target : ℝ) := by
  rw [f_pow_to_engine M, ← one_plus_alpha_eq]
  exact LeanCert.Engine.verify_bklnwAlpha_pow_upper M target proofConfig
    (by simp only [proofConfig]; norm_num) h_check

-- 2^145 (for b=100)
theorem pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(145:ℕ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  have h := alpha_pow_upper_bridge 145 (10002421/10000000) (by native_decide)
  calc _ ≤ ↑(10002421 / 10000000 : ℚ) := h
    _ = (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by push_cast; norm_num

-- 2^217 (for b=150)
theorem pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(217:ℕ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  have h := alpha_pow_upper_bridge 217 (1000003758/1000000000) (by native_decide)
  calc _ ≤ ↑(1000003758 / 1000000000 : ℚ) := h
    _ ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by push_cast; norm_num

-- 2^289 (for b=200)
theorem pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(289:ℕ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  have h := alpha_pow_upper_bridge 289 (100000007813/100000000000) (by native_decide)
  calc _ ≤ ↑(100000007813 / 100000000000 : ℚ) := h
    _ ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by push_cast; norm_num

-- 2^361 (for b=250)
theorem pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(361:ℕ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  have h := alpha_pow_upper_bridge 361 (100000002125/100000000000) (by native_decide)
  calc _ ≤ ↑(100000002125 / 100000000000 : ℚ) := h
    _ ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by push_cast; norm_num

-- 2^433 (for b=300)
theorem pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(433:ℕ)) ≤ (1.00000001938 : ℝ) + (1:ℝ) / 10^9 := by
  have h := alpha_pow_upper_bridge 433 (100000001948/100000000000) (by native_decide)
  calc _ ≤ ↑(100000001948 / 100000000000 : ℚ) := h
    _ ≤ (1.00000001938 : ℝ) + (1:ℝ) / 10^9 := by push_cast; norm_num

end LeanCert.Examples.BKLNW_a2_reflective
