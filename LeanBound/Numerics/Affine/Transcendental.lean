/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.Affine.Nonlinear
import LeanBound.Core.IntervalRat.Taylor
import LeanBound.Numerics.IntervalEval

/-!
# Affine Arithmetic: Transcendental Functions

This file implements transcendental functions for Affine Arithmetic using
Chebyshev linearization combined with Taylor bounds.

## Key Functions

* `AffineForm.exp` - Exponential function
* `AffineForm.tanh` - Hyperbolic tangent (crucial for GELU)
* `AffineForm.log` - Natural logarithm (for LogSumExp)

## Linearization Strategy

For exp(x) on [a, b]:
1. The secant line through (a, e^a) and (b, e^b) gives an upper bound
2. The tangent at the midpoint gives a lower bound
3. We use the midpoint tangent as the linear approximation with error bounds

For tanh(x):
1. tanh is bounded in [-1, 1]
2. For small x, tanh(x) ≈ x is a good approximation
3. For larger x, we use the secant/tangent approach
-/

namespace LeanBound.Numerics.Affine

open LeanBound.Core

namespace AffineForm

/-! ## Exponential Function -/

/-- Exponential using interval evaluation (loses correlation).

    For tighter bounds, use `expChebyshev` which preserves linear terms.
-/
def exp (a : AffineForm) (taylorDepth : Nat := 8) : AffineForm :=
  let I := a.toInterval
  let expI := IntervalRat.expComputable I taylorDepth
  let mid := (expI.lo + expI.hi) / 2
  let rad := (expI.hi - expI.lo) / 2
  -- Use error term (coeffs = []) for soundness proof compatibility
  { c0 := mid
    coeffs := []
    r := |rad|
    r_nonneg := abs_nonneg _ }

/-- Chebyshev linearization for exp(x) on [lo, hi].

    Key insight: exp is convex, so the tangent line at any point is a lower bound.
    We use the tangent at the midpoint m:
      L(x) = e^m + e^m·(x - m) = e^m·(1 + x - m)

    The error is bounded by the difference between the secant and tangent.
-/
def expChebyshev (a : AffineForm) (taylorDepth : Nat := 8) : AffineForm :=
  let I := a.toInterval
  let lo := I.lo
  let hi := I.hi
  let m := (lo + hi) / 2

  -- Compute e^m using Taylor
  let exp_m_I := IntervalRat.expComputable ⟨m, m, le_refl _⟩ taylorDepth
  let exp_m := exp_m_I.lo  -- Lower bound on e^m (conservative for tangent)

  -- Tangent at m: L(x) = e^m + e^m·(x - m) = e^m·x + e^m·(1 - m)
  let α := exp_m  -- Slope
  let β := exp_m * (1 - m)  -- Intercept

  -- Error bound: max deviation from secant
  -- At endpoints: max(e^lo - L(lo), e^hi - L(hi), L(m) - e^m)
  let exp_lo_I := IntervalRat.expComputable ⟨lo, lo, le_refl _⟩ taylorDepth
  let exp_hi_I := IntervalRat.expComputable ⟨hi, hi, le_refl _⟩ taylorDepth

  -- Conservative error: (e^hi - e^lo) / 8 · (hi - lo)² (for small intervals)
  let width := hi - lo
  let δ := (exp_hi_I.hi - exp_lo_I.lo) * width * width / 8

  let scaled := scale α a
  let shifted := add scaled (const β)
  { c0 := shifted.c0
    coeffs := shifted.coeffs
    r := shifted.r + |δ|
    r_nonneg := by linarith [shifted.r_nonneg, abs_nonneg δ] }

/-! ## Hyperbolic Tangent -/

/-- tanh using interval evaluation.

    tanh(x) = (e^x - e^{-x}) / (e^x + e^{-x})
    Always bounded in (-1, 1).
-/
def tanh (a : AffineForm) : AffineForm :=
  let I := a.toInterval
  let tanhI := LeanBound.Numerics.tanhInterval I
  let mid := (tanhI.lo + tanhI.hi) / 2
  let rad := (tanhI.hi - tanhI.lo) / 2
  -- Use error term (coeffs = []) for soundness proof compatibility
  { c0 := mid
    coeffs := []
    r := |rad|
    r_nonneg := abs_nonneg _ }

/-- Chebyshev linearization for tanh(x).

    tanh'(x) = 1 - tanh²(x) = sech²(x)

    For small x: tanh(x) ≈ x with error O(x³)
    For large |x|: tanh(x) ≈ ±1

    We use the tangent at midpoint as approximation.
-/
def tanhChebyshev (a : AffineForm) : AffineForm :=
  let I := a.toInterval
  let lo := I.lo
  let hi := I.hi
  let m := (lo + hi) / 2

  -- Compute tanh(m) and tanh'(m) = 1 - tanh²(m)
  let tanh_m_I := LeanBound.Numerics.tanhInterval ⟨m, m, le_refl _⟩
  let tanh_m := (tanh_m_I.lo + tanh_m_I.hi) / 2
  let deriv := 1 - tanh_m * tanh_m  -- sech²(m)

  -- Tangent: L(x) = tanh(m) + deriv·(x - m)
  let α := deriv
  let β := tanh_m - deriv * m

  -- Error bound: for tanh, the second derivative is bounded
  -- |tanh''(x)| = |2·tanh(x)·sech²(x)| ≤ 2
  -- So error ≤ width² / 2
  let width := hi - lo
  let δ := width * width

  let scaled := scale α a
  let shifted := add scaled (const β)
  { c0 := shifted.c0
    coeffs := shifted.coeffs
    r := shifted.r + |δ|
    r_nonneg := by linarith [shifted.r_nonneg, abs_nonneg δ] }

/-! ## Natural Logarithm -/

/-- Logarithm using interval evaluation (requires positive input). -/
noncomputable def log (a : AffineForm) (_taylorDepth : Nat := 8) : AffineForm :=
  let I := a.toInterval
  if h : 0 < I.lo then
    let logI := IntervalRat.logInterval ⟨I, h⟩
    let mid := (logI.lo + logI.hi) / 2
    let rad := (logI.hi - logI.lo) / 2
    -- Use error term (coeffs = []) for soundness proof compatibility
    { c0 := mid
      coeffs := []
      r := |rad|
      r_nonneg := abs_nonneg _ }
  else
    -- Non-positive: undefined
    { c0 := 0, coeffs := [], r := 10^30, r_nonneg := by norm_num }

/-- Chebyshev linearization for log(x) on [lo, hi] with lo > 0.

    log'(x) = 1/x, so tangent at m is: L(x) = log(m) + (x - m)/m
-/
noncomputable def logChebyshev (a : AffineForm) (hpos : 0 < a.toInterval.lo) : AffineForm :=
  let I := a.toInterval
  let lo := I.lo
  let hi := I.hi
  let m := (lo + hi) / 2

  -- log(m) and 1/m
  -- m = (lo + hi)/2 > lo/2 > 0 since lo > 0
  have hm_pos : 0 < m := by
    simp only [m]
    have hlo_pos := hpos
    have hhi_ge := I.le
    linarith
  let log_m_I := IntervalRat.logInterval ⟨⟨m, m, le_refl _⟩, hm_pos⟩
  let log_m := (log_m_I.lo + log_m_I.hi) / 2

  -- Tangent: L(x) = log(m) + (x-m)/m = x/m + (log(m) - 1)
  let α := 1 / m
  let β := log_m - 1

  -- Error: |log''(x)| = 1/x² ≤ 1/lo² on [lo, hi]
  -- Error ≤ (hi - lo)² / (2·lo²)
  let width := hi - lo
  let δ := width * width / (2 * lo * lo)

  let scaled := scale α a
  let shifted := add scaled (const β)
  { c0 := shifted.c0
    coeffs := shifted.coeffs
    r := shifted.r + |δ|
    r_nonneg := by linarith [shifted.r_nonneg, abs_nonneg δ] }

/-! ## Hyperbolic Functions -/

/-- Hyperbolic sine: sinh(x) = (e^x - e^{-x})/2

    Computed via (exp(x) - exp(-x))/2.
-/
def sinh (a : AffineForm) (taylorDepth : Nat := 8) : AffineForm :=
  let I := a.toInterval
  let negI : IntervalRat := ⟨-I.hi, -I.lo, by linarith [I.le]⟩
  let expI := IntervalRat.expComputable I taylorDepth
  let expNegI := IntervalRat.expComputable negI taylorDepth
  -- sinh = (exp - expNeg) / 2
  let lo := (expI.lo - expNegI.hi) / 2
  let hi := (expI.hi - expNegI.lo) / 2
  let mid := (lo + hi) / 2
  let rad := (hi - lo) / 2
  -- Use error term (coeffs = []) for soundness proof compatibility
  { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }

/-- Hyperbolic cosine: cosh(x) = (e^x + e^{-x})/2

    Computed via (exp(x) + exp(-x))/2. Always ≥ 1.
-/
def cosh (a : AffineForm) (taylorDepth : Nat := 8) : AffineForm :=
  let I := a.toInterval
  let negI : IntervalRat := ⟨-I.hi, -I.lo, by linarith [I.le]⟩
  let expI := IntervalRat.expComputable I taylorDepth
  let expNegI := IntervalRat.expComputable negI taylorDepth
  -- cosh = (exp + expNeg) / 2
  let lo := (expI.lo + expNegI.lo) / 2
  let hi := (expI.hi + expNegI.hi) / 2
  let mid := (lo + hi) / 2
  let rad := (hi - lo) / 2
  -- Use error term (coeffs = []) for soundness proof compatibility
  { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }

/-! ## Soundness Theorems -/

/-- exp is sound -/
theorem mem_exp {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hlen : eps.length = a.coeffs.length)
    (hmem : mem_affine a eps v)
    (taylorDepth : Nat) :
    mem_affine (exp a taylorDepth) eps (Real.exp v) := by
  -- Get v ∈ a.toInterval
  have hv_in_I := mem_toInterval hvalid hlen hmem
  -- Get Real.exp v ∈ expComputable I
  have hexp_in := IntervalRat.mem_expComputable hv_in_I taylorDepth

  -- Set up the interval bounds
  let I := a.toInterval
  let expI := IntervalRat.expComputable I taylorDepth
  let mid := (expI.lo + expI.hi) / 2
  let rad := (expI.hi - expI.lo) / 2

  -- expI.le gives us expI.lo ≤ expI.hi
  have hrad_nonneg : 0 ≤ rad := by
    simp only [rad]
    linarith [expI.le]

  simp only [IntervalRat.mem_def] at hexp_in
  have hlo : (expI.lo : ℝ) ≤ Real.exp v := hexp_in.1
  have hhi : Real.exp v ≤ (expI.hi : ℝ) := hexp_in.2

  -- The result has coeffs = [], so evalLinear = c0 = mid
  simp only [exp, mem_affine, evalLinear, linearSum, List.zipWith, List.sum_nil, add_zero]

  -- We need |Real.exp v - mid| ≤ |rad|
  use Real.exp v - (mid : ℝ)
  constructor
  · -- |Real.exp v - mid| ≤ |rad|
    -- Since rad = (hi - lo)/2 ≥ 0, |rad| = rad
    have habs_eq : |((expI.hi - expI.lo) / 2 : ℚ)| = (expI.hi - expI.lo) / 2 := by
      rw [abs_of_nonneg]; linarith [expI.le]

    -- Rewrite the absolute value
    rw [habs_eq]

    -- Now prove |exp v - mid| ≤ rad directly using lo ≤ exp v ≤ hi
    -- After abs_le, goal is: -↑rad' ≤ exp v - ↑mid ∧ exp v - ↑mid ≤ ↑rad'
    -- where rad' = (expI.hi - expI.lo) / 2 (after simplification)
    rw [abs_le]

    -- Get the rational casts in a form linarith can handle
    have hmid_val : (mid : ℝ) = ((expI.lo : ℝ) + expI.hi) / 2 := by
      simp only [mid]; push_cast; ring
    have hrad_val : (((expI.hi - expI.lo) / 2 : ℚ) : ℝ) = ((expI.hi : ℝ) - expI.lo) / 2 := by
      push_cast; ring

    constructor
    · -- -rad ≤ exp v - mid, i.e., mid - rad ≤ exp v
      -- mid - rad = (lo + hi)/2 - (hi - lo)/2 = lo
      calc -(((expI.hi - expI.lo) / 2 : ℚ) : ℝ)
          = -((expI.hi : ℝ) - expI.lo) / 2 := by push_cast; ring
        _ = (expI.lo : ℝ) - ((expI.lo : ℝ) + expI.hi) / 2 := by ring
        _ = (expI.lo : ℝ) - (mid : ℝ) := by rw [← hmid_val]
        _ ≤ Real.exp v - (mid : ℝ) := by linarith
    · -- exp v - mid ≤ rad, i.e., exp v ≤ mid + rad
      -- mid + rad = (lo + hi)/2 + (hi - lo)/2 = hi
      calc Real.exp v - (mid : ℝ)
          ≤ (expI.hi : ℝ) - (mid : ℝ) := by linarith
        _ = (expI.hi : ℝ) - ((expI.lo : ℝ) + expI.hi) / 2 := by rw [hmid_val]
        _ = ((expI.hi : ℝ) - expI.lo) / 2 := by ring
        _ = (((expI.hi - expI.lo) / 2 : ℚ) : ℝ) := by push_cast; ring
  · ring

/-- tanh is sound -/
theorem mem_tanh {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hlen : eps.length = a.coeffs.length)
    (hmem : mem_affine a eps v) :
    mem_affine (tanh a) eps (Real.tanh v) := by
  -- Get v ∈ a.toInterval
  have hv_in_I := mem_toInterval hvalid hlen hmem
  -- Get Real.tanh v ∈ tanhInterval I = [-1, 1]
  have htanh_in := LeanBound.Numerics.mem_tanhInterval hv_in_I

  -- tanhInterval always returns [-1, 1], so mid = 0, rad = 1
  let tanhI := LeanBound.Numerics.tanhInterval a.toInterval
  let mid := (tanhI.lo + tanhI.hi) / 2
  let rad := (tanhI.hi - tanhI.lo) / 2

  -- The result has coeffs = [], so evalLinear = c0 = mid
  simp only [tanh, mem_affine, evalLinear, linearSum, List.zipWith, List.sum_nil, add_zero]

  simp only [IntervalRat.mem_def] at htanh_in
  have hlo : (tanhI.lo : ℝ) ≤ Real.tanh v := htanh_in.1
  have hhi : Real.tanh v ≤ (tanhI.hi : ℝ) := htanh_in.2

  use Real.tanh v - (mid : ℝ)
  constructor
  · -- |Real.tanh v - mid| ≤ |rad|
    have hrad_nonneg : 0 ≤ rad := by
      simp only [rad]; linarith [tanhI.le]
    have habs_eq : |((tanhI.hi - tanhI.lo) / 2 : ℚ)| = (tanhI.hi - tanhI.lo) / 2 := by
      rw [abs_of_nonneg]; linarith [tanhI.le]

    rw [habs_eq, abs_le]

    have hmid_val : (mid : ℝ) = ((tanhI.lo : ℝ) + tanhI.hi) / 2 := by
      simp only [mid]; push_cast; ring

    constructor
    · calc -(((tanhI.hi - tanhI.lo) / 2 : ℚ) : ℝ)
          = -((tanhI.hi : ℝ) - tanhI.lo) / 2 := by push_cast; ring
        _ = (tanhI.lo : ℝ) - ((tanhI.lo : ℝ) + tanhI.hi) / 2 := by ring
        _ = (tanhI.lo : ℝ) - (mid : ℝ) := by rw [← hmid_val]
        _ ≤ Real.tanh v - (mid : ℝ) := by linarith
    · calc Real.tanh v - (mid : ℝ)
          ≤ (tanhI.hi : ℝ) - (mid : ℝ) := by linarith
        _ = (tanhI.hi : ℝ) - ((tanhI.lo : ℝ) + tanhI.hi) / 2 := by rw [hmid_val]
        _ = ((tanhI.hi : ℝ) - tanhI.lo) / 2 := by ring
        _ = (((tanhI.hi - tanhI.lo) / 2 : ℚ) : ℝ) := by push_cast; ring
  · ring

/-- log is sound for positive inputs -/
theorem mem_log {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hlen : eps.length = a.coeffs.length)
    (hmem : mem_affine a eps v)
    (_hv_pos : 0 < v)
    (hI_pos : 0 < a.toInterval.lo)
    (_taylorDepth : Nat) :
    mem_affine (log a taylorDepth) eps (Real.log v) := by
  -- Get v ∈ a.toInterval
  have hv_in_I := mem_toInterval hvalid hlen hmem

  -- Construct the positive interval
  let I := a.toInterval
  let I_pos : IntervalRat.IntervalRatPos := ⟨I, hI_pos⟩

  -- Coerce membership proof to the IntervalRatPos type
  have hv_in_I_pos : v ∈ I_pos.toIntervalRat := hv_in_I

  -- Get Real.log v ∈ logInterval I_pos
  have hlog_in := IntervalRat.mem_logInterval hv_in_I_pos

  -- The logInterval
  let logI := IntervalRat.logInterval I_pos
  let mid := (logI.lo + logI.hi) / 2
  let rad := (logI.hi - logI.lo) / 2

  -- The result has coeffs = [], so evalLinear = c0 = mid
  simp only [log, dif_pos hI_pos, mem_affine, evalLinear, linearSum, List.zipWith, List.sum_nil, add_zero]

  simp only [IntervalRat.mem_def] at hlog_in
  have hlo : (logI.lo : ℝ) ≤ Real.log v := hlog_in.1
  have hhi : Real.log v ≤ (logI.hi : ℝ) := hlog_in.2

  use Real.log v - (mid : ℝ)
  constructor
  · -- |Real.log v - mid| ≤ |rad|
    have hrad_nonneg : 0 ≤ rad := by
      simp only [rad]; linarith [logI.le]
    have habs_eq : |((logI.hi - logI.lo) / 2 : ℚ)| = (logI.hi - logI.lo) / 2 := by
      rw [abs_of_nonneg]; linarith [logI.le]

    rw [habs_eq, abs_le]

    have hmid_val : (mid : ℝ) = ((logI.lo : ℝ) + logI.hi) / 2 := by
      simp only [mid]; push_cast; ring

    constructor
    · calc -(((logI.hi - logI.lo) / 2 : ℚ) : ℝ)
          = -((logI.hi : ℝ) - logI.lo) / 2 := by push_cast; ring
        _ = (logI.lo : ℝ) - ((logI.lo : ℝ) + logI.hi) / 2 := by ring
        _ = (logI.lo : ℝ) - (mid : ℝ) := by rw [← hmid_val]
        _ ≤ Real.log v - (mid : ℝ) := by linarith
    · calc Real.log v - (mid : ℝ)
          ≤ (logI.hi : ℝ) - (mid : ℝ) := by linarith
        _ = (logI.hi : ℝ) - ((logI.lo : ℝ) + logI.hi) / 2 := by rw [hmid_val]
        _ = ((logI.hi : ℝ) - logI.lo) / 2 := by ring
        _ = (((logI.hi - logI.lo) / 2 : ℚ) : ℝ) := by push_cast; ring
  · ring

end AffineForm

end LeanBound.Numerics.Affine
