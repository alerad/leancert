/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Transformer
import LeanCert.Engine.Affine.Vector

/-!
# Affine Arithmetic LayerNorm for ML

This file bridges the ML Transformer module with the Affine Arithmetic module,
providing **tight bounds** for LayerNorm by preserving correlations.

## The Problem with Standard Interval Arithmetic

Standard interval arithmetic loses correlations between variables. In LayerNorm:
- `μ = mean(x)` depends on all `x_i`
- `x_i - μ` should be small when all inputs are similar
- But interval arithmetic treats `x_i` and `μ` as independent!

Example: If `x_i ∈ [0.9, 1.1]` for all i:
- Standard: `μ ∈ [0.9, 1.1]`, so `x_i - μ ∈ [-0.2, 0.2]` (4x overestimate!)
- Affine: Tracks that `μ` comes from the same `x_i`, giving `x_i - μ ≈ 0`

## Solution: Affine Arithmetic

Affine forms track symbolic dependencies via noise symbols:
- `x_i = c₀ + c₁·ε₁ + c₂·ε₂ + ... + [-r, r]`
- Shared `ε_i` across variables preserve correlations
- When we compute `x - mean(x)`, the common terms cancel!

## Main Definitions

* `LayerNormParams.forwardAffine` - LayerNorm using affine arithmetic
* `LayerNormParams.forwardIntervalTight` - Convert affine result back to intervals

## References

* de Figueiredo & Stolfi, "Affine Arithmetic: Concepts and Applications", 2004
-/

namespace LeanCert.ML.Transformer

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Affine

/-! ## Affine LayerNorm Forward Pass -/

namespace LayerNormParams

/-- Forward pass using affine arithmetic for tight bounds.

    This converts the input intervals to affine forms, computes LayerNorm
    while preserving correlations, then extracts the resulting intervals.

    Key advantage: The centering step `x - μ` preserves correlations,
    giving much tighter bounds than standard interval arithmetic.
-/
def forwardAffine (params : LayerNormParams) (Is : IntervalVector)
    : AffineVector :=
  -- Convert intervals to affine forms with unique noise symbols per element
  let affine_input := AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat)
  -- Use the affine LayerNorm implementation
  AffineVector.layerNorm affine_input params.gamma params.beta params.epsilon

/-- Convert affine output back to intervals.

    This extracts conservative interval bounds from the affine forms.
    The bounds are tight because correlations were preserved during computation.
-/
def forwardIntervalTight (params : LayerNormParams) (Is : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  let affine_result := params.forwardAffine Is
  -- Convert each affine form back to an interval
  affine_result.map (fun af =>
    IntervalDyadic.ofIntervalRat af.toInterval prec)

/-! ## Comparison: Interval vs Affine Bounds -/

/-- Compute both interval and affine bounds for comparison.

    Returns (interval_bounds, affine_bounds) for the same input.
    The affine bounds should be tighter, especially for centering. -/
def compareBounds (params : LayerNormParams) (Is : IntervalVector) (prec : Int := -53)
    : IntervalVector × IntervalVector :=
  let interval_result := params.forwardInterval Is prec
  let affine_result := params.forwardIntervalTight Is prec
  (interval_result, affine_result)

/-- Measure the tightness improvement from affine arithmetic.

    Returns the ratio of interval width to affine width for each output dimension.
    Values > 1 indicate affine is tighter. -/
def tightnessRatio (params : LayerNormParams) (Is : IntervalVector) (prec : Int := -53)
    : List ℚ :=
  let (interval_bounds, affine_bounds) := params.compareBounds Is prec
  List.zipWith (fun I_int I_aff =>
    let w_int := I_int.hi.toRat - I_int.lo.toRat
    let w_aff := I_aff.hi.toRat - I_aff.lo.toRat
    if w_aff = 0 then 1000  -- Affine gave exact bound
    else w_int / w_aff
  ) interval_bounds affine_bounds

end LayerNormParams

/-! ## Soundness Theorem -/

/-- The affine LayerNorm is sound: if inputs are in the affine forms,
    then outputs are in the resulting affine forms.

    This follows from composition of:
    - `AffineVector.mem_centered` - centering preserves membership
    - `AffineVector.mem_variance` - variance is sound
    - `AffineForm.mem_add` - addition is sound
    - `AffineForm.mem_sqrt` - square root is sound
    - `AffineForm.mem_inv` - inversion is sound
    - `AffineForm.mem_mul`, `AffineForm.mem_scale`, `AffineForm.mem_add` - final combination

    The proof requires additional hypotheses about positivity of variance + epsilon
    and compatibility of lengths, which are handled in the implementation.
-/
theorem mem_forwardAffine {xs : List ℝ} {Is : IntervalVector}
    (params : LayerNormParams)
    (eps : AffineForm.NoiseAssignment)
    (hvalid : AffineForm.validNoise eps)
    (hmem : AffineVector.mem xs (AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat)) eps)
    (hne : ¬(AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat)).isEmpty)
    (hlen_eps :
      eps.length =
        (AffineVector.variance (AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat))
          |>.add (AffineForm.const params.epsilon)).coeffs.length)
    (hlen_sqrt :
      eps.length =
        ((AffineVector.variance (AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat))
          |>.add (AffineForm.const params.epsilon)) |> AffineForm.sqrt).coeffs.length)
    (hsqrt_pos :
      0 <
        ((AffineVector.variance (AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat))
          |>.add (AffineForm.const params.epsilon)) |> AffineForm.sqrt).toInterval.lo) :
    let ys := layerNormReal xs params.gamma params.beta params.epsilon
    AffineVector.mem ys (params.forwardAffine Is) eps := by
  simpa [LayerNormParams.forwardAffine] using
    (AffineVector.mem_layerNorm (v_real := xs)
      (v := AffineVector.ofIntervals (Is.map IntervalDyadic.toIntervalRat))
      (gamma := params.gamma) (beta := params.beta) (epsilon := params.epsilon)
      params.epsilon_pos hvalid hmem hne hlen_eps hlen_sqrt hsqrt_pos)

/-! ## FFNBlock and TransformerBlock with Affine Arithmetic -/

/-- FFNBlock forward pass using affine arithmetic where beneficial.

    Uses affine arithmetic for LayerNorm (where correlation matters),
    standard intervals for linear layers (where it doesn't). -/
def FFNBlock.forwardIntervalTight (blk : FFNBlock) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  -- Linear layers don't benefit much from affine arithmetic
  -- (no internal correlations to track)
  let hidden := blk.linear1.forwardInterval x prec
  let activated := geluVector hidden prec
  blk.linear2.forwardInterval activated prec

/-- TransformerBlock forward pass with tight LayerNorm bounds.

    Uses affine arithmetic for LayerNorm to avoid the dependency problem. -/
def TransformerBlock.forwardIntervalTight (blk : TransformerBlock) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  -- Pre-norm with affine arithmetic for tighter bounds
  let x_norm := blk.ln1.forwardIntervalTight x prec

  -- Feed-forward with GELU (standard intervals OK here)
  let ff_out := blk.ffn.forwardInterval x_norm prec

  -- Residual connection
  let residual := LeanCert.Engine.IntervalVector.add x ff_out

  -- Post-norm with affine arithmetic
  blk.ln2.forwardIntervalTight residual prec

end LeanCert.ML.Transformer
