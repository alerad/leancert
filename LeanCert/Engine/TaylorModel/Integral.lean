/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.Engine.TaylorModel.Core
import LeanCert.Engine.Integrate

/-!
# Taylor Model Integration

This module connects Taylor-model pointwise enclosures to certified interval
enclosures for definite integrals.

The first bridge is deliberately conservative: it integrates the global
Taylor-model range bound over the domain.  This is enough to certify interval
kernel banks and constant-factory observers today.  Tighter polynomial-exact
Taylor integration can be layered on top without changing this API.

The second bridge is the polynomial-exact enclosure shape used by certified
quadrature: if the integral of the Taylor polynomial is known exactly, the
only interval over-approximation comes from integrating the remainder interval.
-/

namespace LeanCert.Engine

open LeanCert.Core
open MeasureTheory
open scoped ENNReal

namespace TaylorModel

/--
Exact rational formula for integrating a shifted polynomial over `[a,b]`.

This is the computational primitive for polynomial-exact Taylor quadrature:

`∫ x in a..b, p(x-c) dx =
  Σ_i p_i ((b-c)^(i+1) - (a-c)^(i+1))/(i+1)`.
-/
noncomputable def integrateShiftedPoly (p : Polynomial ℚ) (a b c : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    p.coeff i *
      (((b - c) ^ (i + 1) - (a - c) ^ (i + 1)) / (i + 1 : ℚ))

/--
Polynomial-exact integral enclosure for a Taylor model over its own domain.

The polynomial part is integrated exactly by `integrateShiftedPoly`; the
remainder interval is scaled by the domain width.
-/
noncomputable def integralBoundPolyExact (tm : TaylorModel) : IntervalRat :=
  IntervalRat.add
    (IntervalRat.singleton
      (integrateShiftedPoly tm.poly tm.domain.lo tm.domain.hi tm.center))
    (IntervalRat.scale tm.domain.width tm.remainder)

/--
Coarse integral enclosure for a Taylor model over its own domain.

If `tm.bound = [lo, hi]` contains all values of `f` on `tm.domain`, this interval
is `[width * lo, width * hi]`, expressed through the standard interval product.
-/
noncomputable def integralBoundCoarse (tm : TaylorModel) : IntervalRat :=
  IntervalRat.mul (IntervalRat.singleton tm.domain.width) tm.bound

/--
Soundness of the coarse Taylor-model integral bound.

This theorem is intentionally phrased in terms of the Taylor-model semantic
predicate `evalSet`, so any Taylor-model construction that proves
`∀ x ∈ tm.domain, f x ∈ tm.evalSet x` can immediately produce an integral
certificate.
-/
theorem integral_mem_bound_coarse (tm : TaylorModel) (f : ℝ → ℝ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x)
    (hInt : IntervalIntegrable f volume tm.domain.lo tm.domain.hi) :
    ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x ∈
      integralBoundCoarse tm := by
  unfold integralBoundCoarse
  set fBound := tm.bound with hfBound_def
  have hbounds : ∀ x : ℝ, x ∈ tm.domain → f x ∈ fBound := by
    intro x hx
    simpa [hfBound_def] using (taylorModel_correct tm f hf x hx)
  have hlo : ∀ x ∈ Set.Icc (tm.domain.lo : ℝ) (tm.domain.hi : ℝ),
      (fBound.lo : ℝ) ≤ f x := by
    intro x hx
    exact (hbounds x hx).1
  have hhi : ∀ x ∈ Set.Icc (tm.domain.lo : ℝ) (tm.domain.hi : ℝ),
      f x ≤ (fBound.hi : ℝ) := by
    intro x hx
    exact (hbounds x hx).2
  have hIle : (tm.domain.lo : ℝ) ≤ tm.domain.hi := by
    exact_mod_cast tm.domain.le
  have ⟨h_lower, h_upper⟩ := integral_bounds_of_bounds hIle hInt hlo hhi
  have hwidth : (tm.domain.width : ℝ) =
      (tm.domain.hi : ℝ) - tm.domain.lo := by
    simp only [IntervalRat.width, Rat.cast_sub]
  have hwidth_nn : (0 : ℝ) ≤ tm.domain.width := by
    exact_mod_cast IntervalRat.width_nonneg tm.domain
  have hfBound_le : (fBound.lo : ℝ) ≤ fBound.hi := by
    exact_mod_cast fBound.le
  have h_lo' : (tm.domain.width : ℝ) * fBound.lo ≤
      ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x := by
    calc (tm.domain.width : ℝ) * fBound.lo = fBound.lo * tm.domain.width := by ring
       _ = fBound.lo * ((tm.domain.hi : ℝ) - tm.domain.lo) := by rw [hwidth]
       _ ≤ ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x := h_lower
  have h_hi' : ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x ≤
      (tm.domain.width : ℝ) * fBound.hi := by
    calc ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x
       ≤ fBound.hi * ((tm.domain.hi : ℝ) - tm.domain.lo) := h_upper
     _ = fBound.hi * tm.domain.width := by rw [hwidth]
     _ = (tm.domain.width : ℝ) * fBound.hi := by ring
  have hcorners : (tm.domain.width : ℝ) * fBound.lo ≤
      tm.domain.width * fBound.hi :=
    mul_le_mul_of_nonneg_left hfBound_le hwidth_nn
  rw [IntervalRat.mem_def]
  constructor
  · have hcorner : (IntervalRat.mul (IntervalRat.singleton tm.domain.width) fBound).lo =
        min (min (tm.domain.width * fBound.lo) (tm.domain.width * fBound.hi))
            (min (tm.domain.width * fBound.lo) (tm.domain.width * fBound.hi)) := rfl
    simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
    calc (↑tm.domain.width * ↑fBound.lo) ⊓ (↑tm.domain.width * ↑fBound.hi)
        = ↑tm.domain.width * ↑fBound.lo := min_eq_left hcorners
      _ ≤ ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x := h_lo'
  · have hcorner : (IntervalRat.mul (IntervalRat.singleton tm.domain.width) fBound).hi =
        max (max (tm.domain.width * fBound.lo) (tm.domain.width * fBound.hi))
            (max (tm.domain.width * fBound.lo) (tm.domain.width * fBound.hi)) := rfl
    simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
    calc ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x
        ≤ ↑tm.domain.width * ↑fBound.hi := h_hi'
      _ = (↑tm.domain.width * ↑fBound.lo) ⊔ (↑tm.domain.width * ↑fBound.hi) :=
          (max_eq_right hcorners).symm

/--
Soundness of the polynomial-exact Taylor-model integral bound, assuming the
Taylor polynomial integral has been identified with `integrateShiftedPoly`.

The assumption `hPolyIntegral` is intentionally explicit: the reusable numeric
soundness theorem here is the interval/remainder part of Taylor quadrature,
while callers may discharge the polynomial antiderivative equality using the
best local polynomial API available for their representation.
-/
theorem integral_mem_bound_polyExact_of_poly_integral (tm : TaylorModel) (f : ℝ → ℝ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x)
    (hInt : IntervalIntegrable f volume (tm.domain.lo : ℝ) (tm.domain.hi : ℝ))
    (hPolyInt : IntervalIntegrable tm.evalPoly volume
      (tm.domain.lo : ℝ) (tm.domain.hi : ℝ))
    (hPolyIntegral :
      ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), tm.evalPoly x =
        (integrateShiftedPoly tm.poly tm.domain.lo tm.domain.hi tm.center : ℝ)) :
    ∫ x in (tm.domain.lo : ℝ)..(tm.domain.hi : ℝ), f x ∈
      integralBoundPolyExact tm := by
  unfold integralBoundPolyExact
  set a : ℝ := (tm.domain.lo : ℝ)
  set b : ℝ := (tm.domain.hi : ℝ)
  set pInt : ℚ := integrateShiftedPoly tm.poly tm.domain.lo tm.domain.hi tm.center
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast tm.domain.le
  have hwidth : (tm.domain.width : ℝ) = b - a := by
    dsimp [a, b]
    simp only [IntervalRat.width, Rat.cast_sub]
  have hpoly_lower : IntervalIntegrable
      (fun x => tm.evalPoly x + (tm.remainder.lo : ℝ)) volume a b := by
    dsimp [a, b]
    exact hPolyInt.add (Continuous.intervalIntegrable continuous_const _ _)
  have hpoly_upper : IntervalIntegrable
      (fun x => tm.evalPoly x + (tm.remainder.hi : ℝ)) volume a b := by
    dsimp [a, b]
    exact hPolyInt.add (Continuous.intervalIntegrable continuous_const _ _)
  have hrem_bounds : ∀ x ∈ Set.Icc a b,
      tm.evalPoly x + (tm.remainder.lo : ℝ) ≤ f x ∧
        f x ≤ tm.evalPoly x + (tm.remainder.hi : ℝ) := by
    intro x hx
    have hxDomain : x ∈ tm.domain := by
      simpa [a, b] using hx
    rcases hf x hxDomain with ⟨r, hr, hfx⟩
    rw [hfx]
    simp only [TaylorModel.evalPoly]
    have hrl : (tm.remainder.lo : ℝ) ≤ r := hr.1
    have hrh : r ≤ (tm.remainder.hi : ℝ) := hr.2
    constructor <;> linarith
  have h_lower_int :
      ∫ x in a..b, tm.evalPoly x + (tm.remainder.lo : ℝ) ≤
        ∫ x in a..b, f x := by
    exact intervalIntegral.integral_mono_on hab hpoly_lower
      (by simpa [a, b] using hInt) (fun x hx => (hrem_bounds x hx).1)
  have h_upper_int :
      ∫ x in a..b, f x ≤
        ∫ x in a..b, tm.evalPoly x + (tm.remainder.hi : ℝ) := by
    exact intervalIntegral.integral_mono_on hab
      (by simpa [a, b] using hInt) hpoly_upper (fun x hx => (hrem_bounds x hx).2)
  have hpoly_lower_eval :
      ∫ x in a..b, tm.evalPoly x + (tm.remainder.lo : ℝ) =
        (pInt : ℝ) + (b - a) * tm.remainder.lo := by
    dsimp [a, b, pInt]
    rw [intervalIntegral.integral_add hPolyInt
      (Continuous.intervalIntegrable continuous_const _ _), hPolyIntegral]
    simp [a, b, pInt, intervalIntegral.integral_const, mul_comm]
  have hpoly_upper_eval :
      ∫ x in a..b, tm.evalPoly x + (tm.remainder.hi : ℝ) =
        (pInt : ℝ) + (b - a) * tm.remainder.hi := by
    dsimp [a, b, pInt]
    rw [intervalIntegral.integral_add hPolyInt
      (Continuous.intervalIntegrable continuous_const _ _), hPolyIntegral]
    simp [a, b, pInt, intervalIntegral.integral_const, mul_comm]
  rw [IntervalRat.mem_def]
  have hscale_lower :
      ((IntervalRat.scale tm.domain.width tm.remainder).lo : ℝ) ≤
        tm.domain.width * tm.remainder.lo := by
    exact (IntervalRat.mem_scale tm.domain.width
      (show (tm.remainder.lo : ℝ) ∈ tm.remainder from
        ⟨by rfl, by exact_mod_cast tm.remainder.le⟩)).1
  have hscale_upper :
      (tm.domain.width : ℝ) * tm.remainder.hi ≤
        (IntervalRat.scale tm.domain.width tm.remainder).hi := by
    exact (IntervalRat.mem_scale tm.domain.width
      (show (tm.remainder.hi : ℝ) ∈ tm.remainder from
        ⟨by exact_mod_cast tm.remainder.le, by rfl⟩)).2
  constructor
  · simp only [IntervalRat.add, IntervalRat.singleton, Rat.cast_add]
    calc
      (pInt : ℝ) + (IntervalRat.scale tm.domain.width tm.remainder).lo
          ≤ (pInt : ℝ) + tm.domain.width * tm.remainder.lo := by
            gcongr
      _ = (pInt : ℝ) + (b - a) * tm.remainder.lo := by rw [hwidth]
      _ = ∫ x in a..b, tm.evalPoly x + (tm.remainder.lo : ℝ) := hpoly_lower_eval.symm
      _ ≤ ∫ x in a..b, f x := h_lower_int
  · simp only [IntervalRat.add, IntervalRat.singleton, Rat.cast_add]
    calc
      ∫ x in a..b, f x
          ≤ ∫ x in a..b, tm.evalPoly x + (tm.remainder.hi : ℝ) := h_upper_int
      _ = (pInt : ℝ) + (b - a) * tm.remainder.hi := hpoly_upper_eval
      _ = (pInt : ℝ) + tm.domain.width * tm.remainder.hi := by rw [hwidth]
      _ ≤ (pInt : ℝ) + (IntervalRat.scale tm.domain.width tm.remainder).hi := by
            gcongr

end TaylorModel
end LeanCert.Engine
