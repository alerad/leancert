/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Contour-shift certificates

This module provides a small certificate-facing wrapper around mathlib's
rectangle Cauchy-Goursat theorem.  The goal is to make orientation bookkeeping
explicit before adding residue automation.

The boundary convention is:

`bottom - top + I * right - I * left`.

Here `right` and `left` are real-parameter vertical integrals, so multiplying by
`I` converts them to complex contour integrals with the standard orientation.
-/

namespace LeanCert.Analysis.ContourShift

open Complex
open MeasureTheory
open Filter
open Topology
open scoped Real
open scoped BigOperators

/-- Bottom horizontal side of the rectangle from `z.re + z.im * I` to
`w.re + z.im * I`. -/
noncomputable def bottomIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ x : ℝ in z.re..w.re, f (x + z.im * I)

/-- Top horizontal side of the rectangle from `z.re + w.im * I` to
`w.re + w.im * I`.  It appears with a minus sign in the positive boundary. -/
noncomputable def topIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ x : ℝ in z.re..w.re, f (x + w.im * I)

/-- Right vertical side, parameterized upward from `z.im` to `w.im`. -/
noncomputable def rightIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ y : ℝ in z.im..w.im, f (w.re + y * I)

/-- Left vertical side, parameterized upward from `z.im` to `w.im`.
It appears with a minus sign in the positive boundary. -/
noncomputable def leftIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

/-- Positively oriented rectangle boundary integral in side-integral form. -/
noncomputable def rectBoundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  bottomIntegral f z w - topIntegral f z w +
    I * rightIntegral f z w - I * leftIntegral f z w

/--
Mathlib's rectangle Cauchy-Goursat theorem in LeanCert's named-side notation.
-/
theorem rectBoundary_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : DifferentiableOn ℂ f
      (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im))) :
    rectBoundary f z w = 0 := by
  simpa [rectBoundary, bottomIntegral, topIntegral, rightIntegral, leftIntegral]
    using Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z w Hc Hd

/--
A boundary identity certificate for one rectangle.

The residue side is deliberately supplied as data.  This lets contour-shift
users prove or import residue identities separately, while the shift algebra and
orientation bookkeeping are centralized here.
-/
structure VerticalShiftCert where
  f : ℂ → ℂ
  z : ℂ
  w : ℂ
  residueSum : ℂ
  boundary_eq :
    rectBoundary f z w = (2 * Real.pi * I) * residueSum

namespace VerticalShiftCert

/-- Algebraic vertical-shift identity induced by the boundary certificate. -/
theorem vertical_shift (C : VerticalShiftCert) :
    I * rightIntegral C.f C.z C.w =
      I * leftIntegral C.f C.z C.w +
        (2 * Real.pi * I) * C.residueSum -
          bottomIntegral C.f C.z C.w +
            topIntegral C.f C.z C.w := by
  have h := C.boundary_eq
  unfold rectBoundary at h
  rw [← h]
  ring

/-- Holomorphic rectangle certificates have zero residue side. -/
def ofHolomorphicRectangle
    (f : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : DifferentiableOn ℂ f
      (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im))) :
    VerticalShiftCert where
  f := f
  z := z
  w := w
  residueSum := 0
  boundary_eq := by
    simpa using rectBoundary_eq_zero_of_continuousOn_of_differentiableOn f z w Hc Hd

end VerticalShiftCert

/-! ## Shift-oriented finite and infinite certificates -/

/--
Vertical-line integral over the symmetric segment `[-T, T]`, oriented upward.
-/
noncomputable def verticalIntegral (F : ℂ → ℂ) (σ : ℝ) (T : ℝ) : ℂ :=
  ∫ t : ℝ in (-T)..T, F (σ + t * I) * I

/-- Top horizontal side from `σ₀ + T i` to `σ₁ + T i`. -/
noncomputable def topHorizontalIntegral (F : ℂ → ℂ) (σ₀ σ₁ T : ℝ) : ℂ :=
  ∫ x : ℝ in σ₀..σ₁, F (x + T * I)

/-- Bottom horizontal side from `σ₁ - T i` to `σ₀ - T i`. -/
noncomputable def bottomHorizontalIntegral (F : ℂ → ℂ) (σ₀ σ₁ T : ℝ) : ℂ :=
  ∫ x : ℝ in σ₁..σ₀, F (x - T * I)

/-- Finite pole data in a vertical strip. -/
structure StripPoleCert (F : ℂ → ℂ) (σ₀ σ₁ : ℝ) where
  poles : Finset ℂ
  in_strip : ∀ ρ ∈ poles, σ₀ < ρ.re ∧ ρ.re < σ₁
  residue : ℂ → ℂ

/-- Sum of finite residue data. -/
noncomputable def stripResidueSum {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (P : StripPoleCert F σ₀ σ₁) : ℂ :=
  ∑ ρ ∈ P.poles, P.residue ρ

/--
Finite rectangle shift certificate.

This structure intentionally stores the finite rectangle identity as data.  A
future residue-theorem constructor can produce this field, while the rest of the
contour-shift engine can already use it.
-/
structure RectangleShiftCert (F : ℂ → ℂ) (σ₀ σ₁ T : ℝ) where
  poles : Finset ℂ
  residue : ℂ → ℂ
  rectangle_identity :
    verticalIntegral F σ₀ T =
      verticalIntegral F σ₁ T -
        topHorizontalIntegral F σ₀ σ₁ T -
          bottomHorizontalIntegral F σ₀ σ₁ T +
            (2 * Real.pi * I) * ∑ ρ ∈ poles, residue ρ

namespace RectangleShiftCert

/-- Residue sum for a finite rectangle certificate. -/
noncomputable def residueSum {F : ℂ → ℂ} {σ₀ σ₁ T : ℝ}
    (C : RectangleShiftCert F σ₀ σ₁ T) : ℂ :=
  ∑ ρ ∈ C.poles, C.residue ρ

end RectangleShiftCert

/-- Horizontal sides vanish along a height sequence. -/
structure HorizontalVanishCert
    (F : ℂ → ℂ) (σ₀ σ₁ : ℝ) (T : ℕ → ℝ) where
  top_vanish :
    Tendsto (fun n => topHorizontalIntegral F σ₀ σ₁ (T n)) atTop (𝓝 0)
  bottom_vanish :
    Tendsto (fun n => bottomHorizontalIntegral F σ₀ σ₁ (T n)) atTop (𝓝 0)

/--
Horizontal vanishing from explicit norm bounds.

The conversion theorem is kept separate so users can either provide direct
vanishing or prove it by bounding both horizontal sides.
-/
structure HorizontalBoundCert
    (F : ℂ → ℂ) (σ₀ σ₁ : ℝ) (T : ℕ → ℝ) where
  bound : ℕ → ℝ
  bound_nonneg : ∀ n, 0 ≤ bound n
  bound_tendsto_zero : Tendsto bound atTop (𝓝 0)
  top_norm_le :
    ∀ n, ‖topHorizontalIntegral F σ₀ σ₁ (T n)‖ ≤ bound n
  bottom_norm_le :
    ∀ n, ‖bottomHorizontalIntegral F σ₀ σ₁ (T n)‖ ≤ bound n

namespace HorizontalBoundCert

/-- Norm-bound horizontal certificate implies horizontal vanishing. -/
theorem toVanishCert {F : ℂ → ℂ} {σ₀ σ₁ : ℝ} {T : ℕ → ℝ}
    (B : HorizontalBoundCert F σ₀ σ₁ T) :
    HorizontalVanishCert F σ₀ σ₁ T where
  top_vanish := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => B.top_norm_le n) B.bound_tendsto_zero
  bottom_vanish := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => B.bottom_norm_le n) B.bound_tendsto_zero

end HorizontalBoundCert

/--
Infinite contour-shift certificate.

This is the main reusable certificate object: finite rectangle identities are
provided for each height, horizontal sides vanish, vertical sides converge, and
finite pole data is stable across the sequence.
-/
structure ContourShiftCert (F : ℂ → ℂ) (σ₀ σ₁ : ℝ) where
  T : ℕ → ℝ
  hT_pos : ∀ n, 0 < T n
  hT_tendsto : Tendsto T atTop atTop
  poles : Finset ℂ
  residue : ℂ → ℂ
  rectCert : ∀ n, RectangleShiftCert F σ₀ σ₁ (T n)
  same_poles : ∀ n, (rectCert n).poles = poles
  same_residue : ∀ n ρ, (rectCert n).residue ρ = residue ρ
  left_limit :
    ∃ L₀ : ℂ, Tendsto (fun n => verticalIntegral F σ₀ (T n)) atTop (𝓝 L₀)
  right_limit :
    ∃ L₁ : ℂ, Tendsto (fun n => verticalIntegral F σ₁ (T n)) atTop (𝓝 L₁)
  horizontal : HorizontalVanishCert F σ₀ σ₁ T

namespace ContourShiftCert

/-- Chosen left vertical limit. -/
noncomputable def leftValue {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (C : ContourShiftCert F σ₀ σ₁) : ℂ :=
  Classical.choose C.left_limit

/-- Chosen right vertical limit. -/
noncomputable def rightValue {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (C : ContourShiftCert F σ₀ σ₁) : ℂ :=
  Classical.choose C.right_limit

/-- Stable finite residue sum for an infinite shift certificate. -/
noncomputable def residueSum {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (C : ContourShiftCert F σ₀ σ₁) : ℂ :=
  ∑ ρ ∈ C.poles, C.residue ρ

private theorem rectangle_identity_stable {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (C : ContourShiftCert F σ₀ σ₁) (n : ℕ) :
    verticalIntegral F σ₀ (C.T n) =
      verticalIntegral F σ₁ (C.T n) -
        topHorizontalIntegral F σ₀ σ₁ (C.T n) -
          bottomHorizontalIntegral F σ₀ σ₁ (C.T n) +
            (2 * Real.pi * I) * C.residueSum := by
  have h := (C.rectCert n).rectangle_identity
  have hsum :
      ∑ ρ ∈ (C.rectCert n).poles, (C.rectCert n).residue ρ =
        ∑ ρ ∈ C.poles, C.residue ρ := by
    rw [C.same_poles n]
    exact Finset.sum_congr rfl (fun ρ hρ => C.same_residue n ρ)
  simpa [ContourShiftCert.residueSum, hsum] using h

/-- Limit-passing contour-shift identity, existential-limit form. -/
theorem shift_identity {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (C : ContourShiftCert F σ₀ σ₁) :
    ∃ L₀ L₁ : ℂ,
      Tendsto (fun n => verticalIntegral F σ₀ (C.T n)) atTop (𝓝 L₀) ∧
      Tendsto (fun n => verticalIntegral F σ₁ (C.T n)) atTop (𝓝 L₁) ∧
      L₀ = L₁ + (2 * Real.pi * I) * C.residueSum := by
  rcases C.left_limit with ⟨L₀, hL₀⟩
  rcases C.right_limit with ⟨L₁, hL₁⟩
  refine ⟨L₀, L₁, hL₀, hL₁, ?_⟩
  let R : ℂ := (2 * Real.pi * I) * C.residueSum
  have hRhs :
      Tendsto
        (fun n =>
          verticalIntegral F σ₁ (C.T n) -
            topHorizontalIntegral F σ₀ σ₁ (C.T n) -
              bottomHorizontalIntegral F σ₀ σ₁ (C.T n) + R)
        atTop (𝓝 (L₁ - 0 - 0 + R)) :=
    ((hL₁.sub C.horizontal.top_vanish).sub C.horizontal.bottom_vanish).add
      tendsto_const_nhds
  have hRhs' :
      Tendsto
        (fun n =>
          verticalIntegral F σ₁ (C.T n) -
            topHorizontalIntegral F σ₀ σ₁ (C.T n) -
              bottomHorizontalIntegral F σ₀ σ₁ (C.T n) + R)
        atTop (𝓝 (L₁ + R)) := by
    simpa using hRhs
  have hfun :
      (fun n => verticalIntegral F σ₀ (C.T n)) =
        fun n =>
          verticalIntegral F σ₁ (C.T n) -
            topHorizontalIntegral F σ₀ σ₁ (C.T n) -
              bottomHorizontalIntegral F σ₀ σ₁ (C.T n) + R := by
    funext n
    simpa [R] using rectangle_identity_stable C n
  have hLeftToR : Tendsto (fun n => verticalIntegral F σ₀ (C.T n)) atTop
      (𝓝 (L₁ + R)) := by
    rw [hfun]
    exact hRhs'
  have huniq := tendsto_nhds_unique hL₀ hLeftToR
  simpa [R] using huniq

/-- Limit-passing contour-shift identity using chosen limit accessors. -/
theorem shift_identity' {F : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (C : ContourShiftCert F σ₀ σ₁) :
    C.leftValue = C.rightValue + (2 * Real.pi * I) * C.residueSum := by
  have hL₀ := Classical.choose_spec C.left_limit
  have hL₁ := Classical.choose_spec C.right_limit
  rcases C.shift_identity with ⟨L₀, L₁, h0, h1, hEq⟩
  have hLeft : C.leftValue = L₀ := tendsto_nhds_unique hL₀ h0
  have hRight : C.rightValue = L₁ := tendsto_nhds_unique hL₁ h1
  rw [hLeft, hRight]
  exact hEq

end ContourShiftCert

end LeanCert.Analysis.ContourShift
