/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.XiIdentity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Group.Bounded

/-! Geometry of the negative-time logarithmic coordinate change.
This module does not assert the saddle-point approximation. -/
namespace LeanCert.Analysis.DBN
open Complex Filter Set
open scoped Topology

/-- Conversion from the s-plane back to the repository's cosine coordinate. -/
noncomputable def heatCoordinate (s : ℂ) : ℂ := (2*s-1)/I

/-- Completed heat function in the classical xi normalization. -/
noncomputable def xiHeat (t : ℝ) (s : ℂ) : ℂ := 8 * H t (heatCoordinate s)

@[simp] theorem heatCoordinate_im (s : ℂ) : (heatCoordinate s).im = 1-2*s.re := by
  simp [heatCoordinate, div_I, Complex.mul_im]

theorem xiHeat_zero (s : ℂ) : xiHeat 0 s = riemannXi s := by
  rw [xiHeat, H_zero_eq_riemannXi]
  have he : (1/2 : ℂ) + I * heatCoordinate s / 2 = s := by
    unfold heatCoordinate
    field_simp
    ring
  rw [he]
  ring

/-- The Dobner chart for a=-t/4>0. -/
noncomputable def dobnerMap (a : ℝ) (s : ℂ) : ℂ :=
  s + (a : ℂ)*Complex.log (s/(2*Real.pi : ℂ))

theorem dobnerMap_re (a : ℝ) (s : ℂ) :
    (dobnerMap a s).re = s.re + a*Real.log ‖s/(2*Real.pi : ℂ)‖ := by
  simp [dobnerMap, Complex.mul_re, Complex.log_re]

/-- A concrete height threshold moves a left-bounded strip strictly to the
right of the critical line. -/
theorem dobnerMap_re_gt_half {a R : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : -R ≤ s.re)
    (hh : 2*Real.pi*Real.exp ((R+1)/a) ≤ |s.im|) :
    (1/2 : ℝ) < (dobnerMap a s).re := by
  have hp : 0 < 2*Real.pi := by positivity
  have hn : Real.exp ((R+1)/a) ≤ ‖s/(2*Real.pi : ℂ)‖ := by
    rw [norm_div]
    have he : ‖(2*Real.pi : ℂ)‖ = 2*Real.pi := by
      norm_cast
      exact abs_of_pos hp
    rw [he]
    apply (le_div_iff₀ hp).mpr
    have := Complex.abs_im_le_norm s
    nlinarith
  have hl := Real.log_le_log (Real.exp_pos _) hn
  rw [Real.log_exp] at hl
  have he : a*((R+1)/a) = R+1 := by field_simp
  rw [dobnerMap_re]
  nlinarith [mul_le_mul_of_nonneg_left hl ha.le]

/-- A zero to the right of the critical line is a nonreal heat zero. -/
theorem nonreal_heat_zero_of_xiHeat_zero {t : ℝ} {s : ℂ}
    (hz : xiHeat t s = 0) (hs : (1/2 : ℝ) < s.re) :
    H t (heatCoordinate s) = 0 ∧ (heatCoordinate s).im ≠ 0 := by
  constructor
  · simpa only [xiHeat, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using hz
  · rw [heatCoordinate_im]
    linarith

/-- On every fixed compact set, unbounded upward translations eventually land
to the right of the critical line after the Dobner chart. -/
theorem eventually_dobnerMap_right_on_compact {a : ℝ} (ha : 0 < a)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop) {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ s ∈ K, (1/2 : ℝ) < (dobnerMap a (s+(τ n : ℂ)*I)).re := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  filter_upwards [hτ.eventually (eventually_ge_atTop
    (2*Real.pi*Real.exp ((R+1)/a)+R))] with n hn s hs
  have hre : -R ≤ s.re := by
    have := Complex.abs_re_le_norm s
    have := neg_abs_le s.re
    have := hR s hs
    linarith
  have him : -R ≤ s.im := by
    have := Complex.abs_im_le_norm s
    have := neg_abs_le s.im
    have := hR s hs
    linarith
  apply dobnerMap_re_gt_half ha (R := R)
  · simpa using hre
  · have habs := le_abs_self (s.im+τ n)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith

end LeanCert.Analysis.DBN
