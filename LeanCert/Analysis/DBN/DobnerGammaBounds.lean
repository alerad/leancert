/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerNormalization
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute Gamma bounds on the initial contour. These do not constitute
sectorial Stirling estimates or the Dobner saddle-point approximation. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set

theorem norm_Gamma_le_real_Gamma {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx (s-1)]
  simp

theorem norm_xiGamma_re_two {s : ℂ} (hs : s.re = 2) :
    ‖xiGamma s‖ ≤ (‖s‖+1)^2/(2*Real.pi) := by
  have hG : ‖Complex.Gamma (s/2)‖ ≤ 1 := by
    have h := norm_Gamma_le_real_Gamma (s := s/2) (by simp [hs])
    simpa [hs] using h
  have hp : ‖(Real.pi : ℂ)^(-s/2)‖ = Real.pi⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp [hs, Real.rpow_neg_one]
  have hb : ‖Gammaℝ s‖ ≤ Real.pi⁻¹ := by
    rw [Gammaℝ_def, norm_mul, hp]
    simpa using mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr Real.pi_pos.le)
  have hsub : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s (1 : ℂ)
  have hpoly : ‖s‖*‖s-1‖ ≤ (‖s‖+1)^2 := by
    nlinarith [norm_nonneg s, norm_nonneg (s-1)]
  rw [xiGamma, norm_div, norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    ‖s‖*‖s-1‖*‖Gammaℝ s‖/2 ≤ (‖s‖+1)^2*Real.pi⁻¹/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hpoly hb (norm_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- A simple polynomial bound on the original contour; it is enough for
Gaussian-weighted integrability, but not for normalized relative errors. -/
theorem norm_xiGamma_vertical (y : ℝ) :
    ‖xiGamma (2+(y : ℂ)*I)‖ ≤ (3+|y|)^2 := by
  have h := norm_xiGamma_re_two (s := 2+(y : ℂ)*I) (by simp)
  have hn : ‖(2 : ℂ)+(y : ℂ)*I‖ ≤ 2+|y| := by
    simpa [norm_mul] using norm_add_le (2 : ℂ) ((y : ℂ)*I)
  have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  apply h.trans
  apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
  nlinarith [norm_nonneg ((2 : ℂ)+(y : ℂ)*I), abs_nonneg y,
    mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (3+|y|))]

end LeanCert.Analysis.DBN
