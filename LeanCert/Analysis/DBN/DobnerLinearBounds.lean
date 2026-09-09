/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerGammaRatio
import LeanCert.Analysis.DBN.DobnerGammaReciprocal
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

namespace LeanCert.Analysis.DBN
open Complex Filter Set
open scoped Topology

/-- The linear-normalized Gamma quotient admits Gaussian growth throughout
its local sector, even when the relative error is not small. -/
theorem norm_xiGamma_linearRatio_le {s u : ℂ} (hr : 0 ≤ s.re+s.im/2)
    (hy : 4 ≤ s.im) (hu : ‖u‖ ≤ s.im/2) :
    ‖xiGamma (s+u)/xiGamma s * Complex.exp (-Complex.log (s/(2*Real.pi))*u/2)‖ ≤
      (9/4 : ℝ)*Real.exp 5 * Real.exp (9*‖u‖^2/(4*s.im)) := by
  let A := Complex.log (s/(2*Real.pi))*u/2
  let Q := u^2/(4*s)
  let R := xiGamma (s+u)/xiGamma s / Complex.exp (A+Q)
  have hyp : 0 < s.im := by linarith
  have hn : s.im ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_im_le_norm s)
  have hq : ‖Q‖ ≤ ‖u‖^2/(4*s.im) := by
    dsimp [Q]
    rw [norm_div, norm_pow, norm_mul, Complex.norm_ofNat]
    gcongr
  have hb := xiGamma_relative_error_bound hr hy hu
  have hR : ‖R‖ ≤ (1+‖u‖/s.im)^2 *
      Real.exp (GammaRatio.ratioError (s.im/2) (‖u‖/2)) := by
    have ht := norm_add_le (R-1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at ht
    change ‖R-1‖ ≤ _ at hb
    linarith
  have he : xiGamma (s+u)/xiGamma s * Complex.exp (-Complex.log (s/(2*Real.pi))*u/2) =
      R*Complex.exp Q := by
    dsimp [R, A]
    rw [show -Complex.log (s/(2*Real.pi))*u/2 = -(Complex.log (s/(2*Real.pi))*u/2) by ring]
    simp only [Complex.exp_add, Complex.exp_neg]
    field_simp
  have hhalf : ‖u‖/s.im ≤ 1/2 := (div_le_iff₀ hyp).mpr (by linarith)
  have hnon : 0 ≤ ‖u‖/s.im := by positivity
  have hpoly : (1+‖u‖/s.im)^2 ≤ (9/4 : ℝ) := by nlinarith
  have hd : GammaRatio.ratioError (s.im/2) (‖u‖/2) ≤ 5+2*‖u‖^2/s.im := by
    have heq : GammaRatio.ratioError (s.im/2) (‖u‖/2) =
        8*(‖u‖/s.im)+4*(‖u‖/s.im)^2+4*(‖u‖/s.im)*(‖u‖^2/s.im) := by
      unfold GammaRatio.ratioError
      ring
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ ‖u‖^2/s.im by positivity)
    have hsquare : (‖u‖/s.im)^2 ≤ (1/4 : ℝ) := by nlinarith
    calc
      _ ≤ 8*(1/2 : ℝ)+4*(1/4 : ℝ)+4*(1/2 : ℝ)*(‖u‖^2/s.im) := by nlinarith
      _ = _ := by ring
  rw [he, norm_mul]
  calc
    _ ≤ ((9/4 : ℝ)*Real.exp (5+2*‖u‖^2/s.im)) * Real.exp (‖u‖^2/(4*s.im)) := by
      apply mul_le_mul _ ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hq))
        (norm_nonneg _) (by positivity)
      exact hR.trans (mul_le_mul hpoly (Real.exp_le_exp.mpr hd) (Real.exp_pos _).le (by norm_num))
    _ = _ := by simp only [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Exponential reciprocal control before the Dobner chart correction. -/
theorem norm_inv_xiGamma_le_exp_on_strip (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 2 ≤ s.im →
      ‖(xiGamma s)⁻¹‖ ≤ C * Real.exp (Real.pi*s.im/2) := by
  obtain ⟨B, hB, hb⟩ := norm_inv_Gamma_le_exp_on_strip (M/2) (by positivity)
  refine ⟨2*Real.pi^(M/2)*B, by positivity, ?_⟩
  intro s hre him
  have him' : 1 ≤ |s.im| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hg : ‖(Complex.Gamma (s/2))⁻¹‖ ≤ B * Real.exp (Real.pi*s.im/2) := by
    have h := hb (s/2) (by simpa [abs_div] using (div_le_div_of_nonneg_right hre (by norm_num : (0 : ℝ) ≤ 2)))
      (by simp [abs_div, abs_of_nonneg (by linarith : 0 ≤ s.im)]; linarith)
    simpa [abs_div, abs_of_nonneg (by linarith : 0 ≤ s.im), mul_div_assoc] using h
  have hp : Real.pi^(s.re/2) ≤ Real.pi^(M/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (div_le_div_of_nonneg_right ((le_abs_self s.re).trans hre) (by norm_num))
  calc
    _ ≤ 2*Real.pi^(s.re/2)*‖(Complex.Gamma (s/2))⁻¹‖ := norm_inv_xiGamma_le him'
    _ ≤ 2*Real.pi^(M/2)*(B*Real.exp (Real.pi*s.im/2)) := by gcongr
    _ = _ := by ring

/-- An arbitrarily weak Gaussian growth bound for real Gamma on `[1,infinity)`.
The proof uses factorials and the elementary tangent bound for log, not Stirling. -/
theorem real_Gamma_le_exp_sq (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → Real.Gamma q ≤ C*Real.exp (ε*q^2) := by
  let δ := ε/8
  let A := |1+Real.log δ|
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hA : 0 ≤ A := abs_nonneg _
  refine ⟨Real.exp (2*A^2/ε), Real.exp_pos _, ?_⟩
  intro q hq
  have hqp : 0 < q := by linarith
  let n := Nat.ceil q
  have hnq : q ≤ (n : ℝ) := Nat.le_ceil q
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hqp hnq
  have hn2 : (n : ℝ) ≤ 2*q := by
    have ht := Nat.ceil_lt_add_one hqp.le
    change (n : ℝ) < q+1 at ht
    linarith
  have hG : Real.Gamma q ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ q*Real.Gamma q := le_mul_of_one_le_left (Real.Gamma_pos_of_pos hqp).le hq
      _ = Real.Gamma (q+1) := (Real.Gamma_add_one hqp.ne').symm
      _ ≤ Real.Gamma ((n : ℝ)+1) := Real.Gamma_strictMonoOn_Ici.monotoneOn
        (by simp; linarith) (by simp; linarith) (by linarith)
      _ = _ := Real.Gamma_nat_eq_factorial n
  have hlog : Real.log (n : ℝ) ≤ δ*(n : ℝ)+A := by
    have hh := Real.log_le_sub_one_of_pos (mul_pos hδ hnp)
    rw [Real.log_mul hδ.ne' hnp.ne'] at hh
    have ha := neg_abs_le (1+Real.log δ)
    dsimp [A]
    linarith
  have hnlog : (n : ℝ)*Real.log (n : ℝ) ≤ ε*q^2+2*A^2/ε := by
    have hmul := mul_le_mul_of_nonneg_left hlog hnp.le
    have hn2sq : (n : ℝ)^2 ≤ 4*q^2 := by nlinarith
    have hd := mul_le_mul_of_nonneg_left hn2sq hδ.le
    have ha := mul_le_mul_of_nonneg_left hn2 hA
    have hyoung : 2*A*q ≤ ε/2*q^2+2*A^2/ε := by
      apply (mul_le_mul_iff_right₀ hε).mp
      field_simp
      nlinarith [sq_nonneg (ε*q-2*A)]
    dsimp [δ] at hd hmul
    nlinarith
  calc
    _ ≤ (n : ℝ)^n := hG.trans (by exact_mod_cast Nat.factorial_le_pow n)
    _ = Real.exp ((n : ℝ)*Real.log (n : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hnp]
    _ ≤ Real.exp (ε*q^2+2*A^2/ε) := Real.exp_le_exp.mpr hnlog
    _ = _ := by rw [Real.exp_add]; ring

theorem one_add_sq_le_mul_exp (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    1+x^2 ≤ (1+1/ε)*Real.exp (ε*x^2) := by
  have h1 : 1 ≤ Real.exp (ε*x^2) := Real.one_le_exp (by positivity)
  have hx : x^2 ≤ Real.exp (ε*x^2)/ε := by
    apply (le_div_iff₀ hε).mpr
    have := Real.add_one_le_exp (ε*x^2)
    nlinarith
  calc
    _ ≤ Real.exp (ε*x^2)+Real.exp (ε*x^2)/ε := add_le_add h1 hx
    _ = _ := by ring

/-- Sub-Gaussian growth in the positive real coordinate, with only a quadratic
factor in the imaginary coordinate. -/
theorem norm_xiGamma_le_exp_sq (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 2 ≤ z.re →
      ‖xiGamma z‖ ≤ C*(1+z.im^2)*Real.exp (ε*z.re^2) := by
  obtain ⟨B, hB, hb⟩ := real_Gamma_le_exp_sq (2*ε) (by positivity)
  refine ⟨B*(1+1/(ε/2)), by positivity, ?_⟩
  intro z hz
  have hg : ‖Complex.Gamma (z/2)‖ ≤ B*Real.exp ((ε/2)*z.re^2) := by
    apply (norm_Gamma_le_real_Gamma (by simp only [div_ofNat_re]; linarith)).trans
    have h := hb (z.re/2) (by linarith)
    simpa only [div_ofNat_re, show 2*ε*(z.re/2)^2 = (ε/2)*z.re^2 by ring] using h
  have hp : ‖(Real.pi : ℂ)^(-z/2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [div_ofNat_re, neg_re]
    linarith
  have hpoly : ‖z‖*‖z-1‖/2 ≤ (1+z.re^2)*(1+z.im^2) := by
    have hh : ‖z-1‖ ≤ ‖z‖+1 := by simpa using norm_sub_le z (1 : ℂ)
    have hn : ‖z‖^2 = z.re^2+z.im^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_left hh (norm_nonneg z),
      sq_nonneg (‖z‖-1), mul_nonneg (sq_nonneg z.re) (sq_nonneg z.im)]
  have hnorm : ‖xiGamma z‖ = (‖z‖*‖z-1‖/2)*‖(Real.pi : ℂ)^(-z/2)‖*‖Complex.Gamma (z/2)‖ := by
    simp only [xiGamma, Gammaℝ_def, norm_div, norm_mul, Complex.norm_ofNat]
    ring
  rw [hnorm]
  calc
    _ ≤ ((1+z.re^2)*(1+z.im^2))*1*(B*Real.exp ((ε/2)*z.re^2)) := by gcongr
    _ ≤ (((1+1/(ε/2))*Real.exp ((ε/2)*z.re^2))*(1+z.im^2))*1*
        (B*Real.exp ((ε/2)*z.re^2)) := by
      gcongr
      exact one_add_sq_le_mul_exp (ε/2) (by positivity) z.re
    _ = _ := by
      have he : Real.exp ((ε/2)*z.re^2)*Real.exp ((ε/2)*z.re^2) = Real.exp (ε*z.re^2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc
        _ = B*(1+1/(ε/2))*(1+z.im^2)*
          (Real.exp ((ε/2)*z.re^2)*Real.exp ((ε/2)*z.re^2)) := by ring
        _ = _ := by rw [he]

end LeanCert.Analysis.DBN
