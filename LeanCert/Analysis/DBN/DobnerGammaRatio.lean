/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.GammaRatio
import LeanCert.Analysis.DBN.DobnerContourShift

/-! Quantitative relative estimates for the actual DBN Gamma normalization. -/
namespace LeanCert.Analysis.DBN
open Complex Filter
open scoped Topology

private theorem log_scaled_half {s : ℂ} (hs : s ≠ 0) :
    Complex.log (s/(2*Real.pi)) = Complex.log (s/2)-(Real.log Real.pi : ℂ) := by
  have he : s/(2*Real.pi) = ((Real.pi⁻¹ : ℝ) : ℂ)*(s/2) := by push_cast; ring
  rw [he, Complex.log_ofReal_mul (by positivity) (div_ne_zero hs (by norm_num)),
    Real.log_inv, Complex.ofReal_neg]
  ring

/-- Exact polynomial and Gamma-ratio factorization; all principal-log branch
identities are justified before any estimates are made. -/
theorem xiGamma_relative_factorization {s : ℂ} (hs : s ≠ 0) (u : ℂ) :
    xiGamma (s+u)/xiGamma s /
        Complex.exp (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s)) =
      ((s+u)*(s+u-1)/(s*(s-1))) *
        (Complex.Gamma ((s+u)/2)/Complex.Gamma (s/2) /
          Complex.exp ((u/2)*Complex.log (s/2)+(u/2)^2/(2*(s/2)))) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : Complex.log (Real.pi : ℂ)*(-(s+u)/2) -
      Complex.log (Real.pi : ℂ)*(-s/2) -
      (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s)) =
      -((u/2)*Complex.log (s/2)+(u/2)^2/(2*(s/2))) := by
    rw [log_scaled_half hs, ← Complex.ofReal_log Real.pi_pos.le]
    ring
  unfold xiGamma
  simp only [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hp]
  have he' := congrArg Complex.exp he
  simp only [Complex.exp_sub, Complex.exp_neg] at he'
  calc
    _ = ((s+u)*(s+u-1)/(s*(s-1))) *
        (Complex.Gamma ((s+u)/2)/Complex.Gamma (s/2)) *
        (Complex.exp (Complex.log (Real.pi : ℂ)*(-(s+u)/2)) /
          Complex.exp (Complex.log (Real.pi : ℂ)*(-s/2)) /
          Complex.exp (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s))) := by
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    _ = _ := by rw [he']; ring

private theorem polynomial_relative_bound {s u : ℂ} (hy : 0 < s.im) :
    ‖(s+u)*(s+u-1)/(s*(s-1))-1‖ ≤ 2*‖u‖/s.im+‖u‖^2/s.im^2 := by
  have hs : s ≠ 0 := by intro h; simp [h] at hy
  have hs1 : s-1 ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; linarith
  have he : (s+u)*(s+u-1)/(s*(s-1))-1 = u/s+u/(s-1)+(u/s)*(u/(s-1)) := by
    field_simp
    ring
  have hn : s.im ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_im_le_norm s)
  have hn1 : s.im ≤ ‖s-1‖ := by
    simpa using (le_abs_self (s-1).im).trans (Complex.abs_im_le_norm (s-1))
  have hb : ‖u/s‖ ≤ ‖u‖/s.im := by rw [norm_div]; gcongr
  have hb1 : ‖u/(s-1)‖ ≤ ‖u‖/s.im := by rw [norm_div]; gcongr
  rw [he]
  calc
    _ ≤ ‖u/s‖+‖u/(s-1)‖+‖u/s‖*‖u/(s-1)‖ := by
      have := norm_add_le (u/s) (u/(s-1))
      have := norm_add_le (u/s+u/(s-1)) ((u/s)*(u/(s-1)))
      rw [norm_mul] at this
      linarith
    _ ≤ ‖u‖/s.im+‖u‖/s.im+(‖u‖/s.im)*(‖u‖/s.im) := by gcongr
    _ = _ := by ring

/-- The actual xi-Gamma factor has a uniform quadratic relative estimate on a
sector covering every fixed vertical strip at sufficiently large height. -/
theorem xiGamma_relative_error_bound {s u : ℂ} (hr : 0 ≤ s.re+s.im/2)
    (hy : 4 ≤ s.im) (hu : ‖u‖ ≤ s.im/2) :
    ‖xiGamma (s+u)/xiGamma s /
        Complex.exp (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s)) - 1‖ ≤
      (1+‖u‖/s.im)^2 * Real.exp (GammaRatio.ratioError (s.im/2) (‖u‖/2)) - 1 := by
  have hyp : 0 < s.im := by linarith
  have hs : s ≠ 0 := by intro h; simp [h] at hyp
  have hg := GammaRatio.relative_error_bound (s := s/2) (u := u/2)
    (by simp only [div_ofNat_re, div_ofNat_im]; linarith)
    (by simp only [div_ofNat_im]; linarith)
    (by simp only [norm_div, Complex.norm_ofNat, div_ofNat_im]; linarith)
  let P := (s+u)*(s+u-1)/(s*(s-1))
  let G := Complex.Gamma ((s+u)/2)/Complex.Gamma (s/2) /
    Complex.exp ((u/2)*Complex.log (s/2)+(u/2)^2/(2*(s/2)))
  let q := ‖u‖/s.im
  let E := Real.exp (GammaRatio.ratioError (s.im/2) (‖u‖/2))
  have hg' : ‖G-1‖ ≤ E-1 := by
    simpa only [G, E, add_div, norm_div, Complex.norm_ofNat, div_ofNat_im] using hg
  have hp : ‖P-1‖ ≤ 2*q+q^2 := by
    convert polynomial_relative_bound (u := u) hyp using 1
    dsimp [P, q]
    ring
  have hp' : ‖P‖ ≤ (1+q)^2 := by
    have ht := norm_add_le (P-1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at ht
    nlinarith
  have he : 0 ≤ E-1 := (norm_nonneg _).trans hg'
  rw [xiGamma_relative_factorization hs]
  change ‖P*G-1‖ ≤ (1+q)^2*E-1
  have hx : P*G-1 = P*(G-1)+(P-1) := by ring
  rw [hx]
  have ht := norm_add_le (P*(G-1)) (P-1)
  rw [norm_mul] at ht
  have hm := mul_le_mul hp' hg' (norm_nonneg _) (sq_nonneg (1+q))
  nlinarith

/-- Uniform bounded-displacement convergence on the entire sector, hence on
every fixed vertical strip. The height threshold is independent of `Re(s)`
and of the displacement in the specified ball. -/
theorem xiGamma_relative_error_eventually (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ s u : ℂ, Y ≤ s.im → 0 ≤ s.re+s.im/2 → ‖u‖ ≤ R →
      ‖xiGamma (s+u)/xiGamma s /
        Complex.exp (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s))-1‖ < ε := by
  let B := fun y : ℝ => (1+R/y)^2 *
    Real.exp (8*R/y+4*R^2/y^2+4*R^3/y^2)-1
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun y : ℝ => 8*R/y+4*R^2/y^2+4*R^3/y^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (((hi.const_mul (8*R)).add ((hi.pow 2).const_mul (4*R^2))).add
        ((hi.pow 2).const_mul (4*R^3)))
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa [B, div_eq_mul_inv] using
      ((((hi.const_mul R).const_add 1).pow 2).mul
        ((Real.continuous_exp.tendsto 0).comp hd)).sub_const 1
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp (hB.eventually (gt_mem_nhds hε))
  refine ⟨max Y (max 4 (2*R)), by positivity, ?_⟩
  intro s u hy hr hu
  have hy4 : 4 ≤ s.im := (le_max_left 4 (2*R)).trans ((le_max_right Y _).trans hy)
  have hyr : 2*R ≤ s.im := (le_max_right 4 (2*R)).trans ((le_max_right Y _).trans hy)
  have hyp : 0 < s.im := by linarith
  apply lt_of_le_of_lt (xiGamma_relative_error_bound hr hy4 (by linarith))
  apply lt_of_le_of_lt _ (hY s.im ((le_max_left Y _).trans hy))
  have he : GammaRatio.ratioError (s.im/2) (‖u‖/2) =
      8*‖u‖/s.im+4*‖u‖^2/s.im^2+4*‖u‖^3/s.im^2 := by
    unfold GammaRatio.ratioError
    ring
  rw [he]
  dsimp [B]
  gcongr

/-- The proved Gamma estimate applies to the actual normalized contour
integrand after its exact Gaussian cancellation. This is a pointwise estimate,
not yet an integrated tail bound. -/
theorem saddleIntegrand_quadratic_relative_error_bound {a : ℝ} (ha : 0 < a)
    {s u : ℂ} (hr : 0 ≤ s.re+s.im/2) (hy : 4 ≤ s.im) (hu : ‖u‖ ≤ s.im/2)
    (L : ℝ) :
    ‖saddleIntegrand (4*a) (dobnerMap a s) L (s+u) / dobnerGamma a s /
        Complex.exp (-s*(L : ℂ)+u^2/(4*(a : ℂ))-u*(L : ℂ)+u^2/(4*s))-1‖ ≤
      (1+‖u‖/s.im)^2 * Real.exp (GammaRatio.ratioError (s.im/2) (‖u‖/2)) - 1 := by
  rw [saddleIntegrand_normalized_factorization ha]
  have he :
      (xiGamma (s+u)/xiGamma s * Complex.exp (-Complex.log (s/(2*Real.pi))*u/2)) *
        Complex.exp (-s*(L : ℂ)+u^2/(4*(a : ℂ))-u*(L : ℂ)) /
        Complex.exp (-s*(L : ℂ)+u^2/(4*(a : ℂ))-u*(L : ℂ)+u^2/(4*s)) =
      xiGamma (s+u)/xiGamma s /
        Complex.exp (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s)) := by
    rw [show -Complex.log (s/(2*Real.pi))*u/2 = -(Complex.log (s/(2*Real.pi))*u/2) by ring]
    simp only [Complex.exp_add, Complex.exp_neg]
    field_simp
  simp only [neg_mul] at he ⊢
  rw [he]
  exact xiGamma_relative_error_bound hr hy hu

end LeanCert.Analysis.DBN
