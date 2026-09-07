import LeanCert.Analysis.DBN.HeatFlow

/-! Symmetries of the actual heat integral, without using kernel evenness. -/
namespace LeanCert.Analysis.DBN
open MeasureTheory

theorem H_even (t : ℝ) (z : ℂ) : H t (-z) = H t z := by
  simp [H, heatIntegrand]

theorem H_conj (t : ℝ) (z : ℂ) : H t (starRingEnd ℂ z) = starRingEnd ℂ (H t z) := by
  unfold H
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [heatIntegrand, map_mul, Complex.conj_ofReal, ← Complex.cos_conj]

theorem H_real (t x : ℝ) : (H t (x : ℂ)).im = 0 := by
  have h := congrArg Complex.im (H_conj t (x : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

/-- Positivity at the origin excludes the identically-zero heat transform at every time. -/
theorem H_zero_re_pos (t : ℝ) : 0 < (H t 0).re := by
  have hi := (heatIntegrand_integrable t 0).re
  have he (u : ℝ) : (heatIntegrand t 0 u).re = Real.exp (t*u^2)*Phi u := by
    simp only [heatIntegrand, zero_mul, Complex.cos_zero, mul_one, Complex.ofReal_re]
  change IntegrableOn (fun u => (heatIntegrand t 0 u).re) (Set.Ioi 0) at hi
  simp only [he] at hi
  have hp {u : ℝ} (hu : 0 < u) : 0 < Real.exp (t*u^2)*Phi u :=
    mul_pos (Real.exp_pos _) (Phi_pos hu.le)
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun u => Real.exp (t*u^2)*Phi u) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun u hu => (hp hu).le))
  have hs : Function.support (fun u => Real.exp (t*u^2)*Phi u) ∩ Set.Ioi 0 = Set.Ioi 0 := by
    ext u
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt (hp h), h⟩⟩
  have hpos := (setIntegral_pos_iff_support_of_nonneg_ae hn hi).mpr
    (by rw [hs]; simp)
  have hr := integral_re (heatIntegrand_integrable t 0)
  change (∫ u in Set.Ioi (0 : ℝ), (heatIntegrand t 0 u).re) = (H t 0).re at hr
  rw [← hr]
  simpa only [he] using hpos

theorem H_zero_ne_zero (t : ℝ) : H t 0 ≠ 0 := by
  intro h
  have := H_zero_re_pos t
  simp [h] at this

end LeanCert.Analysis.DBN
