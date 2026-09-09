import LeanCert.Analysis.DBN.PolynomialApproximation
import LeanCert.Analysis.DBN.PolynomialHeatTransfer
import LeanCert.Analysis.DBN.HeatShift

/-! Transfer finite polynomial strip contraction to the actual entire H₀. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Filter Polynomial
open scoped Topology

theorem shiftIter_H_re_pos (t a : ℝ) (n : ℕ) :
    0 < (shiftIter a n (H t) 0).re := by
  have hi := (shiftHeatIntegrand_integrable t a n 0).re
  have he (u : ℝ) : (shiftHeatIntegrand t a n 0 u).re = Real.cosh (a*u)^n * (Real.exp (t*u^2) * Phi u) := by
    simp only [shiftHeatIntegrand, heatIntegrand, zero_mul,
      Complex.cos_zero, mul_one, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  change IntegrableOn (fun u => (shiftHeatIntegrand t a n 0 u).re) (Ioi 0) at hi
  simp only [he] at hi
  have hp {u : ℝ} (hu : 0 < u) : 0 < Real.cosh (a*u)^n * (Real.exp (t*u^2) * Phi u) :=
    mul_pos (pow_pos (Real.cosh_pos _) _) (mul_pos (Real.exp_pos _) (Phi_pos hu.le))
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u => Real.cosh (a*u)^n * (Real.exp (t*u^2) * Phi u)) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun u hu => (hp hu).le))
  have hs : Function.support (fun u => Real.cosh (a*u)^n * (Real.exp (t*u^2) * Phi u)) ∩ Ioi 0 = Ioi 0 := by
    ext u
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt (hp h), h⟩⟩
  have hpos := (setIntegral_pos_iff_support_of_nonneg_ae hn hi).mpr (by rw [hs]; simp)
  have hr := integral_re (shiftHeatIntegrand_integrable t a n 0)
  change (∫ u in Ioi (0 : ℝ), (shiftHeatIntegrand t a n 0 u).re) =
    (∫ u in Ioi (0 : ℝ), shiftHeatIntegrand t a n 0 u).re at hr
  rw [shiftIter_H_eq_integral, ← hr]
  simpa only [he] using hpos

theorem shiftIter_H_ne_zero (t a : ℝ) (n : ℕ) : shiftIter a n (H t) 0 ≠ 0 := by
  intro h
  have := shiftIter_H_re_pos t a n
  simp [h] at this

theorem shiftIter_H_zero_re_pos (a : ℝ) (n : ℕ) :
    0 < (shiftIter a n (H 0) 0).re := shiftIter_H_re_pos 0 a n

theorem shiftIter_H_zero_ne_zero (a : ℝ) (n : ℕ) : shiftIter a n (H 0) 0 ≠ 0 :=
  shiftIter_H_ne_zero 0 a n

/-- The established time-zero cutoffs inhabit the reusable approximation API. -/
noncomputable def H_zero_stripApproximation : StripPolynomialApproximation (H 0) 1 where
  polynomial := HZeroPolynomial
  nonzero := HZeroPolynomial_ne_zero
  conj := HZeroPolynomial_conj
  strip := by simpa using HZeroPolynomial_strip
  convergence := HZeroPolynomial_convergence

/-- Finite shifts with total squared budget one have only real zeros, now for H₀ itself. -/
theorem shiftIter_H_unit_real (n : ℕ) (hn : 0 < n) {z : ℂ}
    (hz : shiftIter (Real.sqrt (1/(n : ℝ))) n (H 0) z = 0) : z.im = 0 := by
  by_contra him
  let a := Real.sqrt (1/(n : ℝ))
  have h := entire_limit_ne_zero
    (F := fun m => (shiftPolynomialIter a n (HZeroPolynomial m)).eval)
    (f := shiftIter a n (H 0))
    (fun m => (shiftPolynomialIter a n (HZeroPolynomial m)).differentiable)
    (shiftIter_entire a n (H_entire 0)) ⟨0, shiftIter_H_zero_ne_zero a n⟩
    (by simpa only [eval_shiftPolynomialIter] using
      shiftIter_convergence HZeroPolynomial_convergence a n)
    (U := {w : ℂ | w.im ≠ 0}) (isOpen_ne.preimage Complex.continuous_im)
    (by
      intro m w hw hzero
      exact hw (shiftPolynomialIter_unit_real _ (HZeroPolynomial_ne_zero m)
        (HZeroPolynomial_conj m) (HZeroPolynomial_strip m) n hn hzero)) him
  exact h hz

end LeanCert.Analysis.DBN
