import LeanCert.Analysis.DBN.PolynomialApproximation
import LeanCert.Analysis.DBN.ZeroLimit
import LeanCert.Analysis.DBN.HeatShift

/-! Transfer finite polynomial strip contraction to the actual entire H₀. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Filter Polynomial
open scoped Topology

theorem shiftIter_entire (a : ℝ) (n : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (shiftIter a n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    change Differentiable ℂ (fun z =>
      (shiftIter a n f (z+(a : ℂ)*I) + shiftIter a n f (z-(a : ℂ)*I))/2)
    fun_prop

theorem shiftIter_convergence {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f l) (a : ℝ) (n : ℕ) :
    TendstoLocallyUniformly (fun m => shiftIter a n (F m)) (shiftIter a n f) l := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have hp := ih.comp (fun z => z+(a : ℂ)*I) (by fun_prop)
    have hm := ih.comp (fun z => z-(a : ℂ)*I) (by fun_prop)
    have hu : UniformContinuous (fun w : ℂ => (1/2 : ℂ)*w) :=
      (ContinuousLinearMap.mul ℂ ℂ (1/2)).uniformContinuous
    change TendstoLocallyUniformly
      (fun m z => (shiftIter a n (F m) (z+(a : ℂ)*I) + shiftIter a n (F m) (z-(a : ℂ)*I))/2)
      (fun z => (shiftIter a n f (z+(a : ℂ)*I) + shiftIter a n f (z-(a : ℂ)*I))/2) l
    simpa only [Function.comp_def, Pi.add_apply,
      div_eq_mul_inv, mul_comm, one_mul] using hu.comp_tendstoLocallyUniformly (hp.add hm)

theorem shiftIter_H_zero_re_pos (a : ℝ) (n : ℕ) :
    0 < (shiftIter a n (H 0) 0).re := by
  have hi := (shiftHeatIntegrand_integrable 0 a n 0).re
  have he (u : ℝ) : (shiftHeatIntegrand 0 a n 0 u).re = Real.cosh (a*u)^n * Phi u := by
    simp only [shiftHeatIntegrand, heatIntegrand, zero_mul, Real.exp_zero, one_mul,
      Complex.cos_zero, mul_one, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  change IntegrableOn (fun u => (shiftHeatIntegrand 0 a n 0 u).re) (Ioi 0) at hi
  simp only [he] at hi
  have hp {u : ℝ} (hu : 0 < u) : 0 < Real.cosh (a*u)^n * Phi u :=
    mul_pos (pow_pos (Real.cosh_pos _) _) (Phi_pos hu.le)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u => Real.cosh (a*u)^n * Phi u) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun u hu => (hp hu).le))
  have hs : Function.support (fun u => Real.cosh (a*u)^n * Phi u) ∩ Ioi 0 = Ioi 0 := by
    ext u
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt (hp h), h⟩⟩
  have hpos := (setIntegral_pos_iff_support_of_nonneg_ae hn hi).mpr (by rw [hs]; simp)
  have hr := integral_re (shiftHeatIntegrand_integrable 0 a n 0)
  change (∫ u in Ioi (0 : ℝ), (shiftHeatIntegrand 0 a n 0 u).re) =
    (∫ u in Ioi (0 : ℝ), shiftHeatIntegrand 0 a n 0 u).re at hr
  rw [shiftIter_H_eq_integral, ← hr]
  simpa only [he] using hpos

theorem shiftIter_H_zero_ne_zero (a : ℝ) (n : ℕ) : shiftIter a n (H 0) 0 ≠ 0 := by
  intro h
  have := shiftIter_H_zero_re_pos a n
  simp [h] at this

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
