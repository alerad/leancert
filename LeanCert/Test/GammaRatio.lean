import LeanCert.Analysis.DBN.DobnerGammaRatio
import Mathlib.Util.AssertNoSorry

open Complex LeanCert.Analysis LeanCert.Analysis.DBN

-- The region includes negative real parts; no positivity of Re(s+u) is needed.
example {s u : ℂ} (hr : -s.im/2 ≤ s.re) (hy : 2 ≤ s.im) (hu : ‖u‖ ≤ s.im/2) :
    ‖Gamma (s+u)/Gamma s / Complex.exp (u*Complex.log s+u^2/(2*s))-1‖ ≤
      Real.exp (GammaRatio.ratioError s.im ‖u‖)-1 :=
  GammaRatio.relative_error_bound (by linarith) hy hu

-- Growing displacements, with an explicit error that vanishes as h → infinity.
example {s u : ℂ} {h : ℝ} (hh : 2 ≤ h) (hr : 0 ≤ s.re+s.im/2)
    (hy : h^5 ≤ s.im) (hu : ‖u‖ ≤ h^3) :
    ‖Gamma (s+u)/Gamma s / Complex.exp (u*Complex.log s+u^2/(2*s))-1‖ ≤
      Real.exp (20/h)-1 := GammaRatio.relative_error_bound_growing hh hr hy hu

-- Every fixed vertical strip is contained in the proved sector eventually.
example (M R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s u : ℂ, Y ≤ s.im → |s.re| ≤ M → ‖u‖ ≤ R →
      ‖xiGamma (s+u)/xiGamma s /
        Complex.exp (Complex.log (s/(2*Real.pi))*u/2+u^2/(4*s))-1‖ < ε := by
  obtain ⟨Y, _, hY⟩ := xiGamma_relative_error_eventually R hR hε
  refine ⟨max Y (2*M), ?_⟩
  intro s u hy hx hu
  apply hY s u ((le_max_left _ _).trans hy) _ hu
  have := (le_max_right Y (2*M)).trans hy
  have := (abs_le.mp hx).1
  linarith

assert_no_sorry GammaRatio.sum_inv_norm_sq_le
assert_no_sorry GammaRatio.harmonic_error_bound
assert_no_sorry GammaRatio.inverse_square_error_bound
assert_no_sorry GammaRatio.exp_logEulerRatio_tendsto
assert_no_sorry GammaRatio.relative_error_bound
assert_no_sorry GammaRatio.relative_error_bound_growing
assert_no_sorry xiGamma_relative_factorization
assert_no_sorry xiGamma_relative_error_bound
assert_no_sorry xiGamma_relative_error_eventually
assert_no_sorry saddleIntegrand_quadratic_relative_error_bound
