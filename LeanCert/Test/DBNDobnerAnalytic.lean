import LeanCert.Analysis.DBN.DobnerDirichlet
import LeanCert.Analysis.DBN.DobnerGammaReciprocal
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex MeasureTheory

-- Actual normalization; no abstract F or multiplier G is supplied.
example (a : ℝ) {s : ℂ} (hs : 0 < s.im) : dobnerGamma a s ≠ 0 := dobnerGamma_ne_zero a hs
example (a : ℝ) {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ (normalizedHeat a) s := differentiableAt_normalizedHeat a hs
example {s : ℂ} (hs : 0 < s.im) : normalizedHeat 0 s = riemannZeta s := normalizedHeat_zero hs
example (a : ℝ) {s : ℂ} (hs : 0 < s.im) :
    xiHeat (-4*a) (dobnerMap a s) = dobnerGamma a s * normalizedHeat a s :=
  normalizedHeat_identity a hs

-- Integrability and value are tested separately, including a complex Gaussian center.
example (q z : ℂ) (c : ℝ) :
    Integrable (fun x : ℝ => gaussianShift q x * H 0 (z+(c*x : ℝ))) :=
  gaussianShift_average_H_zero_integrable q z c
example (q z : ℂ) (c : ℝ) :
    (∫ x : ℝ, gaussianShift q x * H 0 (z+(c*x : ℝ))) =
      (Real.sqrt Real.pi : ℂ)*H (-c^2/4) (z+(c : ℂ)*q) :=
  gaussianShift_average_H_zero q z c
example {b : ℝ} (hb : 0 < b) (s : ℂ) : Integrable (verticalGaussianIntegrand b 2 s) :=
  verticalGaussianIntegral_integrable b hb 2 s
example {b : ℝ} (hb : 0 < b) (s : ℂ) :
    (∫ x : ℝ, verticalGaussianIntegrand b 2 s x) =
      (Real.sqrt Real.pi : ℂ)*xiHeat (-b) s := verticalGaussianIntegral b hb 2 s

example (q : ℂ) (c : ℝ) : Summable (dobnerContourTerm q c) := dobnerContourTerm_summable q c
example (q : ℂ) (c : ℝ) :
    (∑' k, dobnerContourTerm q c k) =
      (Real.sqrt Real.pi : ℂ)*xiHeat (-c^2) (2+(c : ℂ)*q*I) :=
  dobnerContourTerm_tsum_eq_heat q c
example {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (∑' k, normalizedContourTerm a s k) = normalizedHeat a s := normalizedContourTerm_tsum ha s

-- The missing approximation remains an explicit premise.
example (h : ∀ a : ℝ, 0 < a → NormalizedHeatApproximation a) : 0 ≤ Lambda :=
  Lambda_nonneg_of_normalizedHeatApproximation h

assert_no_sorry normalizedContourTerm_tsum
assert_no_sorry verticalGaussianIntegral
assert_no_sorry gammaContourWeight_integrable
assert_no_sorry Lambda_nonneg_of_normalizedHeatApproximation

-- Unconditional reciprocal bounds: no approximation hypothesis is supplied.
example (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (Real.pi*|s.im|) :=
  norm_inv_Gamma_le_exp_on_strip M hM

example (a : ℝ) (ha : 0 < a) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 2 ≤ s.im →
      ‖(dobnerGamma a s)⁻¹‖ ≤ C * Real.exp (Real.pi*s.im/2) :=
  norm_inv_dobnerGamma_le_exp_on_strip a ha M hM

-- The recurrence estimate applies to both signs of the imaginary part.
example (s : ℂ) (n : ℕ) (hs : s.im ≤ -1) :
    ‖(Complex.Gamma (s+n))⁻¹‖ ≤ ‖(Complex.Gamma s)⁻¹‖ := by
  apply norm_inv_Gamma_add_nat_le
  rw [abs_of_nonpos (by linarith)]
  linarith

assert_no_sorry norm_inv_Gamma_le_reflection
assert_no_sorry norm_inv_Gamma_add_nat_le
assert_no_sorry norm_inv_Gamma_le_exp_on_strip
assert_no_sorry norm_inv_dobnerGamma_le_exp_on_strip
