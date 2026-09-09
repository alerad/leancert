import LeanCert.Analysis.DBN.DobnerContourShift
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis LeanCert.Analysis.DBN Complex MeasureTheory

-- The generic constructor also handles reversed endpoints and zero width.
example (F : ℂ → ℂ) (hF : Differentiable ℂ F) (T : ℝ) :
    ContourShift.RectangleShiftCert F 3 1 T :=
  ContourShift.RectangleShiftCert.ofHolomorphicStrip F 3 1 T (fun z _ => hF z)
example (F : ℂ → ℂ) (σ T : ℝ) (hF : Differentiable ℂ F) :
    ContourShift.RectangleShiftCert F σ σ T :=
  ContourShift.RectangleShiftCert.ofHolomorphicStrip F σ σ T (fun z _ => hF z)

-- This is an equality of actual absolutely convergent integrals, not chosen limits.
example {b : ℝ} (hb : 0 < b) (w : ℂ) (L : ℝ) :
    (∫ y : ℝ, saddleIntegrand b w L (3+(y : ℂ)*I)) =
      ∫ y : ℝ, saddleIntegrand b w L (1+(y : ℂ)*I) := by
  simpa using saddleIntegrand_contour_shift b hb w L 3 1 (by norm_num) (by norm_num)

example {b : ℝ} (hb : 0 < b) (w : ℂ) (L : ℝ) :
    Integrable (fun y : ℝ => saddleIntegrand b w L (1+(y : ℂ)*I)) := by
  simpa using saddleIntegrand_vertical_integrable b hb w L 1 (by norm_num)

-- No restriction on Re(s): the new full contour stays at positive real part.
example {a : ℝ} (ha : 0 < a) (s : ℂ) (k : ℕ) :
    normalizedContourTerm a s k =
      (∫ y : ℝ, saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1))
        (3+(y : ℂ)*I)) /
      ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ)*dobnerGamma a s) := by
  simpa using normalizedContourTerm_eq_shifted_integral ha s k 3 (by norm_num)

-- Exact identity, not an asymptotic claim about the Gamma ratio.
example {a : ℝ} (ha : 0 < a) (s u : ℂ) (L : ℝ) :
    saddleIntegrand (4*a) (dobnerMap a s) L (s+u) / dobnerGamma a s =
      (xiGamma (s+u)/xiGamma s * Complex.exp (-Complex.log (s/(2*Real.pi))*u/2)) *
      Complex.exp (-(s*(L : ℂ))+u^2/(4*(a : ℂ))-u*(L : ℂ)) :=
  saddleIntegrand_normalized_factorization ha s u L

assert_no_sorry ContourShift.integral_vertical_eq_of_holomorphic_of_vanish
assert_no_sorry saddleIntegrand_strip_bound
assert_no_sorry saddleIntegrand_vertical_integrable
assert_no_sorry saddleIntegrand_contour_shift
assert_no_sorry normalizedContourTerm_eq_shifted_integral
assert_no_sorry normalizedContourTerm_eq_saddle_line
assert_no_sorry saddleIntegrand_normalized_factorization
