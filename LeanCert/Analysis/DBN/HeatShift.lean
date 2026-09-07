import LeanCert.Analysis.DBN.HeatSymmetry
import LeanCert.Analysis.DBN.StripIteration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Exact finite imaginary shifts of the actual heat integral. The limiting
Gaussian multiplier and zero-preserving approximation are not assumed here. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Polynomial

noncomputable def shiftIter (a : ℝ) : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f => f
  | n+1, f => shiftAverage (shiftIter a n f) a

theorem eval_shiftPolynomialIter (a : ℝ) (n : ℕ) (p : ℂ[X]) (z : ℂ) :
    (shiftPolynomialIter a n p).eval z = shiftIter a n p.eval z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [shiftPolynomialIter, eval_shiftPolynomial, shiftIter, shiftAverage, ih]

noncomputable def shiftHeatIntegrand (t a : ℝ) (n : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  (Real.cosh (a*u) : ℂ)^n * heatIntegrand t z u

private theorem cos_shift_pair (a u : ℝ) (z : ℂ) :
    (Complex.cos ((z+(a : ℂ)*I)*(u : ℂ)) + Complex.cos ((z-(a : ℂ)*I)*(u : ℂ)))/2 =
      (Real.cosh (a*u) : ℂ) * Complex.cos (z*(u : ℂ)) := by
  rw [add_mul, sub_mul, Complex.cos_add, Complex.cos_sub]
  have hc : Complex.cos ((a : ℂ)*I*(u : ℂ)) = (Real.cosh (a*u) : ℂ) := by
    rw [show (a : ℂ)*I*(u : ℂ) = ((a*u : ℝ) : ℂ)*I by push_cast; ring,
      Complex.cos_mul_I]
    norm_cast
  rw [hc]
  ring

theorem shiftHeatIntegrand_succ (t a : ℝ) (n : ℕ) (z : ℂ) (u : ℝ) :
    shiftHeatIntegrand t a (n+1) z u =
      (shiftHeatIntegrand t a n (z+(a : ℂ)*I) u +
       shiftHeatIntegrand t a n (z-(a : ℂ)*I) u)/2 := by
  have h := cos_shift_pair a u z
  simp only [shiftHeatIntegrand, heatIntegrand]
  rw [pow_succ]
  linear_combination -((Real.cosh (a*u) : ℂ)^n * ((Real.exp (t*u^2)*Phi u : ℝ) : ℂ)) * h

theorem shiftHeatIntegrand_integrable (t a : ℝ) (n : ℕ) (z : ℂ) :
    IntegrableOn (shiftHeatIntegrand t a n z) (Ioi 0) := by
  change IntegrableOn (fun u => shiftHeatIntegrand t a n z u) (Ioi 0)
  induction n generalizing z with
  | zero => simpa only [shiftHeatIntegrand, pow_zero, one_mul] using heatIntegrand_integrable t z
  | succ n ih =>
    simp only [IntegrableOn, shiftHeatIntegrand_succ]
    exact ((ih (z+(a : ℂ)*I)).add (ih (z-(a : ℂ)*I))).div_const 2

/-- Finite shifts multiply the actual Fourier kernel by a power of `cosh`. -/
theorem shiftIter_H_eq_integral (t a : ℝ) (n : ℕ) (z : ℂ) :
    shiftIter a n (H t) z = ∫ u in Ioi (0 : ℝ), shiftHeatIntegrand t a n z u := by
  induction n generalizing z with
  | zero => simp [shiftIter, shiftHeatIntegrand, H]
  | succ n ih =>
    simp only [shiftIter, shiftAverage, ih, shiftHeatIntegrand_succ]
    rw [integral_div, integral_add (shiftHeatIntegrand_integrable t a n _)
      (shiftHeatIntegrand_integrable t a n _)]

/-- The finite multipliers have exactly the Gaussian domination needed for the heat limit. -/
theorem cosh_pow_le_heat_multiplier (a u : ℝ) (n : ℕ) :
    Real.cosh (a*u)^n ≤ Real.exp (((n : ℝ)*a^2/2)*u^2) := by
  have h := pow_le_pow_left₀ (Real.cosh_pos (a*u)).le (Real.cosh_le_exp_half_sq (a*u)) n
  rw [← Real.exp_nat_mul] at h
  calc
    Real.cosh (a*u)^n ≤ Real.exp ((n : ℝ)*((a*u)^2/2)) := h
    _ = Real.exp (((n : ℝ)*a^2/2)*u^2) := by congr 1; ring

/-- Domination by the corresponding Gaussian heat weight, before taking any limit. -/
theorem shiftHeatIntegrand_norm_le (t a : ℝ) (n : ℕ) (z : ℂ) (u : ℝ) :
    ‖shiftHeatIntegrand t a n z u‖ ≤ ‖heatIntegrand (t+(n : ℝ)*a^2/2) z u‖ := by
  have h := cosh_pow_le_heat_multiplier a u n
  have hcosh : 0 ≤ Real.cosh (a*u) := (Real.cosh_pos _).le
  have he : Real.exp ((t+(n : ℝ)*a^2/2)*u^2) =
      Real.exp (((n : ℝ)*a^2/2)*u^2) * Real.exp (t*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [shiftHeatIntegrand, heatIntegrand, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hcosh, abs_of_pos (Real.exp_pos _), he]
  nlinarith [mul_le_mul_of_nonneg_right h
    (show 0 ≤ Real.exp (t*u^2) * |Phi u| * ‖Complex.cos (z*(u : ℂ))‖ by positivity)]

/-- Gaussian domination on bounded imaginary parts, uniform in all finite shifts
whose squared budget is exactly one. -/
theorem shiftHeatIntegrand_bound_unit (a : ℝ) (n : ℕ) (hbudget : (n : ℝ)*a^2 = 1)
    (Y : ℝ) {z : ℂ} (hz : |z.im| ≤ Y) {u : ℝ} (hu : 0 ≤ u) :
    ‖shiftHeatIntegrand 0 a n z u‖ ≤
      (44 * Real.exp ((1/2 : ℝ)^2+(Y+1)^2+1)) * Real.exp (-u^2) := by
  have h := shiftHeatIntegrand_norm_le 0 a n z u
  rw [hbudget, zero_add] at h
  exact h.trans (heatIntegrand_bound_box (1/2) Y (by norm_num) hz hu)

end LeanCert.Analysis.DBN
