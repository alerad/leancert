import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Explicit absorption of polynomial factors into exponential decay. -/
namespace LeanCert.Analysis

/-- Retain half of the exponential decay while absorbing any natural power. -/
theorem pow_mul_exp_neg_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    x^m * Real.exp (-x) ≤ (2^m * (m.factorial : ℝ)) * Real.exp (-x/2) := by
  have h := Real.pow_div_factorial_le_exp (x/2) (show 0 ≤ x/2 by positivity) m
  have hf : (0 : ℝ) < m.factorial := by positivity
  have hp : x^m ≤ (2^m * (m.factorial : ℝ)) * Real.exp (x/2) := by
    have h' := (div_le_iff₀ hf).mp h
    have h'' := mul_le_mul_of_nonneg_left h' (show (0 : ℝ) ≤ 2^m by positivity)
    simpa [div_pow, mul_div_cancel₀ _ (ne_of_gt (show (0 : ℝ) < 2^m by positivity)),
      mul_assoc, mul_comm, mul_left_comm] using h''
  have he : Real.exp (x/2) * Real.exp (-x) = Real.exp (-x/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, he] using mul_le_mul_of_nonneg_right hp (Real.exp_pos (-x)).le

end LeanCert.Analysis
