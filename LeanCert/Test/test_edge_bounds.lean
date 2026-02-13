import LeanCert.Tactic.IntervalAuto

open LeanCert.Core

def Icc01 : Set ℝ := Set.Icc (0:ℝ) 1

theorem edge_bound_def_seticc : ∀ x ∈ Icc01, x * x ≤ (1 : ℚ) := by
  interval_bound

theorem edge_bound_neg_interval : ∀ x ∈ Set.Icc (-2:ℝ) 2, x * x ≤ (4 : ℚ) := by
  interval_bound

theorem edge_bound_abs_interval : ∀ x ∈ Set.Icc (-1:ℝ) 1, abs x ≤ (1 : ℚ) := by
  interval_bound

theorem edge_bound_sqrt_upper : ∀ x ∈ Set.Icc (0:ℝ) 4, Real.sqrt x ≤ (2 : ℚ) := by
  interval_bound

theorem edge_bound_rpow_half : ∀ x ∈ Set.Icc (0:ℝ) 4, x ^ ((1:ℝ) / 2) ≤ (2 : ℚ) := by
  interval_bound

theorem edge_bound_rpow_inv_two : ∀ x ∈ Set.Icc (0:ℝ) 4, x ^ ((2:ℝ)⁻¹) ≤ (2 : ℚ) := by
  interval_bound

theorem edge_bound_rpow_three_halves :
    ∀ x ∈ Set.Icc (0:ℝ) 1, x ^ ((3:ℝ) / 2) ≤ (1 : ℚ) := by
  interval_bound

theorem edge_bound_rpow_one_point_five :
    ∀ x ∈ Set.Icc (0:ℝ) 1, x ^ (1.5:ℝ) ≤ (1 : ℚ) := by
  interval_bound

theorem edge_bound_sinh_upper : ∀ x ∈ Set.Icc (0:ℝ) 2, Real.sinh x ≤ (4 : ℚ) := by
  interval_bound 15

theorem edge_bound_cosh_lower : ∀ x ∈ Set.Icc (-1:ℝ) 1, (1 : ℚ) ≤ Real.cosh x := by
  interval_bound

theorem edge_bound_tanh_upper : ∀ x ∈ Set.Icc (-2:ℝ) 2, Real.tanh x ≤ (1 : ℚ) := by
  interval_bound

theorem edge_bound_tanh_lower : ∀ x ∈ Set.Icc (-2:ℝ) 2, (-1 : ℚ) ≤ Real.tanh x := by
  interval_bound

theorem edge_bound_pi_shift : ∀ x ∈ Icc01, x + Real.pi ≤ (5 : ℚ) := by
  interval_bound

theorem edge_bound_strict : ∀ x ∈ Icc01, x * x < (2 : ℚ) := by
  interval_bound
