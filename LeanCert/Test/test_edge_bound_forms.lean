import LeanCert.Tactic.IntervalAuto

theorem edge_bound_setof : ∀ x ∈ {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1}, x * x ≤ (1 : ℚ) := by
  certify_bound

theorem edge_bound_and : ∀ x : ℝ, (0:ℝ) ≤ x ∧ x ≤ 1 → x * x ≤ (1 : ℚ) := by
  certify_bound

theorem edge_bound_arrow : ∀ x : ℝ, (0:ℝ) ≤ x → x ≤ 1 → x * x ≤ (1 : ℚ) := by
  certify_bound

theorem edge_bound_decimal : ∀ x ∈ Set.Icc (-0.5:ℝ) (1/3), x * x ≤ (1 : ℚ) := by
  certify_bound

theorem edge_bound_scientific : ∀ x ∈ Set.Icc (0:ℝ) (2.5:ℝ), x ≤ (3 : ℚ) := by
  certify_bound
