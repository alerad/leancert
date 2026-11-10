module

public import LeanCert.Tactic.Discovery

public section

theorem edge_minimize_and : ∃ m : ℚ, ∀ x : ℝ, (0:ℝ) ≤ x ∧ x ≤ 1 → x * x ≥ m := by
  interval_minimize

theorem edge_maximize_and : ∃ M : ℚ, ∀ x : ℝ, (0:ℝ) ≤ x ∧ x ≤ 1 → x * x ≤ M := by
  interval_maximize

theorem edge_minimize_arrow : ∃ m : ℚ, ∀ x : ℝ, (0:ℝ) ≤ x → x ≤ 1 → x * x ≥ m := by
  interval_minimize

theorem edge_root_add_neg : ∃ x ∈ Set.Icc (0:ℝ) 2, x * x + -2 = 0 := by
  interval_roots

theorem edge_argmax_identity : ∃ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, y ≤ x := by
  interval_argmax
