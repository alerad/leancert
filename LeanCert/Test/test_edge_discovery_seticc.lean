import LeanCert.Tactic.Discovery

abbrev Icc01 : Set ℝ := Set.Icc (0:ℝ) 1

theorem edge_minimize_seticc : ∃ m : ℚ, ∀ x ∈ Icc01, x * x ≥ m := by
  interval_minimize

theorem edge_maximize_seticc : ∃ M : ℚ, ∀ x ∈ Icc01, x * x ≤ M := by
  interval_maximize

theorem edge_root_seticc : ∃ x ∈ Set.Icc (0:ℝ) 2, x * x - 2 = 0 := by
  interval_roots

theorem edge_unique_root_seticc : ∃! x, x ∈ Set.Icc (1:ℝ) 2 ∧ x * x - 2 = 0 := by
  interval_unique_root

theorem edge_argmax_seticc : ∃ x ∈ Icc01, ∀ y ∈ Icc01, y * y ≤ x * x := by
  interval_argmax

-- Regression: norm_num closes trivial objectives outright; the tactic must
-- not invoke the interval engine on an already-closed goal.
theorem edge_argmax_const : ∃ x ∈ Icc01, ∀ y ∈ Icc01, (0:ℝ) ≤ (0:ℝ) := by
  interval_argmax
