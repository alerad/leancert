import LeanCert.Tactic.Refute
import LeanCert.Tactic.IntervalAuto

open LeanCert.Core

/-- IntervalRat domain to exercise interval_refute on non-Set.Icc intervals. -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

theorem edge_refute_intervalrat : ∀ x ∈ I01, x * x ≤ (1 : ℚ) := by
  interval_refute
  certify_bound

theorem edge_refute_strict_intervalrat : ∀ x ∈ I01, x * x < (2 : ℚ) := by
  interval_refute
  certify_bound
