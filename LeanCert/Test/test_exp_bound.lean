import LeanCert

example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.718282 := by
  certify_bound
