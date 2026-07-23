import LeanCert

-- e ≈ 2.718281828...

-- This should work (from earlier)
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.718282 := by
  certify_bound

-- Tighter bound
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.7182819 := by
  certify_bound

-- Even tighter
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.71828183 := by
  certify_bound

-- Very tight (e ≈ 2.718281828...)
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.718281829 := by
  certify_bound

-- Regression: closed point inequalities should be certified before `norm_num`
-- rewrites decimal square roots into quotient forms such as `√3 / √2`.
example : (2.5 : ℝ) ≤ 9.2211 * Real.exp (-0.8476 * Real.sqrt 1.5) := by
  interval_decide
