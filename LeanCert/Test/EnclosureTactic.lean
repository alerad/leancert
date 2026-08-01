/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Test.DownstreamPatterns.Extension
import LeanCert.Tactic.Enclosure

/-! # Focused registered-enclosure tactic regressions -/

namespace LeanCert.Test.EnclosureTactic

open LeanCert.Test.DownstreamPatterns.Extension

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, positiveBranch (x + 1) ≤ 2 := by
  enclosure_bound (trust := kernel)

/- Core operations may surround multiple independently checked atoms. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    positiveBranch (x + 1) + shifted x ≤ 4 := by
  enclosure_bound (trust := kernel)

/- The shared parser retains implication-style interval domains. -/
example : ∀ x : ℝ, (0 ≤ x ∧ x ≤ 1) → positiveBranch (x + 1) ≤ 2 := by
  enclosure_bound (trust := kernel)

/- A broad candidate is retried on checked subintervals. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, narrowIdentity x ≤ 2 := by
  enclosure_bound (subdivisions := 1) (trust := kernel)

/- Correlation loss in a widened proof-carrying atom is repaired by subdivision. -/
example : ∀ x ∈ Set.Icc (1 / 20 : ℝ) 1, fatPositive x - x ≤ (1 / 2 : ℝ) := by
  enclosure_bound (subdivisions := 4) (trust := kernel)

/- The reporting variant is itself an executable proof. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, shifted x ≤ 2 := by
  enclosure_bound? (trust := native)

/- Failure is transactional: the fallback sees the original untouched goal. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, narrowIdentity x ≤ 2 := by
  first
  | enclosure_bound (subdivisions := 0) (trust := kernel)
  | intro x hx
    simpa [narrowIdentity] using hx.2

end LeanCert.Test.EnclosureTactic
