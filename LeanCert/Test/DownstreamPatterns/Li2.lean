/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.Li2Bounds

/-!
# PrimeNumberTheoremAnd lightweight li(2) pattern

Adapted from `IEANTN/Li2Bounds.lean`. This tests the lightweight interface and
its definitional bridge without importing or rebuilding `Li2Verified`.
-/

open Real MeasureTheory
open scoped Interval
open LeanCert.Engine.TaylorModel

namespace LeanCert.Test.DownstreamPatterns.Li2

noncomputable def downstreamLi2 : ℝ :=
  ∫ t in (0 : ℝ)..1, symmetricLogCombination t

private theorem downstreamLi2_eq : downstreamLi2 = _root_.Li2.li2 := rfl

/-- The lightweight lower and upper certificates transport across the local definition. -/
example : (1039 : ℚ) / 1000 ≤ downstreamLi2 ∧ downstreamLi2 ≤ (106 : ℚ) / 100 := by
  rw [downstreamLi2_eq]
  exact _root_.Li2.li2_bounds

end LeanCert.Test.DownstreamPatterns.Li2
