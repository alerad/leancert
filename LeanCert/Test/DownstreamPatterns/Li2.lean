/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.CertifiedBounds.Li2

/-!
# PrimeNumberTheoremAnd lightweight li(2) pattern

Adapted from `IEANTN/Li2Bounds.lean`. This tests the lightweight interface and
its definitional bridge without importing or rebuilding `Li2Verified`.
-/

open Real MeasureTheory
open scoped Interval

namespace LeanCert.Test.DownstreamPatterns.Li2

noncomputable def downstreamLi2 : ℝ :=
  ∫ t in (0 : ℝ)..1, LeanCert.CertifiedBounds.Li2.integrand t

private theorem downstreamLi2_eq :
    downstreamLi2 = LeanCert.CertifiedBounds.Li2.value := rfl

/-- The lightweight lower and upper certificates transport across the local definition. -/
example : (1039 : ℚ) / 1000 ≤ downstreamLi2 ∧ downstreamLi2 ≤ (106 : ℚ) / 100 := by
  rw [downstreamLi2_eq]
  exact LeanCert.CertifiedBounds.Li2.bounds

/-- The integrand facts used by PNT+ are also available without an engine import. -/
example (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < LeanCert.CertifiedBounds.Li2.integrand t ∧
      LeanCert.CertifiedBounds.Li2.integrand t ≤ 2 :=
  ⟨LeanCert.CertifiedBounds.Li2.integrand_pos t ht0 ht1,
    LeanCert.CertifiedBounds.Li2.integrand_le_two t ht0 ht1⟩

end LeanCert.Test.DownstreamPatterns.Li2
