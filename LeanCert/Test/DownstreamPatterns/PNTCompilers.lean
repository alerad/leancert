/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.PNTCompilers
import LeanCert.ANT.Asymp.Pointwise
import LeanCert.ANT.Asymp.Inequality

/-!
# PrimeNumberTheoremAnd explicit-PNT compiler pattern

PNT+ imports these three ANT modules in `IEANTN/FKS2.lean`. This example
ensures the generic compiler theorem remains straightforward to instantiate.
-/

namespace LeanCert.Test.DownstreamPatterns.PNTCompilers

open LeanCert.ANT.PNTCompilers

/-- A concrete instantiation of the generic `ψ → θ` error transfer. -/
example (x : ℝ) : |(fun y : ℝ => y) x - x| ≤ 1 + 1 := by
  apply psi_to_theta_bound
    (psi := fun y : ℝ => y + 1)
    (theta := fun y : ℝ => y)
    (psiError := 1)
    (powerContribution := 1)
    (powerBound := 1)
  · ring
  · simp
  · norm_num
  · norm_num

end LeanCert.Test.DownstreamPatterns.PNTCompilers
