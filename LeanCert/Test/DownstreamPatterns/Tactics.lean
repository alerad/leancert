/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# PrimeNumberTheoremAnd tactic patterns

Small numerical goals adapted from `IEANTN/LogTables.lean`,
`IEANTN/TMEEMT.lean`, and `IEANTN/Ramanujan/RamanujanCalculations.lean`.
These examples protect downstream tactic syntax and elaboration behavior.
-/

open Real Set

namespace LeanCert.Test.DownstreamPatterns.Tactics

/-- PNT+ uses `interval_decide` for nested transcendental point goals. -/
example : (0.633415 : ℝ) < log (log 6.58) := by
  interval_decide

/-- PNT+ also uses `interval_auto` directly for closed exponential goals. -/
example : exp (20 : ℝ) ≤ 485165196 := by
  interval_auto

/-- PNT+ currently expresses point bounds as singleton interval goals. -/
example : ∀ y ∈ Icc (8 : ℝ) 8, exp y < (3914 : ℝ) := by
  certify_bound 20

/-- A representative high-dynamic-range singleton interval from PNT+. -/
example : ∀ y ∈ Icc (3914 : ℝ) 3914,
    2 * y ^ 6 * exp (-y) ≤ (1 : ℝ) / 1000000 := by
  certify_bound 20

end LeanCert.Test.DownstreamPatterns.Tactics
