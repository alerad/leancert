/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Numerically qualified relative completeness

Geometric subdivision alone does not imply convergence of computed interval
bounds. A complete refinement schedule must also drive outward-rounding and
analytic approximation errors to zero. This module records that requirement
and proves the resulting positive-margin completeness theorem.
-/

namespace LeanCert.Validity

open Filter

/-- Error components controlled by a coordinated refinement schedule.

* `spatial` is the error due to finite cell diameter;
* `rounding` is outward dyadic/rational rounding error;
* `analytic` is Taylor or other certified approximation remainder.

For expressions with partial domains, construction of these bounds also
requires the refined cells to remain inside the expression's valid domain. -/
structure NumericalRefinementSchedule where
  spatial : Nat → ℝ
  rounding : Nat → ℝ
  analytic : Nat → ℝ
  spatial_nonneg : ∀ n, 0 ≤ spatial n
  rounding_nonneg : ∀ n, 0 ≤ rounding n
  analytic_nonneg : ∀ n, 0 ≤ analytic n
  spatial_tendsto_zero : Tendsto spatial atTop (nhds 0)
  rounding_tendsto_zero : Tendsto rounding atTop (nhds 0)
  analytic_tendsto_zero : Tendsto analytic atTop (nhds 0)

namespace NumericalRefinementSchedule

/-- Total certified over-approximation error at one refinement stage. -/
def totalError (schedule : NumericalRefinementSchedule) (n : Nat) : ℝ :=
  schedule.spatial n + schedule.rounding n + schedule.analytic n

theorem totalError_nonneg (schedule : NumericalRefinementSchedule) (n : Nat) :
    0 ≤ schedule.totalError n := by
  exact add_nonneg (add_nonneg (schedule.spatial_nonneg n)
    (schedule.rounding_nonneg n)) (schedule.analytic_nonneg n)

/-- Coordinated spatial, rounding, and analytic refinement drives total error
to zero. -/
theorem totalError_tendsto_zero (schedule : NumericalRefinementSchedule) :
    Tendsto schedule.totalError atTop (nhds 0) := by
  change Tendsto
    (fun n => schedule.spatial n + schedule.rounding n + schedule.analytic n)
    atTop (nhds 0)
  simpa only [zero_add] using
    (schedule.spatial_tendsto_zero.add schedule.rounding_tendsto_zero).add
      schedule.analytic_tendsto_zero

/-- Every positive proof margin eventually dominates the total numerical error. -/
theorem eventually_totalError_lt (schedule : NumericalRefinementSchedule)
    {margin : ℝ} (hmargin : 0 < margin) :
    ∀ᶠ n in atTop, schedule.totalError n < margin := by
  exact (schedule.totalError_tendsto_zero.eventually (Iio_mem_nhds hmargin))

/-- Relative completeness for strict upper bounds.

If the mathematical bound has a positive margin below the target and the
computed upper enclosure exceeds the true bound by at most `totalError`, then
the checker eventually proves the target. -/
theorem eventually_certifies_upper (schedule : NumericalRefinementSchedule)
    (upper : Nat → ℝ) {trueBound target margin : ℝ}
    (hmargin : 0 < margin)
    (hstrict : trueBound ≤ target - margin)
    (hupper : ∀ n, upper n ≤ trueBound + schedule.totalError n) :
    ∀ᶠ n in atTop, upper n < target := by
  filter_upwards [schedule.eventually_totalError_lt hmargin] with n hn
  exact lt_of_le_of_lt (hupper n) (by linarith)

/-- Existential form used by finite search procedures: some refinement stage
certifies every strict target whose positive margin dominates the vanishing
error schedule. -/
theorem exists_certifying_upper (schedule : NumericalRefinementSchedule)
    (upper : Nat → ℝ) {trueBound target margin : ℝ}
    (hmargin : 0 < margin)
    (hstrict : trueBound ≤ target - margin)
    (hupper : ∀ n, upper n ≤ trueBound + schedule.totalError n) :
    ∃ n, upper n < target := by
  exact (schedule.eventually_certifies_upper upper hmargin hstrict hupper).exists

/-- Relative completeness for strict lower bounds, dual to
`eventually_certifies_upper`. -/
theorem eventually_certifies_lower (schedule : NumericalRefinementSchedule)
    (lower : Nat → ℝ) {trueBound target margin : ℝ}
    (hmargin : 0 < margin)
    (hstrict : target + margin ≤ trueBound)
    (hlower : ∀ n, trueBound - schedule.totalError n ≤ lower n) :
    ∀ᶠ n in atTop, target < lower n := by
  filter_upwards [schedule.eventually_totalError_lt hmargin] with n hn
  exact lt_of_lt_of_le (by linarith) (hlower n)

/-- Existential finite-stage form of strict lower-bound completeness. -/
theorem exists_certifying_lower (schedule : NumericalRefinementSchedule)
    (lower : Nat → ℝ) {trueBound target margin : ℝ}
    (hmargin : 0 < margin)
    (hstrict : target + margin ≤ trueBound)
    (hlower : ∀ n, trueBound - schedule.totalError n ≤ lower n) :
    ∃ n, target < lower n := by
  exact (schedule.eventually_certifies_lower lower hmargin hstrict hlower).exists

end NumericalRefinementSchedule

end LeanCert.Validity
