/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic
import LeanCert.Test.DownstreamPatterns.Extension

/-! # End-to-end execution of downstream enclosure rules -/

namespace LeanCert.Test.ExtensionExecution

open LeanCert.Test.DownstreamPatterns.Extension

/-- Merely importing rules must not consume budget for ordinary expressions. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ 1 := by
  leancert (budget := 1)

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, positiveBranch (x + 1) ≤ 2 := by
  leancert

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) ≤ positiveBranch (x + 1) := by
  leancert

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    positiveBranch (positiveBranch (x + 1)) ≤ 2 := by
  leancert

/- Ordinary supported operations may surround a registered application, and
the original quantified variable may occur independently outside it. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, positiveBranch (x + 1) + x ≤ 3 := by
  leancert

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    positiveBranch (x + 1) * positiveBranch (x + 1) ≤ 4 := by
  leancert

/- Distinct registered subterms become independent proof-carrying holes in
the surrounding core expression. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    positiveBranch (x + 1) + shifted x ≤ 4 := by
  leancert

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp (positiveBranch (x + 1)) < 8 := by
  leancert

/- Composition works recursively inside the argument of another registered
application. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    positiveBranch (Real.exp (positiveBranch (x + 1))) < 8 := by
  leancert

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp (positiveBranch (x + 1)) + x < 9 := by
  leancert?

/-- error: LeanCert recognized: univariate interval bound

Domain obstruction:
  input interval is not strictly positive

Narrow the domain or prove the required positivity/nonzero condition. Increasing numerical precision does not repair an invalid domain. -/
#guard_msgs in
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, positiveBranch x ≤ 1 := by
  leancert

/-- error: LeanCert recognized: univariate interval bound

Domain obstruction:
  the checked interval evaluator rejected a partial operation

Narrow the domain or prove the required positivity/nonzero condition. Increasing numerical precision does not repair an invalid domain. -/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.log (positiveBranch (x + 1) - 2) ≤ 0 := by
  leancert

end LeanCert.Test.ExtensionExecution
