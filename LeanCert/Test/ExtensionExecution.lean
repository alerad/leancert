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
open Lean Meta Elab Tactic
open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Extension

/-- Exercise discovery followed by fixed replay against a fresh goal.  The
second pass consumes the retained rule outputs and never calls a candidate. -/
elab "registered_enclosure_replay" : tactic => unsafe do
  let originalGoal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some spec ← parseBound? target
    | throwError "registered_enclosure_replay expected a bound"
  let prepared ← match ← prepareGoal (.bound spec) with
    | .ok prepared => pure prepared
    | .error failure => throwError failure.detail
  let discoveryGoal ← mkFreshExprMVar target MetavarKind.syntheticOpaque
  setGoals [discoveryGoal.mvarId!]
  let certificate ←
    match ← registeredEnclosureBoundSubdivCoreTyped prepared (-53) 10 4 with
    | .ok outcome =>
        unless (← getGoals).isEmpty do
          throwError "registered enclosure discovery left goals"
        pure outcome.certificate
    | .error _ => throwError "registered enclosure discovery failed"
  setGoals [originalGoal]
  match ← replayRegisteredEnclosureBoundCoreTyped prepared certificate with
  | .ok _ => pure ()
  | .error _ => throwError "registered enclosure fixed replay failed"

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

/- A registered checker that rejects the initial width succeeds on the two
bisected leaves. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, narrowIdentity x ≤ 2 := by
  leancert?

set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, narrowIdentity x ≤ 2 := by
  registered_enclosure_replay

/- Subdivision also retries when the registered certificates are valid but
their composed enclosure is too coarse for the requested comparison. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, shifted x - x ≤ 2 := by
  leancert (subdivisions := 1)

/- Rational endpoints and bounds may materialize through `Rat.divInt`; their
proof transport must normalize without leaking side goals. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (1 / 20 : ℝ) 1, positiveBranch x ≤ 1 := by
  leancert

/- The widened registered atom loses correlation with `x`; subdivision makes
the composed comparison precise enough. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (1 / 20 : ℝ) 1, fatPositive x - x ≤ (1 / 2 : ℝ) := by
  leancert (subdivisions := 4)

/- Multiple registered atoms remain compositional under distinct core
transcendental operations. -/
set_option leancert.trust "kernel" in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp (positiveBranch (x / 2 + 1 / 10)) +
      Real.sin (positiveBranch (x + 1 / 10)) - x ≤ 4 := by
  leancert

/-- error: LeanCert recognized: univariate interval bound

Attempts:
  1. registered compositional enclosure
     Registered enclosure subdivision reached its configured depth 0 after examining 1 boxes (deepest depth 0; 0 certified leaves). Last failure: The registered candidate was rejected by its checker.

Budget: spent 1 of 1

Next steps:
• Check whether the requested statement is true.
• Increase `(taylorDepth := ...)`, `(subdivisions := ...)`, or `(maxIterations := ...)` when the corresponding attempt was inconclusive.
• Use `interval_refute` to search for a certified counterexample. -/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, narrowIdentity x ≤ 2 := by
  leancert? (budget := 1) (subdivisions := 0)

/- Exhausted speculative subdivision restores the caller's complete tactic
state before another proof is attempted. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, narrowIdentity x ≤ 2 := by
  first
  | leancert (budget := 1) (subdivisions := 0)
  | intro x hx
    simpa [narrowIdentity] using hx.2

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

/- The outer evaluator must honor the widened certified enclosure rather than
the definition of the opaque registered atom. -/
/-- error: LeanCert recognized: univariate interval bound

Domain obstruction:
  the checked interval evaluator rejected a partial operation

Narrow the domain or prove the required positivity/nonzero condition. Increasing numerical precision does not repair an invalid domain. -/
#guard_msgs in
example : ∀ x ∈ Set.Icc (1 / 20 : ℝ) 1, Real.log (fatPositive x) ≤ 2 := by
  leancert

end LeanCert.Test.ExtensionExecution
