/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert

/-!
# Transactional Solver Tests

Synthetic solvers exercise restoration independently of numerical engines.
-/

open Lean Meta Elab Tactic
open LeanCert.Tactic

set_option linter.unusedTactic false

private def testReport : SolverReport := {
  intent := .intervalBound
  method := "synthetic transaction test"
}

private def assertOriginalGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  unless after == before do
    throwError "transaction did not restore the original goal list"

elab "expect_partial_attempt" : tactic => do
  let before ← getGoals
  let result ← runAttempt testReport do
    evalTactic (← `(tactic| constructor))
    evalTactic (← `(tactic| exact True.intro))
  match result with
  | .error (.incompleteProof goals) =>
      unless goals.size = 1 do
        throwError "expected one remaining synthetic bridge goal, got {goals.size}"
  | other => throwError "expected incompleteProof, got {repr other}"
  assertOriginalGoals before

elab "expect_throwing_attempt" : tactic => do
  let before ← getGoals
  let result ← runAttempt testReport do
    evalTactic (← `(tactic| constructor))
    throwError "synthetic failure after mutation"
  match result with
  | .error (.internalFailure detail) =>
      unless detail.contains "synthetic failure" do
        throwError "missing original exception detail"
  | other => throwError "expected internalFailure, got {repr other}"
  assertOriginalGoals before

elab "expect_quiet_partial_attempt" : tactic => do
  let before ← getGoals
  let result ← runAttempt testReport do
    logWarning "this speculative warning must not leak"
    evalTactic (← `(tactic| constructor))
    evalTactic (← `(tactic| exact True.intro))
  match result with
  | .error (.incompleteProof _) => pure ()
  | other => throwError "expected incompleteProof, got {repr other}"
  assertOriginalGoals before

elab "close_transactionally" : tactic => do
  let result ← runAttempt testReport do
    evalTactic (← `(tactic| exact True.intro))
  match result with
  | .ok report =>
      unless report.method = testReport.method do
        throwError "successful transaction returned the wrong report"
  | .error failure => throwError "transaction unexpectedly failed: {repr failure}"

example : True ∧ True := by
  expect_partial_attempt
  constructor <;> trivial

example : True ∧ True := by
  expect_throwing_attempt
  constructor <;> trivial

example : True ∧ True := by
  expect_quiet_partial_attempt
  constructor <;> trivial

-- A successful focused attempt must retain sibling goals.
example : True ∧ True := by
  constructor
  · close_transactionally
  · trivial
