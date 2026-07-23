/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert

/-!
# Isolated Solver Protocol Tests

Synthetic solvers exercise proof-artifact isolation independently of numerical
engines.
-/

open Lean Meta Elab Tactic
open LeanCert.Tactic
open LeanCert.Tactic.Solver

set_option linter.unusedTactic false

private def testReport : SolverReport := {
  intent := .intervalBound
  solver := `syntheticSolver
  method := "synthetic protocol test"
  cost := 0
}

private def assertOriginalGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  unless after == before do
    throwError "isolated solver did not restore the original goal list"

private def runSynthetic (solver : TacticM Unit) : TacticM AttemptOutcome := do
  let goal ← getMainGoal
  proveWithTactic testReport (← goal.getType) solver

elab "expect_partial_attempt" : tactic => do
  let before ← getGoals
  let result ← runSynthetic do
    evalTactic (← `(tactic| constructor))
    evalTactic (← `(tactic| exact True.intro))
  match result with
  | .inconclusive evidence =>
      unless evidence.detail.contains "1 proof obligation" do
        throwError "expected one remaining proof obligation, got: {evidence.detail}"
  | _ => throwError "expected an inconclusive outcome"
  assertOriginalGoals before

elab "expect_throwing_attempt" : tactic => do
  let before ← getGoals
  let result ← runSynthetic do
    evalTactic (← `(tactic| constructor))
    throwError "synthetic failure after mutation"
  match result with
  | .inconclusive evidence =>
      unless evidence.detail.contains "could not construct a complete certificate" do
        throwError "expected a sanitized backend failure"
  | _ => throwError "expected an inconclusive outcome"
  assertOriginalGoals before

elab "expect_quiet_partial_attempt" : tactic => do
  let before ← getGoals
  let result ← runSynthetic do
    logWarning "this speculative warning must not leak"
    evalTactic (← `(tactic| constructor))
    evalTactic (← `(tactic| exact True.intro))
  match result with
  | .inconclusive _ => pure ()
  | _ => throwError "expected an inconclusive outcome"
  assertOriginalGoals before

elab "close_with_artifact" : tactic => do
  let result ← runSynthetic do
    evalTactic (← `(tactic| exact True.intro))
  match result with
  | .proved artifact =>
      unless artifact.report.method = testReport.method do
        throwError "successful solver returned the wrong report"
      let goal ← getMainGoal
      goal.assign artifact.proof
      replaceMainGoal []
  | _ => throwError "isolated solver unexpectedly failed"

elab "expect_invalid_artifact_rejected" : tactic => do
  let proposition := mkConst ``True
  let unresolved ← mkFreshExprMVar proposition
  let artifact : ProofArtifact := {
    proof := unresolved
    proposition
    report := testReport
  }
  match ← validateProofArtifact artifact with
  | .error detail =>
      unless detail.contains "unresolved metavariables" do
        throwError "unexpected artifact validation failure: {detail}"
  | .ok _ => throwError "invalid proof artifact was accepted"

elab "close_with_native_artifact" : tactic => do
  let result ← runSynthetic do
    evalTactic (← `(tactic| native_decide))
  match result with
  | .proved artifact =>
      let goal ← getMainGoal
      goal.assign artifact.proof
      replaceMainGoal []
  | .internalError _ detail => throwError "native artifact failed validation: {detail}"
  | _ => throwError "native artifact attempt unexpectedly failed"

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
  · close_with_artifact
  · trivial

example : True := by
  expect_invalid_artifact_rejected
  trivial

-- Successful native computation adds a generated declaration; that declaration
-- must survive while the original sibling goal is restored.
example : List.length (List.range 10) = 10 ∧ True := by
  constructor
  · close_with_native_artifact
  · trivial
