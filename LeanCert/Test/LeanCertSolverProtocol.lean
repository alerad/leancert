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

private def testPlan : SolverPlan := {
  intent := .intervalBound
  solver := `syntheticSolver
  strategy := "synthetic protocol test"
  cost := 0
  backendPolicy := .policy "Dyadic-first with Rational fallback"
  verificationRequested := .auto
}

private def assertOriginalGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  unless after == before do
    throwError "isolated solver did not restore the original goal list"

private def localEnvironmentSize : TacticM Nat := do
  return (← getEnv).constants.map₂.foldl (init := 0) fun count _ _ => count + 1

private def runSynthetic (solver : TacticM Unit) : TacticM AttemptOutcome := do
  let goal ← getMainGoal
  proveWithTactic testPlan (← goal.getType) solver

private def runSyntheticWithPlan (plan : SolverPlan) (solver : TacticM Unit) :
    TacticM AttemptOutcome := do
  let goal ← getMainGoal
  proveWithTactic plan (← goal.getType) solver

private def runSyntheticReported (solver : TacticM SolverExecution) :
    TacticM AttemptOutcome := do
  let goal ← getMainGoal
  proveWithTacticReported testPlan (← goal.getType) solver

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

elab "expect_reported_exception_is_internal" : tactic => do
  let before ← getGoals
  let intended := before.head!
  let environmentSizeBefore ← localEnvironmentSize
  let result ← runSyntheticReported do
    evalTactic (← `(tactic| native_decide))
    throwError "unexpected reported-core exception"
  match result with
  | .internalError solver detail =>
      unless solver == testPlan.solver &&
          detail.contains "unexpected reported-core exception" do
        throwError "reported exception lost its typed internal-error context"
  | _ => throwError "reported-core exception was not classified as internal"
  assertOriginalGoals before
  if ← intended.isAssigned then
    throwError "failed reported attempt assigned the caller's goal"
  let environmentSizeAfter ← localEnvironmentSize
  unless environmentSizeAfter == environmentSizeBefore do
    throwError "failed native attempt leaked a generated environment declaration"

elab "expect_reported_error_message_is_internal" : tactic => do
  let before ← getGoals
  let result ← runSyntheticReported do
    logError "unexpected reported-core diagnostic"
    return {}
  match result with
  | .internalError solver detail =>
      unless solver == testPlan.solver &&
          detail.contains "unexpected reported-core diagnostic" do
        throwError "reported error diagnostic lost its internal-error context"
  | _ => throwError "reported-core error diagnostic was classified as rejection"
  assertOriginalGoals before

elab "expect_subdivision_failure_detail" : tactic => do
  let before ← getGoals
  let plan := {
    testPlan with
    strategyId := StrategyId.subdivision
    -- Deliberately unrelated display text: diagnostics must use the stable kind.
    strategy := "polished user-facing name"
  }
  let result ← runSyntheticWithPlan plan do
    throwError "synthetic subdivision failure"
  match result with
  | .inconclusive evidence =>
      unless evidence.detail.contains "configured depth" do
        throwError "expected subdivision-specific guidance, got: {evidence.detail}"
  | _ => throwError "expected an inconclusive subdivision outcome"
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
      unless artifact.report.plan.strategy = testPlan.strategy do
        throwError "successful solver returned the wrong report"
      match artifact.report.execution.backend with
      | none => pure ()
      | _ => throwError "legacy compatibility solver fabricated execution metadata"
      let goal ← getMainGoal
      goal.assign artifact.proof
      replaceMainGoal []
  | _ => throwError "isolated solver unexpectedly failed"

elab "close_with_reported_artifact" : tactic => do
  let result ← runSyntheticReported do
    evalTactic (← `(tactic| exact True.intro))
    return {
      backend := some .rationalInterval
      verificationUsage := {
        kernelChecks := 1
        nativeChecks := 2
        autoGateReasons := #["finite-sum cost gate"]
      }
      checker := some `syntheticChecker
      verifier := some `syntheticChecker_sound
    }
  match result with
  | .proved artifact =>
      match artifact.report.execution.backend with
      | some .rationalInterval => pure ()
      | _ => throwError "reported backend did not reach the final artifact"
      let usage := artifact.report.execution.verificationUsage
      unless usage.kernelChecks = 1 && usage.nativeChecks = 2 &&
          usage.autoGateReasons == #["finite-sum cost gate"] do
        throwError "reported verification events did not reach the final artifact"
      let goal ← getMainGoal
      goal.assign artifact.proof
      replaceMainGoal []
  | _ => throwError "reported isolated solver unexpectedly failed"

elab "expect_failed_metadata_isolated" : tactic => do
  let before ← getGoals
  let failed ← runSyntheticReported do
    evalTactic (← `(tactic| constructor))
    return {
      backend := some .dyadicInterval
      verificationUsage := { nativeChecks := 99 }
      notes := #["must not leak"]
    }
  match failed with
  | .inconclusive _ => pure ()
  | _ => throwError "expected the Dyadic attempt to be inconclusive"
  assertOriginalGoals before
  let successful ← runSyntheticReported do
    evalTactic (← `(tactic| exact And.intro True.intro True.intro))
    return {
      backend := some .rationalInterval
      verificationUsage := { kernelChecks := 1 }
    }
  match successful with
  | .proved artifact =>
      match artifact.report.execution.backend with
      | some .rationalInterval => pure ()
      | _ => throwError "failed Dyadic metadata leaked into Rational success"
      let usage := artifact.report.execution.verificationUsage
      unless usage.kernelChecks = 1 && usage.nativeChecks = 0 do
        throwError "failed verification events leaked into winning report"
  | _ => throwError "expected Rational fallback to succeed"
  assertOriginalGoals before

elab "expect_verification_usage_monoid" : tactic => do
  let a : Solver.VerificationUsage := {
    kernelChecks := 1
    autoGateReasons := #["a"]
  }
  let b : Solver.VerificationUsage := {
    nativeChecks := 2
    kernelFallbacks := 3
    autoGateReasons := #["b"]
  }
  let c : Solver.VerificationUsage := {
    kernelChecks := 4
    nativeChecks := 5
    autoGateReasons := #["c"]
  }
  let left := (a.combine b).combine c
  let right := a.combine (b.combine c)
  unless left.kernelChecks = right.kernelChecks &&
      left.nativeChecks = right.nativeChecks &&
      left.kernelFallbacks = right.kernelFallbacks &&
      left.autoGateReasons == right.autoGateReasons do
    throwError "verification event aggregation is not associative"
  unless left.kernelChecks = 5 && left.nativeChecks = 7 &&
      left.kernelFallbacks = 3 &&
      left.autoGateReasons == #["a", "b", "c"] do
    throwError "verification event aggregation lost data"

elab "expect_invalid_artifact_rejected" : tactic => do
  let proposition := mkConst ``True
  let unresolved ← mkFreshExprMVar proposition
  let artifact : ProofArtifact := {
    proof := unresolved
    proposition
    report := { plan := testPlan }
  }
  match ← validateProofArtifact proposition artifact with
  | .error detail =>
      unless detail.contains "unresolved metavariables" do
        throwError "unexpected artifact validation failure: {detail}"
  | .ok _ => throwError "invalid proof artifact was accepted"

elab "expect_mismatched_proposition_rejected" : tactic => do
  let prepared := mkConst ``True
  let proposition ← mkAppM ``And #[mkConst ``True, mkConst ``True]
  let proof ← mkAppM ``And.intro #[mkConst ``True.intro, mkConst ``True.intro]
  let artifact : ProofArtifact := {
    proof
    proposition
    report := { plan := testPlan }
  }
  match ← validateProofArtifact prepared artifact with
  | .error detail =>
      unless detail.contains "does not match prepared proposition" do
        throwError "unexpected proposition mismatch diagnostic: {detail}"
  | .ok _ => throwError "artifact for a different proposition was accepted"

elab "expect_central_disposition" : tactic => do
  let unsupported : AttemptOutcome := .unsupported {
    expression := "synthetic"
  }
  let obstruction : AttemptOutcome := .internalError `syntheticSolver "synthetic"
  unless unsupported.disposition == .continue do
    throwError "unsupported outcomes must continue the portfolio"
  unless obstruction.disposition == .stop do
    throwError "internal errors must stop the portfolio"

elab "expect_metadata_irrelevant_to_acceptance" : tactic => do
  let proposition := mkConst ``True
  let report : SolverReport := {
    plan := {
      testPlan with
      intent := .uniqueRoot
      strategy := "deliberately false metadata"
      backendPolicy := .fixed .affineArithmetic
      checker := some `NotARealChecker
      verifier := some `NotAGoldenTheorem
    }
    execution := {
      backend := some .dyadicInterval
      verificationUsage := {
        nativeChecks := 1000000
        autoGateReasons := #["fabricated"]
      }
      checker := some `AlsoNotARealChecker
      verifier := some `AlsoNotAGoldenTheorem
    }
  }
  let artifact : ProofArtifact := {
    proof := mkConst ``True.intro
    proposition
    report
  }
  match ← validateProofArtifact proposition artifact with
  | .ok _ => pure ()
  | .error detail =>
      throwError "irrelevant report metadata affected kernel acceptance: {detail}"

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
  expect_reported_exception_is_internal
  constructor <;> trivial

example : True := by
  expect_reported_error_message_is_internal
  trivial

example : True := by
  expect_subdivision_failure_detail
  trivial

example : True ∧ True := by
  expect_quiet_partial_attempt
  constructor <;> trivial

example : True ∧ True := by
  expect_failed_metadata_isolated
  constructor <;> trivial

-- A successful focused attempt must retain sibling goals.
example : True ∧ True := by
  constructor
  · close_with_artifact
  · trivial

example : True := by
  expect_invalid_artifact_rejected
  expect_mismatched_proposition_rejected
  expect_metadata_irrelevant_to_acceptance
  expect_verification_usage_monoid
  expect_central_disposition
  trivial

example : True := by
  close_with_reported_artifact

example : True := by
  trivial

-- Successful native computation adds a generated declaration; that declaration
-- must survive while the original sibling goal is restored.
example : List.length (List.range 10) = 10 ∧ True := by
  constructor
  · close_with_native_artifact
  · trivial
