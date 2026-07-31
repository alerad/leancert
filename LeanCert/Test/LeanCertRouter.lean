/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Semantic Router Tests

Natural mathematical statements are proved through the public `leancert`
front door, importing only the stable tactic umbrella.
-/

open LeanCert
open MeasureTheory
open Lean Meta Elab Tactic
open LeanCert.Tactic
open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Solver

set_option linter.unusedTactic false

private def checkerExpr : LeanCert.Core.Expr := .var 0
private def checkerInterval : LeanCert.Core.IntervalRat := ⟨0, 1, by norm_num⟩
private def checkerInterval35 : LeanCert.Core.IntervalRat := ⟨3, 5, by norm_num⟩
private def checkerIntervalNeg11 : LeanCert.Core.IntervalRat := ⟨-1, 1, by norm_num⟩

private def adapterTestPlan : SolverPlan := {
  intent := .pointInequality
  solver := `typedAdapterTest
  strategyId := .pointEnclosure
  strategy := "typed adapter preservation test"
  cost := 0
  backendPolicy := .notApplicable
  verificationRequested := .kernel
}

private def expectTypedAdapterFailure : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let semantic ← goal.withContext do
    match ← Semantic.parseGoal goalType with
    | .ok semantic => pure semantic
    | .error failure => throwError "test goal did not parse: {failure.detail}"
  let prepared ← goal.withContext do
    match ← Semantic.prepareGoal semantic with
    | .ok prepared => pure prepared
    | .error failure => throwError "test goal did not prepare: {failure.detail}"
  let spec : SolverSpec := {
    report := adapterTestPlan
    solve := pure <|
      .error (.routerFailure (.internalError "typed result survived semantic transport"))
  }
  match ← spec.toSemanticSolver.attempt prepared {} with
  | AttemptOutcome.routerFailure (Diagnostic.RouterFailure.internalError detail) =>
      unless detail == "typed result survived semantic transport" do
        throwError "typed router failure detail changed during transport"
  | outcome =>
      throwError "semantic adapter discarded its typed result: {repr outcome.disposition}"

elab "expect_typed_adapter_failure" : tactic =>
  expectTypedAdapterFailure

private def expectExactRouteExceptionTerminal : TacticM Unit := do
  let goal ← getMainGoal
  let proposition ← goal.getType
  let plan : SolverPlan := {
    intent := .pointInequality
    solver := `syntheticExactRoute
    strategyId := .exactNormalization
    strategy := "synthetic throwing exact route"
    cost := 0
    backendPolicy := .notApplicable
    verificationRequested := .kernel
  }
  match ← proveWithTypedSolver plan proposition <|
      exactTacticAttemptTyped (throwError "synthetic exact-route exception") with
  | .internalError solver detail =>
      unless solver == `syntheticExactRoute &&
          detail.contains "synthetic exact-route exception" do
        throwError "exact-route exception lost its terminal diagnostic: {detail}"
  | outcome =>
      throwError "exact-route exception was not terminal: {repr outcome.disposition}"

elab "expect_exact_route_exception_terminal" : tactic =>
  expectExactRouteExceptionTerminal

elab "expect_terminal_outcome_stops" : tactic => do
  let mut continued := false
  try
    enforceAttemptDisposition .compact .pointInequality <|
      .internalError `syntheticTerminalSolver "terminal sentinel"
    continued := true
  catch exception =>
    let detail ← exception.toMessageData.toString
    unless detail.contains "terminal sentinel" do
      throwError "terminal outcome lost its diagnostic: {detail}"
  if continued then
    throwError "routing continued after a terminal outcome"

syntax (name := expectRootTypedReport)
  "expect_root_typed_report" ident : tactic

private structure RootReportProbe where
  checker : Name
  verifier : Name
  verification : LeanCert.Tactic.VerificationUsage
  expectedChecker : Name
  expectedVerifier : Name

@[tactic expectRootTypedReport]
unsafe def elabExpectRootTypedReport : Tactic := fun stx => do
  let family := stx[1].getId
  let probe : RootReportProbe ←
    if family == `existence then
      match ← Discovery.intervalRootsCoreTyped 10 with
      | .ok outcome => pure {
          checker := outcome.checker
          verifier := outcome.verifier
          verification := outcome.verification
          expectedChecker := ``LeanCert.Validity.RootFinding.checkSignChange
          expectedVerifier := ``LeanCert.Validity.RootFinding.verify_sign_change
        }
      | .error failure => throwError "typed root-existence route failed: {repr failure}"
    else if family == `unique then
      match ← Discovery.intervalUniqueRootCoreTyped 10 with
      | .ok outcome => pure {
          checker := outcome.checker
          verifier := outcome.verifier
          verification := outcome.verification
          expectedChecker := ``LeanCert.Validity.RootFinding.checkNewtonContractsCore
          expectedVerifier := ``LeanCert.Validity.RootFinding.verify_unique_root_computable
        }
      | .error failure => throwError "typed unique-root route failed: {repr failure}"
    else
      match ← Auto.rootBoundCoreTyped 10 with
      | .ok outcome => pure {
          checker := outcome.checker
          verifier := outcome.verifier
          verification := outcome.verification
          expectedChecker := ``LeanCert.Validity.RootFinding.checkNoRoot
          expectedVerifier := ``LeanCert.Validity.RootFinding.verify_no_root
        }
      | .error failure => throwError "typed no-root route failed: {repr failure}"
  unless probe.checker == probe.expectedChecker &&
      probe.verifier == probe.expectedVerifier do
    throwError "root route retained the wrong checker/Golden Theorem: \
      checker={probe.checker}, verifier={probe.verifier}"
  unless probe.verification.nativeChecks + probe.verification.kernelChecks == 1 do
    throwError "root route did not retain exactly one successful certificate check"

syntax (name := expectRootRejectionRollback)
  "expect_root_rejection_rollback" ident : tactic

@[tactic expectRootRejectionRollback]
unsafe def elabExpectRootRejectionRollback : Tactic := fun stx => do
  let family := stx[1].getId
  let originalGoals ← getGoals
  let originalType ← (← getMainGoal).getType
  let rejected ←
    if family == `existence then
      match ← Discovery.intervalRootsCoreTyped 10 with
      | .error (.rejected _) => pure true
      | .error failure => throwError "root existence returned wrong failure: {repr failure}"
      | .ok _ => pure false
    else if family == `unique then
      match ← Discovery.intervalUniqueRootCoreTyped 10 with
      | .error (.rejected _) => pure true
      | .error failure => throwError "unique root returned wrong failure: {repr failure}"
      | .ok _ => pure false
    else
      match ← Auto.rootBoundCoreTyped 10 with
      | .error (.rejected _) => pure true
      | .error failure => throwError "no-root route returned wrong failure: {repr failure}"
      | .ok _ => pure false
  unless rejected do
    throwError "false root candidate was accepted"
  let restoredGoals ← getGoals
  unless restoredGoals == originalGoals do
    throwError "typed root rejection did not restore the caller's goal list"
  let restoredType ← (← getMainGoal).getType
  unless ← isDefEq restoredType originalType do
    throwError "typed root rejection changed the caller's goal"

syntax (name := expectRootUnsupportedRollback)
  "expect_root_unsupported_rollback" : tactic

@[tactic expectRootUnsupportedRollback]
unsafe def elabExpectRootUnsupportedRollback : Tactic := fun _ => do
  let originalGoals ← getGoals
  let checkRestored (family : String) : TacticM Unit := do
    unless (← getGoals) == originalGoals do
      throwError "{family} unsupported result did not restore the goal list"
  match ← Discovery.intervalRootsCoreTyped 10 with
  | .error (.unsupported ..) => checkRestored "root existence"
  | .error failure => throwError "root existence returned wrong malformed-goal failure: {repr failure}"
  | .ok _ => throwError "root existence accepted a malformed goal"
  match ← Discovery.intervalUniqueRootCoreTyped 10 with
  | .error (.unsupported ..) => checkRestored "unique root"
  | .error failure => throwError "unique root returned wrong malformed-goal failure: {repr failure}"
  | .ok _ => throwError "unique root accepted a malformed goal"
  match ← Auto.rootBoundCoreTyped 10 with
  | .error (.unsupported ..) => checkRestored "no root"
  | .error failure => throwError "no-root returned wrong malformed-goal failure: {repr failure}"
  | .ok _ => throwError "no-root accepted a malformed goal"

syntax (name := expectRootRouterReport)
  "expect_root_router_report" ident : tactic

@[tactic expectRootRouterReport]
unsafe def elabExpectRootRouterReport : Tactic := fun stx => do
  let family := stx[1].getId
  let result ← runLeanCert {} .compact
  let (expectedChecker, expectedVerifier) :=
    if family == `existence then
      (``LeanCert.Validity.RootFinding.checkSignChange,
        ``LeanCert.Validity.RootFinding.verify_sign_change)
    else if family == `unique then
      (``LeanCert.Validity.RootFinding.checkNewtonContractsCore,
        ``LeanCert.Validity.RootFinding.verify_unique_root_computable)
    else
      (``LeanCert.Validity.RootFinding.checkNoRoot,
        ``LeanCert.Validity.RootFinding.verify_no_root)
  unless result.execution.checker == some expectedChecker &&
      result.execution.verifier == some expectedVerifier do
    throwError "front-door root route lost certificate provenance: \
      checker={result.execution.checker}, verifier={result.execution.verifier}"
  unless result.execution.verificationUsage.nativeChecks +
      result.execution.verificationUsage.kernelChecks == 1 do
    throwError "front-door root route did not retain exactly one certificate check"

example : ∃ x ∈ checkerIntervalNeg11,
    LeanCert.Core.Expr.eval (fun _ => x) (.var 0) = 0 := by
  expect_root_typed_report existence

example : ∃! x, x ∈ checkerIntervalNeg11 ∧
    LeanCert.Core.Expr.eval (fun _ => x) (.var 0) = 0 := by
  expect_root_typed_report unique

example : ∀ x ∈ checkerInterval,
    LeanCert.Core.Expr.eval (fun _ => x) (.add (.var 0) (.const 2)) ≠ 0 := by
  expect_root_typed_report absent

example (h : ∃ x ∈ checkerInterval,
    LeanCert.Core.Expr.eval (fun _ => x)
      (.add (.mul (.var 0) (.var 0)) (.const 1)) = 0) :
    ∃ x ∈ checkerInterval,
      LeanCert.Core.Expr.eval (fun _ => x)
        (.add (.mul (.var 0) (.var 0)) (.const 1)) = 0 := by
  expect_root_rejection_rollback existence
  exact h

example (h : ∃! x, x ∈ checkerInterval ∧
    LeanCert.Core.Expr.eval (fun _ => x) (.const 1) = 0) :
    ∃! x, x ∈ checkerInterval ∧
      LeanCert.Core.Expr.eval (fun _ => x) (.const 1) = 0 := by
  expect_root_rejection_rollback unique
  exact h

example (h : ∀ x ∈ checkerIntervalNeg11,
    LeanCert.Core.Expr.eval (fun _ => x) (.var 0) ≠ 0) :
    ∀ x ∈ checkerIntervalNeg11,
      LeanCert.Core.Expr.eval (fun _ => x) (.var 0) ≠ 0 := by
  expect_root_rejection_rollback absent
  exact h

example (h : True) : True := by
  expect_root_unsupported_rollback
  exact h

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  expect_root_router_report existence

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 = 2 := by
  expect_root_router_report unique

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x + 2 ≠ 0 := by
  expect_root_router_report absent

syntax (name := expectRationalPointReport) "expect_rational_point_report" : tactic

@[tactic expectRationalPointReport]
unsafe def elabExpectRationalPointReport : Tactic := fun _ => do
  let result ← runLeanCert {} .compact
  unless result.execution.backend == some .rationalInterval do
    throwError "point difference route did not report Rational execution"
  unless result.execution.verificationUsage.nativeChecks == 1 &&
      result.execution.verificationUsage.kernelChecks == 0 do
    throwError "point Rational report contains leaked or missing verification events"
  unless result.execution.checker ==
        some ``LeanCert.Validity.checkStrictLowerBound &&
      result.execution.verifier ==
        some ``LeanCert.Validity.verify_strict_lower_bound do
    throwError "point Rational checker/Golden-Theorem identity was not retained: \
      checker={result.execution.checker}, verifier={result.execution.verifier}"

syntax (name := expectOptimizationReport) "expect_optimization_report" : tactic

@[tactic expectOptimizationReport]
unsafe def elabExpectOptimizationReport : Tactic := fun _ => do
  let outcome ←
    match ← Auto.optBoundCoreTyped 64 false 10 with
    | .ok outcome => pure outcome
    | .error failure =>
        throwError "typed optimization route unexpectedly failed: {repr failure}"
  unless outcome.maxIterations == 64 do
    throwError "optimization outcome lost its configured iteration limit"
  unless outcome.direction == .upper &&
      outcome.checker == ``LeanCert.Validity.GlobalOpt.checkGlobalUpperBound &&
      outcome.verifier == ``LeanCert.Validity.GlobalOpt.verify_global_upper_bound do
    throwError "optimization report retained the wrong direction/checker/Golden Theorem"

syntax (name := expectDiscoveryReport) "expect_discovery_report" : tactic

@[tactic expectDiscoveryReport]
unsafe def elabExpectDiscoveryReport : Tactic := fun _ => do
  let result ← runLeanCert {} .compact
  let some statistics := result.execution.optimization
    | throwError "discovery route returned no structured statistics"
  unless statistics.iterations.isSome && statistics.gap.isSome &&
      statistics.remainingBoxes.isSome do
    throwError "discovery report did not retain actual optimizer results"
  unless result.execution.checker.isSome && result.execution.verifier.isSome do
    throwError "discovery report lost certification identity"
  unless result.execution.backend == some .rationalInterval do
    throwError "discovery search backend was conflated with witness certification"

syntax (name := expectMvDiscoveryReport)
  "expect_mv_discovery_report" ident : tactic

@[tactic expectMvDiscoveryReport]
unsafe def elabExpectMvDiscoveryReport : Tactic := fun stx => do
  let result ← runLeanCert {} .compact
  let some statistics := result.execution.optimization
    | throwError "multivariate discovery returned no optimization statistics"
  unless statistics.termination.isSome && statistics.iterations.isSome &&
      statistics.gap.isSome do
    throwError "multivariate discovery lost search termination evidence"
  let expectedDirection := stx[1].getId
  let (checker, verifier) :=
    if expectedDirection == `minimum then
      (``LeanCert.Validity.GlobalOpt.checkGlobalLowerBound,
       ``LeanCert.Validity.GlobalOpt.verify_global_lower_bound)
    else
      (``LeanCert.Validity.GlobalOpt.checkGlobalUpperBound,
       ``LeanCert.Validity.GlobalOpt.verify_global_upper_bound)
  unless result.execution.checker == some checker &&
      result.execution.verifier == some verifier do
    throwError "multivariate discovery retained the wrong certificate identity: \
      checker={result.execution.checker}, verifier={result.execution.verifier}"
  unless result.execution.backend == some .rationalInterval do
    throwError "multivariate discovery did not report its Rational search backend"

syntax (name := expectLooseDiscoverySuccess)
  "expect_loose_discovery_success" : tactic

@[tactic expectLooseDiscoverySuccess]
unsafe def elabExpectLooseDiscoverySuccess : Tactic := fun _ => do
  match ← Discovery.intervalMinimizeCoreTyped 10 with
  | .ok outcome =>
      unless outcome.termination == .iterationLimit do
        throwError "expected iteration-limited certified discovery, got \
          {repr outcome.termination}"
  | .error failure =>
      throwError "a loose search with a certifiable endpoint failed: {repr failure}"

syntax (name := expectAttainedReport)
  "expect_attained_report" ident : tactic

@[tactic expectAttainedReport]
unsafe def elabExpectAttainedReport : Tactic := fun stx => do
  let direction := stx[1].getId
  let outcome ←
    if direction == `minimum then
      match ← Discovery.intervalArgminCoreTyped 10 with
      | .ok outcome => pure outcome
      | .error failure => throwError "typed argmin failed: {repr failure}"
    else
      match ← Discovery.intervalArgmaxCoreTyped 10 with
      | .ok outcome => pure outcome
      | .error failure => throwError "typed argmax failed: {repr failure}"
  let expectedVerifier :=
    if direction == `minimum then ``LeanCert.Validity.verify_argmin
    else ``LeanCert.Validity.verify_argmax
  unless outcome.verifier == some expectedVerifier do
    throwError "attained-extremum report retained the wrong Golden Theorem"
  unless outcome.certificates.size == 2 do
    throwError "attained proof retained {outcome.certificates.size} \
      certificates instead of two"
  let first := outcome.certificates[0]!
  let second := outcome.certificates[1]!
  let expectedFirst :=
    if direction == `minimum then ``LeanCert.Validity.checkLowerBound
    else ``LeanCert.Validity.checkUpperBound
  let expectedSecond :=
    if direction == `minimum then ``LeanCert.Validity.checkPointUpperBound
    else ``LeanCert.Validity.checkPointLowerBound
  unless first.checker == expectedFirst && second.checker == expectedSecond do
    throwError "attained proof retained the wrong constituent checkers"
  let usage : LeanCert.Tactic.VerificationUsage :=
    outcome.certificates.foldl
      (fun total certificate => total.combine certificate.verification) {}
  unless usage.kernelChecks + usage.nativeChecks == 2 do
    throwError "attained proof did not retain exactly two successful checks"

syntax (name := expectCompactExtremumRoute)
  "expect_compact_extremum_route" : tactic

@[tactic expectCompactExtremumRoute]
unsafe def elabExpectCompactExtremumRoute : Tactic := fun _ => do
  let result ← runLeanCert {} .compact
  unless result.plan.strategy.contains "compact extreme-value theorem" do
    throwError "front-door extremum routing changed unexpectedly: \
      {result.plan.strategy}"
  unless result.execution.certificates.isEmpty do
    throwError "compact extreme-value route fabricated numerical certificates"

syntax (name := expectAttainedRejectionRollback)
  "expect_attained_rejection_rollback" ident : tactic

@[tactic expectAttainedRejectionRollback]
unsafe def elabExpectAttainedRejectionRollback : Tactic := fun stx => do
  let callerGoals ← getGoals
  let direction := stx[1].getId
  let probeType ←
    if direction == `minimum then
      Term.elabTerm (← `(term| ∃ x ∈ checkerInterval35, ∀ y ∈ checkerInterval35,
        LeanCert.Core.Expr.eval (fun _ => x) (.sin (.var 0)) ≤
          LeanCert.Core.Expr.eval (fun _ => y) (.sin (.var 0))))
        (some (mkSort .zero))
    else
      Term.elabTerm (← `(term| ∃ x ∈ checkerInterval, ∀ y ∈ checkerInterval,
        LeanCert.Core.Expr.eval (fun _ => y) (.sin (.var 0)) ≤
          LeanCert.Core.Expr.eval (fun _ => x) (.sin (.var 0))))
        (some (mkSort .zero))
  let probe ← mkFreshExprMVar probeType
  setGoals [probe.mvarId!]
  let beforeType ← probe.mvarId!.getType
  let result ←
    if direction == `minimum then
      Discovery.intervalArgminCoreTyped 10
    else
      Discovery.intervalArgmaxCoreTyped 10
  match result with
  | .error (.rejectedCandidate ..) =>
      let afterType ← (← getMainGoal).getType
      unless ← isDefEq beforeType afterType do
        throwError "rejected attained candidate changed the caller's goal"
      unless (← getGoals).length == 1 do
        throwError "rejected attained candidate changed the caller's goal list"
      unless !(← probe.mvarId!.isAssigned) do
        throwError "rejected attained candidate retained a partial proof assignment"
      setGoals callerGoals
      evalTactic (← `(tactic| trivial))
  | .error failure =>
      throwError "attained candidate had wrong failure classification: {repr failure}"
  | .ok _ =>
      throwError "irrational attained candidate unexpectedly certified"

syntax (name := expectTypedOptimizationRollback)
  "expect_typed_optimization_rollback" : tactic

@[tactic expectTypedOptimizationRollback]
unsafe def elabExpectTypedOptimizationRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let before ← goal.getType
  match ← Auto.optBoundCoreTyped 8 false 10 with
  | .error (.unsupported ..) =>
      let after ← (← getMainGoal).getType
      unless ← isDefEq before after do
        throwError "unsupported opt_bound mutated the caller's goal"
  | .error failure =>
      throwError "unsupported opt_bound had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "unsupported opt_bound unexpectedly succeeded"

syntax (name := expectTypedMultivariateRollback)
  "expect_typed_multivariate_rollback" : tactic

@[tactic expectTypedMultivariateRollback]
unsafe def elabExpectTypedMultivariateRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let before ← goal.getType
  match ← Auto.multivariateBoundCoreTyped 8 (1 / 1000) false 10 with
  | .error (.unsupported ..) =>
      let after ← (← getMainGoal).getType
      unless ← isDefEq before after do
        throwError "unsupported multivariate bound mutated the caller's goal"
  | .error failure =>
      throwError "unsupported multivariate bound had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "unsupported multivariate bound unexpectedly succeeded"

syntax (name := expectTypedSubdivisionReport)
  "expect_typed_subdivision_report" : tactic

@[tactic expectTypedSubdivisionReport]
unsafe def elabExpectTypedSubdivisionReport : Tactic := fun _ => do
  match ← Auto.intervalBoundSubdivCoreTyped (some 10) 8 with
  | .ok outcome =>
      unless outcome.comparison == .upper do
        throwError "typed subdivision retained the wrong comparison"
      unless outcome.checker == ``LeanCert.Validity.checkUpperBound &&
          outcome.verifier == ``LeanCert.Validity.verify_upper_bound_Icc_core do
        throwError "typed subdivision retained the wrong checker or verifier"
      unless outcome.execution.boxesExamined == 27 &&
          outcome.execution.certifiedLeaves == 14 &&
          outcome.execution.deepestDepthUsed == 5 do
        throwError "typed subdivision retained incorrect search statistics"
      let usage := outcome.execution.verification
      unless usage.kernelChecks + usage.nativeChecks ==
          outcome.execution.certifiedLeaves do
        throwError "subdivision verification count does not match certified leaves"
  | .error failure =>
      throwError "typed subdivision unexpectedly failed: {repr failure}"

syntax (name := expectTypedSubdivisionExhaustion)
  "expect_typed_subdivision_exhaustion" : tactic

@[tactic expectTypedSubdivisionExhaustion]
unsafe def elabExpectTypedSubdivisionExhaustion : Tactic := fun _ => do
  let goal ← getMainGoal
  let before ← goal.getType
  let environmentBefore := (← getEnv).constants.toList.length
  let messagesBefore := (← Core.getMessageLog).toList.length
  match ← Auto.intervalBoundSubdivCoreTyped (some 10) 0 with
  | .error (.exhausted 0 1 0 (some _)) =>
      let afterGoal ← getMainGoal
      let after ← afterGoal.getType
      unless goal == afterGoal && (← isDefEq before after) do
        throwError "exhausted subdivision changed the caller's goal"
      unless !(← goal.isAssigned) do
        throwError "exhausted subdivision retained a partial proof assignment"
      unless (← getEnv).constants.toList.length == environmentBefore do
        throwError "exhausted subdivision leaked an environment declaration"
      unless (← Core.getMessageLog).toList.length == messagesBefore do
        throwError "exhausted subdivision leaked a message"
  | .error failure =>
      throwError "subdivision exhaustion had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "zero-depth subdivision unexpectedly certified the tight bound"

syntax (name := expectTypedSubdivisionPartialRollback)
  "expect_typed_subdivision_partial_rollback" : tactic

@[tactic expectTypedSubdivisionPartialRollback]
unsafe def elabExpectTypedSubdivisionPartialRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let before ← goal.getType
  let environmentBefore := (← getEnv).constants.toList.length
  let messagesBefore := (← Core.getMessageLog).toList.length
  match ← Auto.intervalBoundSubdivCoreTyped (some 10) 4 with
  | .error (.exhausted ..) =>
      let afterGoal ← getMainGoal
      let after ← afterGoal.getType
      unless goal == afterGoal && (← isDefEq before after) do
        throwError "partially certified subdivision changed the caller's goal"
      unless !(← goal.isAssigned) do
        throwError "partially certified subdivision retained a proof assignment"
      unless (← getEnv).constants.toList.length == environmentBefore do
        throwError "partially certified subdivision leaked an environment declaration"
      unless (← Core.getMessageLog).toList.length == messagesBefore do
        throwError "partially certified subdivision leaked a message"
  | .error failure =>
      throwError "partial subdivision rollback had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "exact quarter bound unexpectedly certified at finite subdivision depth"

syntax (name := expectTypedSubdivisionUnsupported)
  "expect_typed_subdivision_unsupported" : tactic

@[tactic expectTypedSubdivisionUnsupported]
unsafe def elabExpectTypedSubdivisionUnsupported : Tactic := fun _ => do
  let goal ← getMainGoal
  let before ← goal.getType
  match ← Auto.intervalBoundSubdivCoreTyped (some 10) 2 with
  | .error (.unsupported ..) =>
      let afterGoal ← getMainGoal
      let after ← afterGoal.getType
      unless goal == afterGoal && (← isDefEq before after) do
        throwError "unsupported subdivision changed the caller's goal"
  | .error failure =>
      throwError "unsupported subdivision had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "unsupported subdivision unexpectedly succeeded"

syntax (name := expectTypedSubdivisionDomain)
  "expect_typed_subdivision_domain" : tactic

@[tactic expectTypedSubdivisionDomain]
unsafe def elabExpectTypedSubdivisionDomain : Tactic := fun _ => do
  let goal ← getMainGoal
  let before ← goal.getType
  match ← Auto.intervalBoundSubdivCoreTyped (some 10) 2 with
  | .error (.domainObstruction _ "Rational interval evaluation" _) =>
      let afterGoal ← getMainGoal
      let after ← afterGoal.getType
      unless goal == afterGoal && (← isDefEq before after) do
        throwError "domain-obstructed subdivision changed the caller's goal"
      unless !(← goal.isAssigned) do
        throwError "domain-obstructed subdivision retained a partial assignment"
  | .error failure =>
      throwError "subdivision domain failure had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "domain-obstructed subdivision unexpectedly succeeded"

example : ∀ ρ, LeanCert.Engine.Optimization.Box.envMem ρ
      ([⟨0, 1, by norm_num⟩] : LeanCert.Engine.Optimization.Box) →
    (∀ i, i ≥
      ([⟨0, 1, by norm_num⟩] : LeanCert.Engine.Optimization.Box).length →
      ρ i = 0) →
    LeanCert.Core.Expr.eval ρ
      (.mul (.var 0) (.var 0)) ≤ (1 : ℚ) := by
  expect_optimization_report

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, x * x ≥ m := by
  expect_discovery_report

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, x * x + y * y ≥ m := by
  expect_mv_discovery_report minimum

example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, x + y ≤ M := by
  expect_mv_discovery_report maximum

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 7, Real.sin x ≥ m := by
  expect_loose_discovery_success

example : ∃ x ∈ checkerInterval, ∀ y ∈ checkerInterval,
    LeanCert.Core.Expr.eval (fun _ => y) (.var 0) ≤
      LeanCert.Core.Expr.eval (fun _ => x) (.var 0) := by
  expect_attained_report maximum

example : ∃ x ∈ checkerInterval, ∀ y ∈ checkerInterval,
    LeanCert.Core.Expr.eval (fun _ => x) (.var 0) ≤
      LeanCert.Core.Expr.eval (fun _ => y) (.var 0) := by
  expect_attained_report minimum

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, y ≤ x := by
  expect_compact_extremum_route

example : True := by
  expect_attained_rejection_rollback maximum

example : True := by
  expect_attained_rejection_rollback minimum

example : True := by
  expect_typed_optimization_rollback
  trivial

example : True := by
  expect_typed_multivariate_rollback
  trivial

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  expect_typed_subdivision_report

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  expect_typed_subdivision_exhaustion
  interval_bound_subdiv 10 8

example (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (1 / 4 : ℚ)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (1 / 4 : ℚ) := by
  expect_typed_subdivision_partial_rollback
  exact h

example : True := by
  expect_typed_subdivision_unsupported
  trivial

example (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Real.log x ≤ 2) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, Real.log x ≤ 2 := by
  expect_typed_subdivision_domain
  exact h

syntax (name := expectTypedOptimizationRejection)
  "expect_typed_optimization_rejection" : tactic

@[tactic expectTypedOptimizationRejection]
unsafe def elabExpectTypedOptimizationRejection : Tactic := fun _ => do
  let callerGoals ← getGoals
  let falseType ← Term.elabTerm
    (← `(∀ ρ, LeanCert.Engine.Optimization.Box.envMem ρ
        ([⟨0, 2, by norm_num⟩] : LeanCert.Engine.Optimization.Box) →
      (∀ i, i ≥
        ([⟨0, 2, by norm_num⟩] : LeanCert.Engine.Optimization.Box).length →
        ρ i = 0) →
      LeanCert.Core.Expr.eval ρ
        (.mul (.var 0) (.var 0)) ≤ (1 : ℚ))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let falseType ← instantiateMVars falseType
  let falseGoal ← mkFreshExprMVar falseType
  setGoals [falseGoal.mvarId!]
  match ← Auto.optBoundCoreTyped 8 false 10 with
  | .error (.rejected _) =>
      unless !(← falseGoal.mvarId!.isAssigned) do
        throwError "rejected opt_bound mutated the caller's goal"
      setGoals callerGoals
      evalTactic (← `(tactic| trivial))
  | .error failure =>
      throwError "false opt_bound certificate had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "false opt_bound certificate unexpectedly succeeded"

example : True := by
  expect_typed_optimization_rejection

syntax (name := expectTypedMultivariateRejection)
  "expect_typed_multivariate_rejection" : tactic

@[tactic expectTypedMultivariateRejection]
unsafe def elabExpectTypedMultivariateRejection : Tactic := fun _ => do
  let callerGoals ← getGoals
  let falseType ← Term.elabTerm
    (← `(∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      x + y ≤ (-1 : ℚ))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let falseType ← instantiateMVars falseType
  let falseGoal ← mkFreshExprMVar falseType
  setGoals [falseGoal.mvarId!]
  match ← Auto.multivariateBoundCoreTyped 8 (1 / 1000) false 10 with
  | .error (.rejected _) =>
      unless !(← falseGoal.mvarId!.isAssigned) do
        throwError "rejected multivariate bound mutated the caller's goal"
      setGoals callerGoals
      evalTactic (← `(tactic| trivial))
  | .error failure =>
      throwError "false multivariate certificate had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "false multivariate certificate unexpectedly succeeded"

example : True := by
  expect_typed_multivariate_rejection

syntax (name := expectDiscoveryDomainObstruction)
  "expect_discovery_domain_obstruction" : tactic

@[tactic expectDiscoveryDomainObstruction]
unsafe def elabExpectDiscoveryDomainObstruction : Tactic := fun _ => do
  let callerGoals ← getGoals
  let obstructedType ← Term.elabTerm
    (← `(∃ m : ℚ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, Real.log x ≥ m)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let obstructedType ← instantiateMVars obstructedType
  let obstructedGoal ← mkFreshExprMVar obstructedType
  setGoals [obstructedGoal.mvarId!]
  match ← Discovery.intervalMinimizeCoreTyped 10 with
  | .error (.domainObstruction _ _ _) =>
      unless !(← obstructedGoal.mvarId!.isAssigned) do
        throwError "domain-obstructed discovery assigned its speculative goal"
      setGoals callerGoals
      evalTactic (← `(tactic| trivial))
  | .error failure =>
      throwError "domain-obstructed discovery had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "domain-obstructed discovery unexpectedly succeeded"

example : True := by
  expect_discovery_domain_obstruction

syntax (name := expectKernelBoundReport) "expect_kernel_bound_report" : tactic

@[tactic expectKernelBoundReport]
unsafe def elabExpectKernelBoundReport : Tactic := fun _ => do
  withTrustMode (some .kernel) do
    let result ← Auto.intervalBoundRationalCoreTyped 10
    let .ok outcome := result
      | throwError "direct Rational bound unexpectedly failed"
    let usage := Solver.VerificationUsage.ofEvents outcome.verification
    unless usage.kernelChecks == 1 && usage.nativeChecks == 0 do
      throwError "kernel bound report contains leaked or incorrect verification events"
    unless outcome.checker == some ``LeanCert.Validity.checkUpperBound &&
        outcome.verifier ==
          some ``LeanCert.Validity.verify_upper_bound_Icc_core do
      throwError "Rational bound checker/Golden-Theorem identity was not retained"

private def expectRationalBoundIdentity (checker verifier : Name) :
    TacticM Unit := do
  match ← Auto.intervalBoundRationalCoreTyped 10 with
  | .ok outcome =>
      unless outcome.checker == some checker && outcome.verifier == some verifier do
        throwError "unexpected Rational bound identity: checker={outcome.checker}, \
          verifier={outcome.verifier}"
  | .error failure =>
      throwError "Rational bound unexpectedly failed: {repr failure}"

elab "expect_rational_lower_bound" : tactic =>
  expectRationalBoundIdentity ``LeanCert.Validity.checkLowerBound
    ``LeanCert.Validity.verify_lower_bound_Icc_core

elab "expect_rational_strict_upper_bound" : tactic =>
  expectRationalBoundIdentity ``LeanCert.Validity.checkStrictUpperBound
    ``LeanCert.Validity.verify_strict_upper_bound_Icc_core

elab "expect_rational_strict_lower_bound" : tactic =>
  expectRationalBoundIdentity ``LeanCert.Validity.checkStrictLowerBound
    ``LeanCert.Validity.verify_strict_lower_bound_Icc_core

elab "expect_rational_bound_inconclusive" : tactic => do
  match ← Auto.intervalBoundRationalCoreTyped 10 with
  | .error (.inconclusive _) => pure ()
  | .error failure =>
      throwError "Rational rejection had the wrong typed category: {repr failure}"
  | .ok _ =>
      throwError "known-false Rational bound unexpectedly succeeded"

elab "expect_rational_bound_unsupported" : tactic => do
  match ← Auto.intervalBoundRationalCoreTyped 10 with
  | .error (.unsupported _ _) => pure ()
  | .error failure =>
      throwError "unsupported Rational expression had the wrong category: \
        {repr failure}"
  | .ok _ =>
      throwError "unsupported Rational expression unexpectedly succeeded"

/--
info: LeanCert recognized: closed certificate check

Selected strategy:
  closed Boolean certificate verification

Certificate verification:
  requested native → used native

Suggested proof:
  by
    leancert
-/
#guard_msgs in
example : LeanCert.Validity.checkUpperBound checkerExpr checkerInterval 1 {} = true := by
  leancert?

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (-1 : ℝ) ≤ x := by
  expect_rational_lower_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x < (2 : ℝ) := by
  expect_rational_strict_upper_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (-1 : ℝ) < x := by
  expect_rational_strict_lower_bound

example (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ (-1 : ℝ)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ (-1 : ℝ) := by
  expect_rational_bound_inconclusive
  exact h

example (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    (if x ≤ 0 then 0 else 1 : ℝ) ≤ (2 : ℝ)) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (if x ≤ 0 then 0 else 1 : ℝ) ≤ (2 : ℝ) := by
  expect_rational_bound_unsupported
  exact h

#guard_msgs in
example : (3 : ℝ) / 2 < 2 := by
  leancert (budget := 1)

-- Typed failures remain visible through normalized bound/root transport.
example : (3 : ℝ) / 2 < 2 := by
  expect_typed_adapter_failure
  norm_num

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ 1 := by
  expect_typed_adapter_failure
  intro x hx
  exact hx.2

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x = 0 := by
  expect_typed_adapter_failure
  exact ⟨0, by simp⟩

example : True := by
  expect_terminal_outcome_stops
  trivial

example : True := by
  expect_exact_route_exception_terminal
  trivial

example : Real.log 2 < Real.exp 1 := by
  expect_rational_point_report

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by
  expect_kernel_bound_report

/--
info: LeanCert recognized: closed numerical comparison

Selected strategy:
  exact normalization

Certificate verification:
  not required by this proof strategy

Suggested proof:
  by
    leancert

Advanced control:
  by
    norm_num
-/
#guard_msgs in
example : (1 : ℝ) < 2 := by
  leancert?

/--
info: LeanCert recognized: closed numerical comparison

Selected strategy:
  direct point enclosure (Taylor depth 10)
  Taylor depth: 10
  precision: -80

Numerical computation:
  Dyadic interval evaluation

Certificate verification:
  requested native → used native
Checker: LeanCert.Validity.checkStrictUpperBoundDyadicChecked
Verifier: LeanCert.Validity.verify_strict_upper_bound_dyadic_checked

Suggested proof:
  by
    leancert

Advanced control:
  by
    interval_auto 10
-/
#guard_msgs in
example : Real.log 2 < 7 / 10 := by
  leancert?

/--
info: LeanCert recognized: univariate interval bound

Selected strategy:
  direct interval enclosure (Taylor depth 10)
  Taylor depth: 10
  precision: -80

Numerical computation:
  Dyadic interval evaluation

Certificate verification:
  requested native → used native
Checker: LeanCert.Validity.checkUpperBoundDyadicChecked
Verifier: LeanCert.Validity.verify_upper_bound_dyadic_checked

Suggested proof:
  by
    leancert

Advanced control:
  by
    certify_bound 10
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x * Real.cos x ≤ 3 := by
  leancert?

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ 1 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x + y ≤ (2 : ℚ) := by
  leancert

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  leancert

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ 2 = x ^ 2 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + 1 ≠ 0 := by
  leancert

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≥ m := by
  leancert

example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ M := by
  leancert

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x * x + y * y ≥ m := by
  leancert

example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x + y ≤ M := by
  leancert

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x ≤ y := by
  leancert

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    2 * y + 1 ≤ 2 * x + 1 := by
  leancert

example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  leancert

-- The direct enclosure is too wide; the third isolated strategy uses subdivision.
/--
info: LeanCert recognized: univariate interval bound

Selected strategy:
  recursive interval subdivision
  Taylor depth 10; maximum recursive depth 8

Numerical computation:
  Rational interval evaluation

Certificate verification:
  requested kernel → used kernel (14 checks)
Checker: LeanCert.Validity.checkUpperBound
Verifier: LeanCert.Validity.verify_upper_bound_Icc_core

Subdivision:
  Taylor depth: 10
  Configured maximum depth: 8
  Deepest depth used: 5
  Boxes examined: 27
  Certified leaves: 14

Suggested proof:
  by
    leancert (subdivisions := 8) (trust := kernel)

Advanced control:
  by
    interval_bound_subdiv 10 8 (trust := kernel)
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  leancert? (subdivisions := 8) (trust := kernel)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (-27 / 100 : ℚ) ≤ x * x - x := by
  leancert (subdivisions := 8)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) < (27 / 100 : ℚ) := by
  leancert (subdivisions := 8)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (-27 / 100 : ℚ) < x * x - x := by
  leancert (subdivisions := 8)

/-! ## Typed finite sums and integrals -/

syntax (name := expectTypedFinSumRollback)
  "expect_typed_finsum_rollback" : tactic

@[tactic expectTypedFinSumRollback]
unsafe def elabExpectTypedFinSumRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let environmentBefore := (← getEnv).constants.toList.length
  let messagesBefore := (← Core.getMessageLog).toList.length
  match ← finSumBoundCoreTyped (-53) 10 with
  | .error (.rejected checker (some _)) =>
      unless checker == ``LeanCert.Engine.checkFinSumUpperBoundFull do
        throwError "finite-sum rejection retained the wrong checker"
      unless (← getMainGoal) == goal && !(← goal.isAssigned) do
        throwError "finite-sum rejection retained a partial proof"
      unless ← isDefEq (← goal.getType) goalType do
        throwError "finite-sum rejection changed the goal type"
      unless (← getEnv).constants.toList.length == environmentBefore do
        throwError "finite-sum rejection leaked an environment declaration"
      unless (← Core.getMessageLog).toList.length == messagesBefore do
        throwError "finite-sum rejection leaked a message"
  | .error failure =>
      throwError "finite-sum rejection had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "false finite-sum bound unexpectedly succeeded"

syntax (name := expectFinSumRouterReport)
  "expect_finsum_router_report" : tactic

@[tactic expectFinSumRouterReport]
unsafe def elabExpectFinSumRouterReport : Tactic := fun _ => do
  let result ← runLeanCert {} .compact
  let some statistics := result.execution.finiteSum
    | throwError "front-door finite-sum route returned no structured statistics"
  unless statistics.path == .reifiedRange && statistics.termCount == 3 &&
      statistics.precision == -53 && !statistics.rewrittenFin do
    throwError "front-door finite-sum route retained incorrect execution facts"
  unless result.execution.checker ==
      some ``LeanCert.Engine.checkFinSumUpperBoundFull &&
      result.execution.verifier ==
      some ``LeanCert.Engine.verify_finsum_upper_full_checked do
    throwError "front-door finite-sum route lost checker provenance"
  unless result.execution.enclosure.isSome do
    throwError "front-door finite-sum route lost its retained enclosure"

syntax (name := expectIntegralPartitionReport)
  "expect_integral_partition_report" : tactic

@[tactic expectIntegralPartitionReport]
unsafe def elabExpectIntegralPartitionReport : Tactic := fun _ => do
  let result ← runLeanCert {} .compact
  let some statistics := result.execution.integralPartitions
    | throwError "partition integral returned no structured search statistics"
  unless statistics.startPartitions == 16 &&
      statistics.chosenPartitions ≤ statistics.maximumPartitions &&
      statistics.attempts > 0 do
    throwError "partition integral retained invalid search statistics"
  unless result.execution.checker ==
      some ``LeanCert.Validity.Integration.checkIntegralPartitionUpperBound &&
      result.execution.verifier ==
      some ``LeanCert.Validity.Integration.integral_partition_upper_of_check do
    throwError "partition integral certified the search instead of its fixed candidate"
  unless result.execution.enclosure.isSome do
    throwError "partition integral lost its selected enclosure"

syntax (name := expectIntegralConjunctionRollback)
  "expect_integral_conjunction_rollback" : tactic

@[tactic expectIntegralConjunctionRollback]
unsafe def elabExpectIntegralConjunctionRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let environmentBefore := (← getEnv).constants.toList.length
  let messagesBefore := (← Core.getMessageLog).toList.length
  match ← integralExactCoreTyped with
  | .error (.unsupported _) =>
      unless (← getMainGoal) == goal && !(← goal.isAssigned) do
        throwError "failed exact-integral conjunction retained its first child"
      unless ← isDefEq (← goal.getType) goalType do
        throwError "failed exact-integral conjunction changed the goal type"
      unless (← getEnv).constants.toList.length == environmentBefore do
        throwError "failed exact-integral conjunction leaked an environment declaration"
      unless (← Core.getMessageLog).toList.length == messagesBefore do
        throwError "failed exact-integral conjunction leaked a message"
  | .error failure =>
      throwError "exact-integral conjunction had wrong failure: {repr failure}"
  | .ok _ =>
      throwError "non-polynomial exact-integral conjunction unexpectedly succeeded"

syntax (name := expectTypedFinRewriteReport)
  "expect_typed_fin_rewrite_report" : tactic

@[tactic expectTypedFinRewriteReport]
unsafe def elabExpectTypedFinRewriteReport : Tactic := fun _ => do
  match ← finSumBoundCoreTyped (-53) 10 with
  | .ok outcome =>
      unless outcome.rewrittenFin && outcome.path == .reifiedExplicit &&
          outcome.termCount == 3 do
        throwError "typed finite-sum route lost its Fin rewrite provenance"
  | .error failure =>
      throwError "typed Fin sum unexpectedly failed: {repr failure}"

syntax (name := expectTypedFinSumDomainRollback)
  "expect_typed_finsum_domain_rollback" : tactic

@[tactic expectTypedFinSumDomainRollback]
unsafe def elabExpectTypedFinSumDomainRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match ← finSumBoundCoreTyped (-53) 10 with
  | .error (.domainObstruction (some 0) _) =>
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "finite-sum domain obstruction changed the caller state"
  | .error failure =>
      throwError "finite-sum domain obstruction had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "division-by-zero finite sum unexpectedly succeeded"

syntax (name := expectTypedFinSumUnsupported)
  "expect_typed_finsum_unsupported" : tactic

@[tactic expectTypedFinSumUnsupported]
unsafe def elabExpectTypedFinSumUnsupported : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match ← finSumBoundCoreTyped (-53) 10 with
  | .error (.unsupported _) =>
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "unsupported finite sum changed the caller state"
  | .error failure =>
      throwError "unsupported finite sum had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "unsupported finite sum unexpectedly succeeded"

syntax (name := expectTypedFinSumWitnessUnsupported)
  "expect_typed_finsum_witness_unsupported" : tactic

@[tactic expectTypedFinSumWitnessUnsupported]
unsafe def elabExpectTypedFinSumWitnessUnsupported : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let badEvaluator ← `(term| (0 : Nat))
  let irrelevantProof ← `(term| by simp)
  match ← finSumWitnessBoundCoreTyped badEvaluator irrelevantProof (-53) with
  | .error (.unsupported detail) =>
      unless detail.contains "malformed witness evaluator" do
        throwError "malformed witness evaluator lost its intentional diagnostic"
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "malformed witness input changed the caller state"
  | .error failure =>
      throwError "malformed witness input had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "malformed witness evaluator unexpectedly succeeded"
  let evaluator ← `(term|
    fun k (_cfg : LeanCert.Engine.DyadicConfig) =>
      LeanCert.Core.IntervalDyadic.singleton
        (LeanCert.Core.Dyadic.ofInt (Int.ofNat k)))
  let badProof ← `(term| (0 : Nat))
  match ← finSumWitnessBoundCoreTyped evaluator badProof (-53) with
  | .error (.unsupported detail) =>
      unless detail.contains "malformed witness proof" do
        throwError "malformed witness proof lost its intentional diagnostic"
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "malformed witness proof changed the caller state"
  | .error failure =>
      throwError "malformed witness proof had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "malformed witness proof unexpectedly succeeded"

syntax (name := expectIntegralExhaustionRollback)
  "expect_integral_exhaustion_rollback" : tactic

@[tactic expectIntegralExhaustionRollback]
unsafe def elabExpectIntegralExhaustionRollback : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let messagesBefore := (← Core.getMessageLog).toList.length
  match ← integralSearchCoreTyped 16 64 with
  | .error (.exhausted 16 64 (some _) (some _) attempts) =>
      unless attempts == 3 do
        throwError "partition exhaustion retained the wrong attempt count"
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "partition exhaustion changed the caller state"
      unless (← Core.getMessageLog).toList.length == messagesBefore do
        throwError "partition exhaustion leaked a message"
  | .error failure =>
      throwError "partition exhaustion had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "false integral bound unexpectedly succeeded"

syntax (name := expectTypedIntegralUnsupported)
  "expect_typed_integral_unsupported" : tactic

@[tactic expectTypedIntegralUnsupported]
unsafe def elabExpectTypedIntegralUnsupported : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match ← integralSearchCoreTyped 16 64 with
  | .error (.unsupported _) =>
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "unsupported integral changed the caller state"
  | .error failure =>
      throwError "unsupported integral had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "unsupported integral unexpectedly succeeded"

syntax (name := expectTypedIntegralDomainObstruction)
  "expect_typed_integral_domain_obstruction" : tactic

@[tactic expectTypedIntegralDomainObstruction]
unsafe def elabExpectTypedIntegralDomainObstruction : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match ← integralSearchCoreTyped 16 64 with
  | .error (.domainObstruction _) =>
      unless (← getMainGoal) == goal && !(← goal.isAssigned) &&
          (← isDefEq (← goal.getType) goalType) do
        throwError "domain-obstructed integral changed the caller state"
  | .error failure =>
      throwError "integral domain obstruction had wrong classification: {repr failure}"
  | .ok _ =>
      throwError "domain-obstructed integral unexpectedly succeeded"

syntax (name := expectReversedIntegralReport)
  "expect_reversed_integral_report" : tactic

@[tactic expectReversedIntegralReport]
unsafe def elabExpectReversedIntegralReport : Tactic := fun _ => do
  match ← integralSearchCoreTyped 16 512 with
  | .ok #[outcome] =>
      let some enclosure := outcome.enclosure
        | throwError "reversed integral report lost its retained enclosure"
      unless enclosure.hi < 0 do
        throwError "reversed integral telemetry describes the swapped integral: {repr enclosure}"
  | .ok outcomes =>
      throwError "reversed integral produced {outcomes.size} outcomes instead of one"
  | .error failure =>
      throwError "reversed integral unexpectedly failed: {repr failure}"

example (h : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 1) :
    ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 1 := by
  expect_typed_finsum_rollback
  fail_if_success finsum_bound
  exact h

example : ∑ k ∈ Finset.Icc (1 : Nat) 3, Real.exp (-(k : ℝ)) ≤ 1 := by
  expect_finsum_router_report

example : ∑ i : Fin 3, Real.exp (-(i : ℝ)) ≤ 2 := by
  expect_typed_fin_rewrite_report

example (h : ∑ k ∈ Finset.Icc (0 : Nat) 1, (1 : ℝ) / k ≤ 2) :
    ∑ k ∈ Finset.Icc (0 : Nat) 1, (1 : ℝ) / k ≤ 2 := by
  expect_typed_finsum_domain_rollback
  exact h

example (f : Nat → ℝ) (h : ∑ k ∈ Finset.Icc (0 : Nat) 1, f k ≤ 0) :
    ∑ k ∈ Finset.Icc (0 : Nat) 1, f k ≤ 0 := by
  expect_typed_finsum_unsupported
  exact h

example (c : ℝ) (h : ∑ k ∈ Finset.Icc (0 : Nat) 1, (k : ℝ) ≤ c) :
    ∑ k ∈ Finset.Icc (0 : Nat) 1, (k : ℝ) ≤ c := by
  expect_typed_finsum_unsupported
  exact h

example (h : ∑ k ∈ Finset.Icc (0 : Nat) 1, (k : ℝ) ≤ 2) :
    ∑ k ∈ Finset.Icc (0 : Nat) 1, (k : ℝ) ≤ 2 := by
  expect_typed_finsum_witness_unsupported
  exact h

example : (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  expect_integral_partition_report

example (f : ℝ → ℝ) (h : (∫ x in (0 : ℝ)..1, f x) ≤ 0) :
    (∫ x in (0 : ℝ)..1, f x) ≤ 0 := by
  expect_typed_integral_unsupported
  exact h

example (h : (∫ x in (-1 : ℝ)..1, Real.log x) ≤ 0) :
    (∫ x in (-1 : ℝ)..1, Real.log x) ≤ 0 := by
  expect_typed_integral_domain_obstruction
  exact h

example : (∫ x in (1 : ℝ)..0, Real.exp x) ≤ 0 := by
  expect_reversed_integral_report

example (h : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 ∧
    (∫ x in (0 : ℝ)..1, Real.exp x) = 1) :
    (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 ∧
    (∫ x in (0 : ℝ)..1, Real.exp x) = 1 := by
  expect_integral_conjunction_rollback
  exact h

example (h : (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 1) :
    (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 1 := by
  expect_integral_exhaustion_rollback
  exact h

-- Failed portfolios restore the original goal and its local context.
example (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 ≤ 0) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 ≤ 0 := by
  fail_if_success leancert (budget := 2)
  exact h

/--
error: LeanCert recognized a conjunction, but child 2 of 2 failed: closed numerical comparison

LeanCert recognized: closed numerical comparison

Attempts:
  1. exact normalization
     solver left 1 proof obligation(s):
False
  2. direct point enclosure (Taylor depth 10)
     The candidate certificate was rejected by its checker.
Try increasing `taylorDepth`, enabling subdivision, or using the corresponding dedicated tactic for finer control.
  3. direct point enclosure (Taylor depth 20)
     The candidate certificate was rejected by its checker.
Try increasing `taylorDepth`, enabling subdivision, or using the corresponding dedicated tactic for finer control.

Budget: spent 3 of 6

Next steps:
• Check whether the requested statement is true.
• Increase `(taylorDepth := ...)`, `(subdivisions := ...)`, or `(maxIterations := ...)` when the corresponding attempt was inconclusive.
• Use `interval_refute` to search for a certified counterexample.
-/
#guard_msgs in
example : ((1 : ℝ) < 2) ∧ ((2 : ℝ) < 1) := by
  leancert?

-- Question mode proves the goal and reports the winning dedicated tactic.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  leancert?

/-! ## Suggested-proof syntax

These are deliberately literal rather than generated-string tests.  Every
primary or dedicated shape that the router may recommend must continue to
elaborate verbatim.
-/

-- Primary recipe, including non-default parameters and requested trust.
example : (3 : ℝ) / 2 < 2 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  leancert (subdivisions := 8) (taylorDepth := 10) (maxIterations := 64)

example : Real.log 2 < 7 / 10 := by
  leancert (trust := kernel)

-- Dedicated recipes retained for advanced use.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound 20

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  interval_bound_subdiv 10 8 (trust := kernel)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  interval_bound_subdiv 10 8 (trust := auto)

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  interval_roots (trust := auto)

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 = 2 := by
  interval_unique_root (trust := kernel)

example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound (trust := native)

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  integral_exact
