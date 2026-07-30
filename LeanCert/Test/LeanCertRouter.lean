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

private def adapterTestPlan : SolverPlan := {
  intent := .pointInequality
  solver := `typedAdapterTest
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
    solve := throwError "legacy Unit adapter ran"
    solveReported := some (throwError "legacy reported adapter ran")
    solveReportedResult := some <| pure <|
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

-- Typed results take precedence over both reported and opaque compatibility
-- adapters, including through normalized bound/root transport.
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
  deepest recursive depth used: 5
  certified leaves: 14

Numerical computation:
  Rational interval evaluation

Certificate verification:
  requested kernel → used kernel (14 checks)
Checker: LeanCert.Validity.checkUpperBound
Verifier: LeanCert.Validity.verify_upper_bound_Icc_core

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

/-! ## Suggested-proof and compatibility syntax

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

-- Dedicated recipes retained for advanced use and legacy compatibility.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound 20

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  interval_bound_subdiv 10 8 (trust := kernel)

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  interval_roots (trust := auto)

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 = 2 := by
  interval_unique_root (trust := kernel)

example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound (trust := native)

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  integral_exact
