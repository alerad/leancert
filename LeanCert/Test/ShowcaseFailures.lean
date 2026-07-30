/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Executable failure showcase

These tests pin searchable public diagnostics without snapshotting incidental
internal exception text.
-/

open Lean Meta Elab Tactic

private unsafe def expectFailureContaining (fragments : Array String) :
    TacticM Unit := do
  let saved ← saveState
  try
    discard <| LeanCert.Tactic.runLeanCert {} .explain
    saved.restore
    throwError "expected `leancert?` to fail"
  catch exception =>
    saved.restore
    let message ← exception.toMessageData.toString
    for fragment in fragments do
      unless message.contains fragment do
        throwError "expected diagnostic fragment {fragment}, got:\n{message}"

syntax (name := expectUnsupportedShowcase) "expect_unsupported_showcase" : tactic
syntax (name := expectDomainObstructionShowcase) "expect_domain_obstruction_showcase" : tactic
syntax (name := expectResolutionAdviceShowcase) "expect_resolution_advice_showcase" : tactic
syntax (name := expectCertifiedCounterexampleShowcase)
  "expect_certified_counterexample_showcase" : tactic
syntax (name := expectAutoNativeShowcase) "expect_auto_native_showcase" : tactic

@[tactic expectUnsupportedShowcase]
unsafe def evalExpectUnsupportedShowcase : Tactic := fun _ =>
  expectFailureContaining #["Unsupported expression:", "Head symbol:", "Suggestions:"]

@[tactic expectDomainObstructionShowcase]
unsafe def evalExpectDomainObstructionShowcase : Tactic := fun _ =>
  expectFailureContaining #[
    "Domain obstruction:",
    "checked evaluator rejected a partial operation",
    "Increasing numerical precision does not repair an invalid domain"
  ]

@[tactic expectResolutionAdviceShowcase]
unsafe def evalExpectResolutionAdviceShowcase : Tactic := fun _ =>
  expectFailureContaining #[
    "Subdivision reached its configured depth",
    "Increase `(taylorDepth := ...)`, `(subdivisions := ...)`"
  ]

@[tactic expectCertifiedCounterexampleShowcase]
unsafe def evalExpectCertifiedCounterexampleShowcase : Tactic := fun _ => do
  let saved ← saveState
  try
    evalTactic (← `(tactic| interval_refute))
    saved.restore
    throwError "expected a certified counterexample"
  catch exception =>
    saved.restore
    let message ← exception.toMessageData.toString
    unless message.contains "Counter-example FOUND" do
      throwError "expected a certified counterexample, got:\n{message}"

@[tactic expectAutoNativeShowcase]
unsafe def evalExpectAutoNativeShowcase : Tactic := fun _ => do
  let report ← LeanCert.Tactic.withTrustMode (some .auto) do
    LeanCert.Tactic.runLeanCert { trust := some .auto } .explain
  unless report.execution.verificationUsage.nativeChecks > 0 do
    throwError "expected auto verification to retain a native check"
  unless report.execution.verificationUsage.autoGateReasons.any
      (·.contains "exceeds autoMaxSumTerms") do
    throwError "expected the finite-sum auto-gate reason"

opaque unsupportedShowcase : ℝ → ℝ

set_option linter.unusedTactic false in
example (h : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3) :
    ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  expect_certified_counterexample_showcase
  exact h

set_option linter.unusedTactic false in
example (h : ∃ x ∈ Set.Icc (0 : ℝ) 1, unsupportedShowcase x = 0) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, unsupportedShowcase x = 0 := by
  expect_unsupported_showcase
  exact h

set_option linter.unusedTactic false in
example (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Real.log x ≤ 1) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, Real.log x ≤ 1 := by
  expect_domain_obstruction_showcase
  exact h

set_option linter.unusedTactic false in
example (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (1 / 4 : ℚ)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (1 / 4 : ℚ) := by
  expect_resolution_advice_showcase
  exact h

private def largeSumBody : LeanCert.Core.Expr := .var 0

example : LeanCert.Engine.checkFinSumUpperBoundFull
    largeSumBody 1 5000 12502500 = true := by
  expect_auto_native_showcase
