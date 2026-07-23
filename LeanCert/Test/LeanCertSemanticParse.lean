/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Parse-once semantic goal tests
-/

open MeasureTheory
open Lean Meta Elab Tactic
open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Bridge

syntax (name := expectCertifiedRefutation) "expect_certified_refutation" : tactic
syntax (name := expectUnsupportedExpression) "expect_unsupported_expression" : tactic
syntax (name := expectUnsupportedCarrier) "expect_unsupported_carrier" : tactic
syntax (name := expectSanitizedCheckerFailure) "expect_sanitized_checker_failure" : tactic

@[tactic expectCertifiedRefutation]
unsafe def evalExpectCertifiedRefutation : Tactic := fun _ => do
  let saved ← saveState
  try
    discard <| LeanCert.Tactic.runLeanCert {}
    saved.restore
    throwError "expected LeanCert to reject the false theorem"
  catch exception =>
    saved.restore
    let detail ← exception.toMessageData.toString
    unless detail.contains "Certified counterexample" do
      throwError "expected a certified-counterexample diagnostic, got:\n{detail}"

private unsafe def expectLeanCertFailure
    (required forbidden : Array String) : TacticM Unit := do
  let saved ← saveState
  try
    discard <| LeanCert.Tactic.runLeanCert {}
    saved.restore
    throwError "expected LeanCert to reject the theorem"
  catch exception =>
    saved.restore
    let detail ← exception.toMessageData.toString
    for fragment in required do
      unless detail.contains fragment do
        throwError "expected diagnostic fragment {fragment}, got:\n{detail}"
    for fragment in forbidden do
      if detail.contains fragment then
        throwError "internal diagnostic fragment {fragment} leaked:\n{detail}"

@[tactic expectUnsupportedExpression]
unsafe def evalExpectUnsupportedExpression : Tactic := fun _ =>
  expectLeanCertFailure #["Unsupported expression"] #["Core.Expr", "Head symbol"]

@[tactic expectUnsupportedCarrier]
unsafe def evalExpectUnsupportedCarrier : Tactic := fun _ =>
  expectLeanCertFailure #["carrier type is not supported"] #["internal preparation failure"]

@[tactic expectSanitizedCheckerFailure]
unsafe def evalExpectSanitizedCheckerFailure : Tactic := fun _ =>
  expectLeanCertFailure #["not accepted"] #["checkNoRoot", "native_decide"]

elab "expect_strict_integral_semantic" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok (.integral spec) =>
      unless spec.comparison == .lt do
        throwError "expected strict integral comparison"
      unless spec.integral == spec.lhs do
        throwError "expected the integral on the left"
  | _ => throwError "expected semantic integral"
  evalTactic (← `(tactic| leancert))

elab "expect_lower_integral_semantic" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok (.integral spec) =>
      unless spec.comparison == .le do
        throwError "expected non-strict integral comparison"
      unless spec.integral == spec.rhs do
        throwError "expected the integral on the right"
  | _ => throwError "expected semantic integral"
  evalTactic (← `(tactic| leancert))

elab "expect_sum_equality_semantic" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok (.finiteSum spec) =>
      unless spec.comparison == .eq do
        throwError "expected finite-sum equality"
  | _ => throwError "expected semantic finite sum"
  evalTactic (← `(tactic| finsum_expand; norm_num))

elab "expect_mixed_conjunction_semantic" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok (.allOf _ children) =>
      unless children.size == 2 do
        throwError "expected two semantic children"
      match children[0]!, children[1]! with
      | .integral _, .bound _ => pure ()
      | _, _ => throwError "unexpected semantic children"
  | _ => throwError "expected semantic conjunction"
  evalTactic (← `(tactic| constructor <;> leancert))

elab "expect_disjunction_rejected" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .error failure =>
      unless failure.detail.contains "disjunction" do
        throwError "unexpected disjunction failure: {failure.detail}"
  | .ok _ => throwError "disjunction should not be classified"
  evalTactic (← `(tactic| exact Or.inl True.intro))

elab "expect_empty_prepared_domain" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok semantic =>
      match ← prepareGoal semantic with
      | .ok prepared =>
          unless prepared.domains.any (fun domain => domain.isProvablyEmpty) do
            throwError "expected a proof-bearing empty domain"
      | .error failure => throwError "preparation failed: {failure.detail}"
  | .error failure => throwError "parsing failed: {failure.detail}"
  evalTactic (← `(tactic| leancert))

elab "expect_singleton_prepared_domain" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok semantic =>
      match ← prepareGoal semantic with
      | .ok prepared =>
          unless prepared.domains.any (fun domain => match domain with
              | .singleton .. => true
              | _ => false) do
            throwError "expected a proof-bearing singleton domain"
      | .error failure => throwError "preparation failed: {failure.detail}"
  | .error failure => throwError "parsing failed: {failure.detail}"
  evalTactic (← `(tactic| leancert))

elab "expect_proof_carrying_reification" : tactic => do
  let goalType ← (← getMainGoal).getType
  match ← parseGoal goalType with
  | .ok (.bound spec) =>
      unless spec.boundVars.all (·.binderId.isSome) do
        throwError "semantic parser discarded binder identity"
      let reflected ← reifyFunction spec.lhs
      if reflected.evalEq.hasMVar then
        throwError "semantic reification equality leaked metavariables"
      discard <| inferType reflected.evalEq
      let capabilities ← deriveCapabilities reflected
      unless capabilities.supportedCore.isSome do
        throwError "expected supported-core capability"
  | _ => throwError "expected semantic bound"
  evalTactic (← `(tactic| leancert))

example : (∫ x in (0 : ℝ)..1, x ^ 2) < 1 / 2 := by
  expect_strict_integral_semantic

example : (1 / 4 : ℝ) ≤ (∫ x in (0 : ℝ)..1, x ^ 2) := by
  expect_lower_integral_semantic

example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) = 15 := by
  expect_sum_equality_semantic

example :
    (∫ x in (0 : ℝ)..1, x ^ 2) ≤ 1 / 2 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ 1) := by
  expect_mixed_conjunction_semantic

example : True ∨ ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ 1 := by
  expect_disjunction_rejected

example : ∀ x ∈ Set.Icc (1 : ℝ) 0, Real.exp x ≤ -100 := by
  expect_empty_prepared_domain

example : ∀ x ∈ Set.Icc (1 : ℝ) 1, (x - 1) ^ 2 ≤ 0 := by
  expect_singleton_prepared_domain

private def wrappedCubic (x : ℝ) : ℝ := x * (x * x) + 1

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, wrappedCubic x ≤ 2 := by
  expect_proof_carrying_reification

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ x + 1 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x ∧ x ≤ 1 := by
  leancert

-- Implication-style interval hypotheses normalize to the same semantic domain.
example : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → x ^ 2 ≤ 1 := by
  leancert

-- Parsing remains context-correct when conjunction splitting creates siblings.
example :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x ^ 2) := by
  leancert

-- Endpoint roots do not require a strict sign change certificate.
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 = 0 := by
  leancert

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, 0 = x - 1 := by
  leancert

example : ∃ x : ℝ, x ^ 2 = 2 ∧ x ∈ Set.Icc (1 : ℝ) 2 := by
  leancert

example : ∃ x : ℝ, 0 = x ^ 2 - 2 ∧ x ∈ Set.Icc (1 : ℝ) 2 := by
  leancert

example : ∃ x ∈ Set.Icc (0 : ℝ) 2, (x - 1) ^ 2 = 0 := by
  leancert

example : ∃! x, x ∈ Set.Icc (0 : ℝ) 1 ∧ x = 0 := by
  leancert

-- Empty existential domains are rejected semantically before root search.
example (h : ∃ x ∈ Set.Icc (1 : ℝ) 0, x = 0) :
    ∃ x ∈ Set.Icc (1 : ℝ) 0, x = 0 := by
  fail_if_success leancert
  exact h

opaque unsupportedSemanticProbe : ℝ → ℝ

set_option linter.unusedTactic false in
example (h : ∃ x ∈ Set.Icc (0 : ℝ) 1, unsupportedSemanticProbe x = 0) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, unsupportedSemanticProbe x = 0 := by
  expect_unsupported_expression
  exact h

set_option linter.unusedTactic false in
example (h : ∀ x ∈ Set.Icc (0 : ℚ) 1, x * x ≤ 1) :
    ∀ x ∈ Set.Icc (0 : ℚ) 1, x * x ≤ 1 := by
  expect_unsupported_carrier
  exact h

set_option linter.unusedTactic false in
example (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ≠ 0) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ≠ 0 := by
  expect_sanitized_checker_failure
  exact h

-- Existence uses compactness and continuity; no rational optimizer is needed.
example : ∃ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (1 : ℝ) 2,
    (x ^ 2 - 2) ^ 2 ≤ (y ^ 2 - 2) ^ 2 := by
  leancert

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (1 : ℝ) 2,
    -((y ^ 2 - 2) ^ 2) ≤ -((x ^ 2 - 2) ^ 2) := by
  leancert

example : ∃ x : ℝ,
    (∀ y ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ y ^ 2) ∧
      x ∈ Set.Icc (0 : ℝ) 1 := by
  leancert

-- Multivariate verifier output is transported back through ordinary syntax.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x * y ≤ 1 := by
  leancert

-- A zero numerical budget still permits exact normalization.
example : (1 : ℝ) ≤ 2 := by
  leancert (budget := 0)

-- Failed proof search can still return checked evidence that the statement is false.
set_option linter.unusedTactic false in
example (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2 := by
  expect_certified_refutation
  exact h
