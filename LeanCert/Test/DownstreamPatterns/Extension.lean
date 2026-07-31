/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Extension

/-!
# Downstream enclosure-extension pattern

This module intentionally imports only the extension umbrella.  It models a downstream
package registering a function without editing LeanCert's expression AST or router.
-/

namespace LeanCert.Test.DownstreamPatterns.Extension

open Lean Elab Command
open LeanCert.Core LeanCert.Tactic.Extension

def shifted (x : ℝ) : ℝ := x + 1

def shiftedCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  .ok <| IntervalRat.add request.input (IntervalRat.singleton 1)

def checkShifted (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (output = IntervalRat.add request.input (IntervalRat.singleton 1))

@[leancert_enclosure shiftedCandidate, priority := 1200]
theorem shifted_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  have hout : output = IntervalRat.add request.input (IntervalRat.singleton 1) := by
    exact of_decide_eq_true hcheck
  rw [hout]
  simpa [shifted] using IntervalRat.mem_add hx (IntervalRat.mem_singleton 1)

@[leancert_enclosure shiftedCandidate, priority := 100]
theorem shifted_mem_fallback
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  exact shifted_mem hx hcheck

/-- A deliberately non-reifiable downstream function used to exercise the
registered execution path rather than LeanCert's built-in expression bridge. -/
noncomputable def positiveBranch (x : ℝ) : ℝ := if x ≤ 0 then 0 else x

def positiveBranchCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 0 < request.input.lo then .ok request.input
  else .error <| .domainObstruction "input interval is not strictly positive"

def checkPositiveBranch (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (0 < request.input.lo) && decide (output = request.input)

/-- A higher-priority bad candidate checks the fallback path to the next
registered rule without weakening the soundness boundary. -/
def rejectedPositiveBranchCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat := .ok request.input

def rejectPositiveBranch (_request : UnaryEnclosureRequest) (_output : IntervalRat) : Bool :=
  false

@[leancert_enclosure rejectedPositiveBranchCandidate, priority := 1300]
theorem rejected_positiveBranch_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (_hx : x ∈ request.input)
    (hcheck : rejectPositiveBranch request output = true) :
    positiveBranch x ∈ output := by
  simp [rejectPositiveBranch] at hcheck

@[leancert_enclosure positiveBranchCandidate, priority := 1200]
theorem positiveBranch_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkPositiveBranch request output = true) :
    positiveBranch x ∈ output := by
  simp only [checkPositiveBranch, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hpositive, rfl⟩
  have hxpositive : 0 < x := by
    exact lt_of_lt_of_le (by exact_mod_cast hpositive) hx.1
  simpa [positiveBranch, not_le.mpr hxpositive] using hx

/-- A deliberately width-sensitive rule used to demonstrate that candidate
rejection on a broad interval can be repaired by checked subdivision. -/
noncomputable def narrowIdentity (x : ℝ) : ℝ := x

def narrowIdentityCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat := .ok request.input

def checkNarrowIdentity (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (request.input.hi - request.input.lo ≤ 1) && decide (output = request.input)

@[leancert_enclosure narrowIdentityCandidate]
theorem narrowIdentity_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkNarrowIdentity request output = true) :
    narrowIdentity x ∈ output := by
  simp only [checkNarrowIdentity, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨_, rfl⟩
  simpa [narrowIdentity] using hx

/- A sound but deliberately widened enclosure. It exercises correlation loss,
subdivision, and domain propagation through a registered atom. -/
noncomputable def fatPositive (x : ℝ) : ℝ := if x ≤ 0 then 0 else x

def fatPositiveOutput (input : IntervalRat) : IntervalRat where
  lo := input.lo - 1 / 10
  hi := input.hi + 1 / 10
  le := by linarith [input.le]

def fatPositiveCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 0 < request.input.lo then .ok (fatPositiveOutput request.input)
  else .error <| .domainObstruction "input interval is not strictly positive"

def checkFatPositive (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (0 < request.input.lo) && decide (output = fatPositiveOutput request.input)

@[leancert_enclosure fatPositiveCandidate]
theorem fatPositive_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkFatPositive request output = true) :
    fatPositive x ∈ output := by
  simp only [checkFatPositive, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hpositive, rfl⟩
  have hxpositive : 0 < x := lt_of_lt_of_le (by exact_mod_cast hpositive) hx.1
  simp only [fatPositive, if_neg (not_le.mpr hxpositive), IntervalRat.mem_def,
    fatPositiveOutput]
  simp only [IntervalRat.mem_def] at hx
  constructor <;> push_cast <;> linarith [hx.1, hx.2]

run_meta do
  let env ← getEnv
  let rules := getUnaryEnclosureRules env ``shifted
  unless rules.size == 2 do
    throwError "expected two downstream shifted rules, found {rules.size}"
  unless rules[0]!.theoremName == ``shifted_mem && rules[0]!.rulePriority == 1200 do
    throwError "highest-priority downstream rule was not ordered first"
  for moduleName in env.header.moduleNames do
    if (`LeanCert.Tactic.LeanCert.Router).isPrefixOf moduleName then
      throwError "extension-only import leaked router module {moduleName}"

end LeanCert.Test.DownstreamPatterns.Extension
