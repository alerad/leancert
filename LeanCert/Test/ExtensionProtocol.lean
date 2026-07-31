/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Test.DownstreamPatterns.Extension

/-! # Typed enclosure-extension registry tests -/

namespace LeanCert.Test.ExtensionProtocol

open Lean Elab Command
open LeanCert.Core LeanCert.Tactic.Extension
open LeanCert.Test.DownstreamPatterns.Extension

run_meta do
  let rules := getUnaryEnclosureRules (← getEnv) ``shifted
  unless rules.size == 2 do
    throwError "persistent enclosure rules did not survive import"
  unless rules[0]!.candidateName == ``shiftedCandidate &&
      rules[0]!.checkerName == ``checkShifted &&
      rules[0]!.theoremName == ``shifted_mem do
    throwError "registered enclosure metadata did not match its declarations"

#print_leancert_rules shifted

def identity (x : ℝ) : ℝ := x

def identityCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  .ok request.input

def checkIdentity (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (output = request.input)

def wrongCandidate (_request : UnaryEnclosureRequest) : Nat := 0

/-- error: invalid @[leancert_enclosure] candidate `LeanCert.Test.ExtensionProtocol.wrongCandidate`: expected type `UnaryEnclosureCandidate`, found
  UnaryEnclosureRequest → ℕ -/
#guard_msgs in
@[leancert_enclosure wrongCandidate]
theorem rejectsWrongCandidate
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkIdentity request output = true) :
    identity x ∈ output := by
  have hout : output = request.input := of_decide_eq_true hcheck
  simpa [identity, hout] using hx

def impossibleChecker (_request : UnaryEnclosureRequest) (_output : IntervalRat) : Bool := false

/-- error: invalid @[leancert_enclosure] theorem `LeanCert.Test.ExtensionProtocol.rejectsWrongInput`: input-membership hypothesis must use `request.input` -/
#guard_msgs in
@[leancert_enclosure identityCandidate]
theorem rejectsWrongInput
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ output)
    (_hcheck : impossibleChecker request output = true) :
    identity x ∈ output := by
  simpa [identity] using hx

def alwaysTrueChecker (_request : UnaryEnclosureRequest) (_output : IntervalRat) : Bool := true

/-- error: invalid @[leancert_enclosure] theorem `LeanCert.Test.ExtensionProtocol.rejectsFalseComparison`: checker hypothesis must compare against `true` -/
#guard_msgs in
@[leancert_enclosure identityCandidate]
theorem rejectsFalseComparison
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (_hx : x ∈ request.input)
    (hcheck : alwaysTrueChecker request output = false) :
    identity x ∈ output := by
  simp [alwaysTrueChecker] at hcheck

/-- error: invalid @[leancert_enclosure] declaration `LeanCert.Test.ExtensionProtocol.rejectsDefinition`: soundness boundary must be a proved theorem, not an axiom or definition -/
#guard_msgs in
@[leancert_enclosure identityCandidate]
def rejectsDefinition
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkIdentity request output = true) :
    identity x ∈ output := by
  have hout : output = request.input := of_decide_eq_true hcheck
  simpa [identity, hout] using hx

end LeanCert.Test.ExtensionProtocol
