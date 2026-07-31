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

@[leancert_enclosure candidate := shiftedCandidate, priority := 1200]
theorem shifted_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  have hout : output = IntervalRat.add request.input (IntervalRat.singleton 1) := by
    exact of_decide_eq_true hcheck
  rw [hout]
  simpa [shifted] using IntervalRat.mem_add hx (IntervalRat.mem_singleton 1)

@[leancert_enclosure candidate := shiftedCandidate, priority := 100]
theorem shifted_mem_fallback
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  exact shifted_mem hx hcheck

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
