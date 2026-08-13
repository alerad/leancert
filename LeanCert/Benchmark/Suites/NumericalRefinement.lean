/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.API.Bounds
import LeanCert.Tactic.NumericalRefinement

/-!
# Coordinated numerical-refinement benchmarks

These compiled checker benchmarks distinguish a cheap first-stage success from
a tight bound which requires the complete precision/Taylor schedule. They
measure candidate checking only, not tactic elaboration or kernel proof replay.
-/

namespace LeanCert.Benchmark.NumericalRefinement

open LeanCert LeanCert.Core LeanCert.Tactic

private def unit : IntervalRat := ⟨0, 1, by norm_num⟩
private def exponential : Expr := .exp (.var 0)
private def looseUpper : ℚ := 3
private def tightUpper : ℚ :=
  2718281828459045235360287472 / 1000000000000000000000000000

private def checkedAt (bound : ℚ) (precision : Int) (taylorDepth : Nat) : Bool :=
  LeanCert.API.Bounds.checkUpperBound exponential unit bound {
    dyadicExponent := precision
    taylorDepth
  }

private def runFixed (bound : ℚ) (precision : Int) (taylorDepth : Nat)
    (expected : Bool) : IO Outcome := do
  let actual := checkedAt bound precision taylorDepth
  if actual = expected then
    return {
      status := if actual then "success" else "rejected"
      backendUsed := some "dyadic"
    }
  return {
    status := "unexpected_result"
    backendUsed := some "dyadic"
    error := some s!"expected {expected}, got {actual}"
  }

private def firstSuccessfulStage (bound : ℚ) :
    List NumericalRefinementStage → Option NumericalRefinementStage
  | [] => none
  | stage :: rest =>
      if checkedAt bound stage.dyadicPrecision stage.taylorDepth then
        some stage
      else
        firstSuccessfulStage bound rest

private def runAdaptive (bound : ℚ) : IO Outcome := do
  let policy := NumericalRefinementPolicy.adaptive 10 0
  match firstSuccessfulStage bound policy.stages with
  | none =>
      return {
        status := "schedule_exhausted"
        backendUsed := some "dyadic"
        error := some "no numerical-refinement stage certified the bound"
      }
  | some stage =>
      return {
        status := "success"
        backendUsed := some s!"dyadic-stage-{stage.index}"
      }

private def refinementCase (name : String) (parameters : List (String × String))
    (expectedStatus : String := "success") (run : IO Outcome) : Case := {
  name := s!"numerical_refinement.{name}"
  family := "numerical_refinement"
  tier := "micro"
  layer := .checkedAPI
  backendRequested := "dyadic"
  suites := ["numerical-refinement", "all"]
  parameters
  input := { astNodes := 2, astDepth := 2, variableCount := 1 }
  innerIterations := 10
  expectedStatus
  run
}

def cases : List Case := [
  refinementCase "loose.fixed_-80_taylor_30"
    [("schedule", "fixed"), ("precision", "-80"), ("taylor_depth", "30")]
    (run := runFixed looseUpper (-80) 30 true),
  refinementCase "loose.adaptive_first_stage"
    [("schedule", "adaptive"), ("expected_stage", "0")]
    (run := runAdaptive looseUpper),
  refinementCase "tight.fixed_-80_rejected"
    [("schedule", "fixed"), ("precision", "-80"), ("taylor_depth", "30")]
    (expectedStatus := "rejected") (run := runFixed tightUpper (-80) 30 false),
  refinementCase "tight.fixed_-117_taylor_30"
    [("schedule", "fixed"), ("precision", "-117"), ("taylor_depth", "30")]
    (run := runFixed tightUpper (-117) 30 true),
  refinementCase "tight.adaptive_final_stage"
    [("schedule", "adaptive"), ("expected_stage", "2")]
    (run := runAdaptive tightUpper)
]

end LeanCert.Benchmark.NumericalRefinement
