/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.Engine.RootFinding.KrawczykCandidate
import LeanCert.Examples.Krawczyk

/-!
# Nonlinear-system certification benchmarks

The internal cases isolate interval-Jacobian construction and the rational
matrix/norm phase.  The checked case measures the complete Boolean certificate
path used by the golden theorem.
-/

namespace LeanCert.Benchmark.Krawczyk

open LeanCert.Engine
open LeanCert.Examples.Krawczyk

private def input : InputMetrics := {
  astNodes := 13
  astDepth := 4
  variableCount := 2
}

private def expInput : InputMetrics := {
  astNodes := 4
  astDepth := 3
  variableCount := 1
}

private def jacobianRun : IO Outcome := do
  let stamp ← IO.monoNanosNow
  let selectedBox : Fin 2 → LeanCert.Core.IntervalRat :=
    if stamp = 0 then fun _ => LeanCert.Core.IntervalRat.singleton 0 else box
  let J := intervalJacobian system selectedBox {}
  let width := (J 0 0).hi - (J 0 0).lo
  if width.den = 0 then
    return { status := "error", error := some "impossible zero denominator" }
  return { status := "success", backendUsed := some "rational" }

private def matrixNormRun : IO Outcome := do
  let stamp ← IO.monoNanosNow
  let selectedBox : Fin 2 → LeanCert.Core.IntervalRat :=
    if stamp = 0 then fun _ => LeanCert.Core.IntervalRat.singleton 0 else box
  let J := intervalJacobian system selectedBox {}
  let q := intervalMatrixBound (preconditionedJacobian certificate.preconditioner J)
  if q < 1 then
    return { status := "success", backendUsed := some "rational" }
  return { status := "failed_contraction", backendUsed := some "rational" }

private def checkedRun : IO Outcome := do
  let stamp ← IO.monoNanosNow
  let selectedBox : Fin 2 → LeanCert.Core.IntervalRat :=
    if stamp = 0 then fun _ => LeanCert.Core.IntervalRat.singleton 0 else box
  if krawczykCheck system selectedBox certificate then
    return { status := "success", backendUsed := some "rational" }
  return { status := "certificate_rejected", backendUsed := some "rational" }

private def expCheckedRun : IO Outcome := do
  let stamp ← IO.monoNanosNow
  let selectedBox : Fin 1 → LeanCert.Core.IntervalRat :=
    if stamp = 0 then fun _ => LeanCert.Core.IntervalRat.singleton 0 else expBox
  if krawczykCheck expSystem selectedBox expCertificate then
    return { status := "success", backendUsed := some "rational" }
  return { status := "certificate_rejected", backendUsed := some "rational" }

private def automaticCandidateRun : IO Outcome := do
  let report := generateAutomaticKrawczyk system box
  if report.succeeded then
    return { status := "success", backendUsed := some "rational" }
  return { status := "candidate_search_failed", backendUsed := some "rational" }

private def shiftedExpSystem : Fin 1 → LeanCert.Core.Expr :=
  ![.add (.exp (.var 0)) (.const (-1 / 8))]

private def shiftedExpBox : Fin 1 → LeanCert.Core.IntervalRat :=
  ![⟨-57 / 20, -33 / 20, by norm_num⟩]

private def refinementCandidateRun : IO Outcome := do
  let report := generateAutomaticKrawczyk shiftedExpSystem shiftedExpBox
  if report.succeeded && report.refinements == 1 then
    return { status := "success", backendUsed := some "rational" }
  return { status := "candidate_refinement_failed", backendUsed := some "rational" }

private def baseParameters : List (String × String) := [
  ("system", "coupled_quadratic_2x2"),
  ("box", "[9/10,11/10]^2"),
  ("preconditioner", "exact_center_jacobian_inverse")
]

def cases : List Case := [
  {
    name := "krawczyk.coupled_quadratic_2x2.interval_jacobian"
    family := "nonlinear_system_roots"
    tier := "micro"
    layer := .internal
    backendRequested := "rational"
    suites := ["smoke", "krawczyk", "all"]
    parameters := baseParameters
    input
    innerIterations := 100
    run := jacobianRun
  },
  {
    name := "krawczyk.coupled_quadratic_2x2.matrix_norm"
    family := "nonlinear_system_roots"
    tier := "micro"
    layer := .internal
    backendRequested := "rational"
    suites := ["krawczyk", "all"]
    parameters := baseParameters
    input
    innerIterations := 100
    run := matrixNormRun
  },
  {
    name := "krawczyk.coupled_quadratic_2x2.checked"
    family := "nonlinear_system_roots"
    tier := "end_to_end"
    layer := .checkedAPI
    backendRequested := "rational"
    suites := ["smoke", "end-to-end", "krawczyk", "all"]
    parameters := baseParameters
    input
    innerIterations := 25
    run := checkedRun
  },
  {
    name := "krawczyk.exp_minus_one_1x1.checked"
    family := "nonlinear_system_roots"
    tier := "end_to_end"
    layer := .checkedAPI
    backendRequested := "rational"
    suites := ["smoke", "end-to-end", "krawczyk", "all"]
    parameters := [
      ("system", "exp_minus_one_1x1"),
      ("box", "[-1/10,1/10]"),
      ("preconditioner", "identity")
    ]
    input := expInput
    innerIterations := 25
    run := expCheckedRun
  },
  {
    name := "krawczyk.coupled_quadratic_2x2.automatic_candidate"
    family := "nonlinear_system_roots"
    tier := "end_to_end"
    layer := .internal
    backendRequested := "rational"
    suites := ["smoke", "krawczyk", "all"]
    parameters := baseParameters ++ [("candidate", "automatic_midpoint_jacobian")]
    input
    innerIterations := 25
    run := automaticCandidateRun
  },
  {
    name := "krawczyk.shifted_exp_1x1.refined_candidate"
    family := "nonlinear_system_roots"
    tier := "end_to_end"
    layer := .internal
    backendRequested := "rational"
    suites := ["krawczyk", "all"]
    parameters := [
      ("system", "exp_x_minus_one_eighth"),
      ("box", "[-57/20,-33/20]"),
      ("candidate", "one_interval_newton_refinement")
    ]
    input := expInput
    innerIterations := 10
    run := refinementCandidateRun
  }
]

end LeanCert.Benchmark.Krawczyk
