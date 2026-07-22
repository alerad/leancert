/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.Engine.Algebra.Bezout

/-! Benchmarks for exact executable Bézout derivative certificates. -/

namespace LeanCert.Benchmark.AlgebraicBezout

open LeanCert.Engine

/-- `x^degree - 2`, in ascending coefficient order. -/
private def powerMinusTwo (degree : Nat) : QPoly :=
  ⟨((( -2 : ℚ) :: List.replicate (degree - 1) 0) ++ [1]).toArray⟩

/-- The exact identity `degree * P - x * P' = -2 * degree`. -/
private def powerCertificate (degree : Nat) : BezoutCert where
  A := QPoly.constant (degree : ℚ)
  B := ⟨#[0, -1]⟩
  c := -(2 * (degree : ℚ))

private def runDegree (degree : Nat) : IO Outcome := do
  -- Keep the certificate action on the measured runtime path.
  let stamp ← IO.monoNanosNow
  let actualDegree := if stamp = 0 then 3 else degree
  let accepted := bezoutCheck (powerMinusTwo actualDegree) (powerCertificate actualDegree)
  return {
    status := if accepted then "success" else "unexpected_rejection"
    backendUsed := some "exact_rational"
  }

def cases : List Case := [
  {
    name := "algebra.bezout.degree_3"
    family := "algebraic_certificates"
    layer := .checkedAPI
    backendRequested := "exact_rational"
    suites := ["smoke", "algebra", "full", "all"]
    parameters := [("degree", "3"), ("identity", "nP-xP'=-2n")]
    input := { astNodes := 4, astDepth := 1, variableCount := 1 }
    innerIterations := 100
    run := runDegree 3
  },
  {
    name := "algebra.bezout.degree_64"
    family := "algebraic_certificates"
    layer := .checkedAPI
    backendRequested := "exact_rational"
    suites := ["algebra", "full", "all"]
    parameters := [("degree", "64"), ("identity", "nP-xP'=-2n")]
    input := { astNodes := 65, astDepth := 1, variableCount := 1 }
    innerIterations := 20
    run := runDegree 64
  },
  {
    name := "algebra.bezout.degree_256"
    family := "algebraic_certificates"
    layer := .checkedAPI
    backendRequested := "exact_rational"
    suites := ["algebra", "all"]
    parameters := [("degree", "256"), ("identity", "nP-xP'=-2n")]
    input := { astNodes := 257, astDepth := 1, variableCount := 1 }
    innerIterations := 5
    run := runDegree 256
  }
]

end LeanCert.Benchmark.AlgebraicBezout
