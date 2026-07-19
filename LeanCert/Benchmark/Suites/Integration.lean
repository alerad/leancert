/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.Validity.IntegrationDyadic

/-!
# Checked integration benchmark suite

Seconds-scale algorithm benchmarks modeled on the computational core of the
verified li(2) example. These cases measure expression evaluation across a
partition plus per-cell domain validation; they do not measure elaboration or
kernel checking of the surrounding theorem.
-/

namespace LeanCert.Benchmark.Integration

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic

/-- Stable interval form of the li(2) integrand used by `Li2Verified`. -/
def li2Integrand : Expr :=
  let x := Expr.var 0
  let one := Expr.const 1
  let x2 := Expr.mul x x
  Expr.mul
    (Expr.log (Expr.add one (Expr.neg x2)))
    (Expr.inv (Expr.mul
      (Expr.log (Expr.add one x))
      (Expr.log (Expr.add one (Expr.neg x)))))

def li2Box : IntervalRat := ⟨1 / 1000, 999 / 1000, by norm_num⟩

private def input : InputMetrics := {
  astNodes := 19
  astDepth := 7
  variableCount := 1
}

private def runLi2Partition (cells : Nat) (h : 0 < cells)
    (cfg : DyadicConfig) : IO Outcome := do
  let result := integratePartitionDyadicChecked li2Integrand li2Box cells h cfg
  -- Force the complete enclosure and validation pass inside the timed action.
  if result.1.width.den = 0 then
    return { status := "error", error := some "impossible zero rational denominator" }
  if result.2 then
    return {
      status := "success"
      interval := some result.1
      backendUsed := some "dyadic"
    }
  return {
    status := "invalid_domain"
    interval := some result.1
    backendUsed := some "dyadic"
  }

private def integrationCase (cells : Nat) (h : 0 < cells := by omega) : Case :=
  let cfg : DyadicConfig := { precision := -53, taylorDepth := 18 }
  {
    name := s!"integration.li2_partition_{cells}.checked.dyadic"
    family := "partitioned_integration"
    tier := "end_to_end"
    layer := .algorithm
    backendRequested := "dyadic"
    suites := ["end-to-end", "all"]
    parameters := [
      ("integrand", "li2_stable_form"),
      ("partition_cells", s!"{cells}"),
      ("dyadic_exponent", "-53"),
      ("taylor_depth", "18"),
      ("domain", "[1/1000,999/1000]")
    ]
    input
    innerIterations := 1
    run := runLi2Partition cells h cfg
  }

def cases : List Case := [
  integrationCase 100,
  integrationCase 500,
  integrationCase 1000,
  integrationCase 2300
]

end LeanCert.Benchmark.Integration
