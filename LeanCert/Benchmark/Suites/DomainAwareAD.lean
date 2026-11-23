/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.API.AD

/-! Benchmarks for checked reciprocal/logarithm automatic differentiation. -/

namespace LeanCert.Benchmark.DomainAwareAD

open LeanCert.Core
open LeanCert.Engine

private def positive : IntervalRat := ⟨1, 2, by norm_num⟩
private def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
private def nested : Expr := .log (.inv (.add (.var 0) (.const 1)))
private def reciprocal : Expr := .inv (.var 0)

private def deepNested : Nat → Expr
  | 0 => .add (.var 0) (.const 2)
  | n + 1 => .add (.mul (deepNested n) (.const (1 / 3))) (.const (1 / 7))

private def deepDomainAware : Expr := .log (.inv (deepNested 60))

private def chooseInterval (fallback : IntervalRat) : IO IntervalRat := do
  let stamp ← IO.monoNanosNow
  return if stamp = 0 then IntervalRat.singleton 1 else fallback

private def uncheckedRun : IO Outcome := do
  let I ← chooseInterval positive
  let result := LeanCert.Internal.AD.evalTotalCore nested (mkDualEnv (fun _ => I) 0) {}
  return { status := "success", interval := some result.der, backendUsed := some "rational" }

private def checkedRun : IO Outcome := do
  let I ← chooseInterval positive
  match derivIntervalChecked nested (fun _ => I) 0 {} with
  | .ok result =>
      return { status := "success", interval := some result, backendUsed := some "rational" }
  | .error err =>
      return { status := "error", error := some s!"{repr err}", backendUsed := some "rational" }

private def rejectedRun : IO Outcome := do
  let I ← chooseInterval crossesZero
  match derivIntervalChecked reciprocal (fun _ => I) 0 {} with
  | .error _ => return { status := "domain_rejected", backendUsed := some "rational" }
  | .ok result =>
      return { status := "unexpected_success", interval := some result, backendUsed := some "rational" }

private def dyadicCheckedRun : IO Outcome := do
  let I ← chooseInterval positive
  let rho : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I (-53)
  match derivIntervalDyadicChecked nested rho 0 {} with
  | .ok result =>
      let resultRat : IntervalRat := result.toIntervalRat
      return { status := "success", interval := some resultRat, backendUsed := some "dyadic" }
  | .error err =>
      return { status := "error", error := some s!"{repr err}", backendUsed := some "dyadic" }

private def deepRationalRun : IO Outcome := do
  let I ← chooseInterval positive
  match derivIntervalChecked deepDomainAware (fun _ => I) 0 {} with
  | .ok result =>
      return { status := "success", interval := some result, backendUsed := some "rational" }
  | .error err =>
      return { status := "error", error := some s!"{repr err}", backendUsed := some "rational" }

private def deepDyadicRun : IO Outcome := do
  let I ← chooseInterval positive
  let rho : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I (-53)
  match derivIntervalDyadicChecked deepDomainAware rho 0 {} with
  | .ok result =>
      let resultRat : IntervalRat := result.toIntervalRat
      return { status := "success", interval := some resultRat, backendUsed := some "dyadic" }
  | .error err =>
      return { status := "error", error := some s!"{repr err}", backendUsed := some "dyadic" }

private def rootExpression (direct : Bool) (a : Expr) : Expr :=
  if direct then .sqrt a else .exp (.mul (.const (1 / 2)) (.log a))

private def normalizationArg : Expr := .add (.const 1) (.mul (.var 0) (.var 0))
private def recurrenceArg : Expr := .inv (.add (.const 4) (.neg (.mul (.const 6) (.var 0))))
private def recurrenceBox : IntervalRat := ⟨0, 1 / 1500000, by norm_num⟩

private def sqrtPublicRun (e : Expr) (box : IntervalRat) (backend : BackendChoice) : IO Outcome := do
  let I ← chooseInterval box
  match evalWithDerivative e [I] 0 { backend := backend } with
  | .ok result =>
      return {
        status := "success"
        interval := some result.derivative
        backendUsed := some (if result.backend == .rational then "rational" else "dyadic") }
  | .error err => return { status := "error", error := some s!"{repr err}" }

/-- Matched public-API workloads, using the existing log/exp route as the baseline. -/
private def sqrtCases : List Case :=
  ([false, true].flatMap fun direct =>
    ([ ("rational", BackendChoice.rational), ("dyadic", BackendChoice.dyadic) ].flatMap
      fun (backendName, backend) =>
        [false, true].map fun recurrence =>
          let route := if direct then "direct" else "log_exp"
          let workload := if recurrence then "recurrence" else "normalization"
          let e : Expr := if recurrence then .neg (rootExpression direct recurrenceArg)
                   else rootExpression direct normalizationArg
          let I := if recurrence then recurrenceBox else positive
          { name := s!"ad.sqrt.{workload}.{backendName}.{route}"
            family := "automatic_differentiation"
            layer := .checkedAPI
            backendRequested := backendName
            suites := ["ad", "full", "all"]
            parameters := [("route", route), ("domain", if recurrence then "[0,1/1500000]" else "[1,2]"),
              ("taylor_depth", "10"), ("dyadic_precision", "-53"), ("rational_sqrt_bits", "20")]
            input := { astNodes := (if recurrence then 9 else 6) + (if direct then 0 else 3),
                       astDepth := (if recurrence then 7 else 4) + (if direct then 0 else 2),
                       variableCount := 1 }
            innerIterations := 3
            run := sqrtPublicRun e I backend }))

def cases : List Case := [
  {
    name := "ad.inv_log_nested.unchecked"
    family := "automatic_differentiation"
    layer := .internal
    backendRequested := "rational"
    suites := ["ad", "full", "all"]
    parameters := [("domain", "[1,2]"), ("implementation", "eval_total_core")]
    input := { astNodes := 5, astDepth := 4, variableCount := 1 }
    innerIterations := 50
    run := uncheckedRun
  },
  {
    name := "ad.inv_log_nested.checked"
    family := "automatic_differentiation"
    layer := .checkedAPI
    backendRequested := "rational"
    suites := ["smoke", "ad", "full", "all"]
    parameters := [("domain", "[1,2]"), ("implementation", "domain_checked")]
    input := { astNodes := 5, astDepth := 4, variableCount := 1 }
    innerIterations := 50
    run := checkedRun
  },
  {
    name := "ad.inv_log_nested.dyadic_checked"
    family := "automatic_differentiation"
    layer := .checkedAPI
    backendRequested := "dyadic"
    suites := ["smoke", "ad", "full", "all"]
    parameters := [("domain", "[1,2]"), ("implementation", "dyadic_domain_checked"),
      ("precision", "-53")]
    input := { astNodes := 5, astDepth := 4, variableCount := 1 }
    innerIterations := 50
    run := dyadicCheckedRun
  },
  {
    name := "ad.inv_crosses_zero.rejected"
    family := "automatic_differentiation"
    layer := .checkedAPI
    backendRequested := "rational"
    suites := ["ad", "full", "all"]
    parameters := [("domain", "[-1,1]"), ("implementation", "domain_checked")]
    input := { astNodes := 2, astDepth := 2, variableCount := 1 }
    innerIterations := 100
    expectedStatus := "domain_rejected"
    run := rejectedRun
  },
  {
    name := "ad.deep_inv_log.rational_checked"
    family := "automatic_differentiation"
    layer := .checkedAPI
    backendRequested := "rational"
    suites := ["ad", "full", "all"]
    parameters := [("depth", "60"), ("implementation", "domain_checked")]
    input := { astNodes := 245, astDepth := 124, variableCount := 1 }
    innerIterations := 5
    run := deepRationalRun
  },
  {
    name := "ad.deep_inv_log.dyadic_checked"
    family := "automatic_differentiation"
    layer := .checkedAPI
    backendRequested := "dyadic"
    suites := ["ad", "full", "all"]
    parameters := [("depth", "60"), ("implementation", "dyadic_domain_checked"),
      ("precision", "-53")]
    input := { astNodes := 245, astDepth := 124, variableCount := 1 }
    innerIterations := 5
    run := deepDyadicRun
  }
] ++ sqrtCases

end LeanCert.Benchmark.DomainAwareAD
