/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.Engine.AD.Dyadic

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
]

end LeanCert.Benchmark.DomainAwareAD
