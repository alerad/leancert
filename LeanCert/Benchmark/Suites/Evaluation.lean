/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.API.Eval
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine

/-!
# Interval evaluator benchmark suite

Representative arithmetic, transcendental, and dependency workloads.  Each
has internal primitive cases and checked public-API cases, so backend kernel
improvements can be distinguished from validation and dispatch overhead.
-/

namespace LeanCert.Benchmark.Evaluation

open LeanCert
open LeanCert.Core
open LeanCert.Engine

def mkPower (n : Nat) : Expr :=
  match n with
  | 0 => .const 1
  | n + 1 => .mul (.var 0) (mkPower n)

def mkPolynomial (n : Nat) : Expr :=
  match n with
  | 0 => .const 1
  | n + 1 => .add (mkPolynomial n) (mkPower (n + 1))

def mkNestedSin (n : Nat) : Expr :=
  match n with
  | 0 => .var 0
  | n + 1 => .sin (mkNestedSin n)

def mkRationalAffineChain (n : Nat) : Expr :=
  match n with
  | 0 => .var 0
  | n + 1 =>
      .add
        (.mul (.const (1000003 / 1000033 : ℚ)) (mkRationalAffineChain n))
        (.const (1 / 1000037 : ℚ))

def mkRepeatedSum (n : Nat) : Expr :=
  match n with
  | 0 => .const 0
  | n + 1 => .add (.var 0) (mkRepeatedSum n)

def mkRepeatedCancellation (n : Nat) : Expr :=
  let sum := mkRepeatedSum n
  .add sum (.neg sum)

def xMinusX : Expr := .add (.var 0) (.neg (.var 0))

def unitBox : List IntervalRat := [⟨-1, 1, by norm_num⟩]

private def exprNodes : Expr → Nat
  | .const _ | .var _ | .namedConst _ => 1
  | .add a b | .mul a b => 1 + exprNodes a + exprNodes b
  | .neg e | .inv e | .exp e | .sin e | .cos e | .log e | .atan e |
    .arsinh e | .atanh e | .sinc e | .erf e | .sinh e | .cosh e | .tanh e |
    .sqrt e => 1 + exprNodes e

private def exprDepth : Expr → Nat
  | .const _ | .var _ | .namedConst _ => 1
  | .add a b | .mul a b => 1 + max (exprDepth a) (exprDepth b)
  | .neg e | .inv e | .exp e | .sin e | .cos e | .log e | .atan e |
    .arsinh e | .atanh e | .sinc e | .erf e | .sinh e | .cosh e | .tanh e |
    .sqrt e => 1 + exprDepth e

private def variableArity : Expr → Nat
  | .const _ | .namedConst _ => 0
  | .var i => i + 1
  | .add a b | .mul a b => max (variableArity a) (variableArity b)
  | .neg e | .inv e | .exp e | .sin e | .cos e | .log e | .atan e |
    .arsinh e | .atanh e | .sinc e | .erf e | .sinh e | .cosh e | .tanh e |
    .sqrt e => variableArity e

private def inputMetrics (e : Expr) : InputMetrics := {
  astNodes := exprNodes e
  astDepth := exprDepth e
  variableCount := variableArity e
}

private def success (backend : String) (interval : IntervalRat) : Outcome := {
  status := "success"
  interval := some interval
  backendUsed := some backend
}

private def internalRational (e : Expr) (box : List IntervalRat) : IO Outcome := do
  let result := LeanCert.Internal.Rational.evalTotalCore e (intervalEnvOfList box) {}
  return success "rational" result

private def internalDyadic (e : Expr) (box : List IntervalRat) : IO Outcome := do
  let precision := -53
  let env := toDyadicEnv (intervalEnvOfList box) precision
  let result := LeanCert.Internal.Dyadic.evalUnchecked e env {
    precision, taylorDepth := 10
  }
  return success "dyadic" result.toIntervalRat

private def internalAffine (e : Expr) (box : List IntervalRat) : IO Outcome := do
  let result := LeanCert.Internal.Affine.evalUnchecked e
    (LeanCert.Engine.toAffineEnv box) {}
  return success "affine" result.toInterval

private def checked (backend : BackendChoice) (expected : ConcreteBackend)
    (e : Expr) (box : List IntervalRat) : IO Outcome := do
  match LeanCert.evalInterval e box { backend } with
  | .error error =>
      return { status := "error", error := some s!"{repr error}" }
  | .ok result =>
      if result.backend = expected then
        return success (match result.backend with
          | .rational => "rational" | .dyadic => "dyadic" | .affine => "affine") result.interval
      else
        return {
          status := "wrong_backend"
          interval := some result.interval
          error := some s!"expected {repr expected}, got {repr result.backend}"
        }

private def backendName : ConcreteBackend → String
  | .rational => "rational"
  | .dyadic => "dyadic"
  | .affine => "affine"

private def internalParameters : ConcreteBackend → List (String × String)
  | .rational => [
      ("implementation", "total_core"),
      ("taylor_depth", "10")
    ]
  | .dyadic => [
      ("implementation", "unchecked_dyadic"),
      ("dyadic_exponent", "-53"),
      ("taylor_depth", "10")
    ]
  | .affine => [
      ("implementation", "unchecked_affine"),
      ("taylor_depth", "10"),
      ("max_noise_symbols", "0")
    ]

private def checkedParameters : List (String × String) := [
  ("implementation", "public_checked_api"),
  ("dyadic_exponent", "-53"),
  ("taylor_depth", "10"),
  ("max_noise_symbols", "0")
]

private structure Workload where
  name : String
  family : String
  expr : Expr
  box : List IntervalRat
  innerIterations : Nat
  parameters : List (String × String)

private def internalCase (workload : Workload) (backend : ConcreteBackend)
    (isSmoke : Bool) (suiteNames : List String) : Case := {
  name := s!"eval.{workload.name}.internal.{backendName backend}"
  family := workload.family
  layer := .internal
  backendRequested := backendName backend
  suites := if isSmoke then "smoke" :: suiteNames else suiteNames
  parameters := workload.parameters ++ internalParameters backend
  input := inputMetrics workload.expr
  innerIterations := workload.innerIterations
  run := match backend with
    | .rational => internalRational workload.expr workload.box
    | .dyadic => internalDyadic workload.expr workload.box
    | .affine => internalAffine workload.expr workload.box
}

private def checkedCase (workload : Workload) (requested : String)
    (backend : BackendChoice) (expected : ConcreteBackend) (isSmoke : Bool)
    (suiteNames : List String) : Case := {
  name := s!"eval.{workload.name}.checked.{requested}"
  family := workload.family
  layer := .checkedAPI
  backendRequested := requested
  suites := if isSmoke then "smoke" :: suiteNames else suiteNames
  parameters := workload.parameters ++ checkedParameters
  input := inputMetrics workload.expr
  innerIterations := workload.innerIterations
  run := checked backend expected workload.expr workload.box
}

private def workloadCases (workload : Workload) (suiteNames : List String)
    (includeSmoke : Bool) : List Case := [
  internalCase workload .rational includeSmoke suiteNames,
  internalCase workload .dyadic includeSmoke suiteNames,
  internalCase workload .affine
    (includeSmoke && workload.name = "x_minus_x") suiteNames,
  checkedCase workload "auto" .auto .dyadic includeSmoke suiteNames,
  checkedCase workload "rational" .rational .rational false suiteNames,
  checkedCase workload "dyadic" .dyadic .dyadic false suiteNames,
  checkedCase workload "affine" .affine .affine
    (includeSmoke && workload.name = "x_minus_x") suiteNames
]

private def baselineWorkloads : List Workload := [
  {
    name := "polynomial_10"
    family := "arithmetic"
    expr := mkPolynomial 10
    box := unitBox
    innerIterations := 20
    parameters := [("degree", "10")]
  },
  {
    name := "nested_sin_3"
    family := "transcendental"
    expr := mkNestedSin 3
    box := unitBox
    innerIterations := 2
    parameters := [("nesting_depth", "3")]
  },
  {
    name := "x_minus_x"
    family := "dependency"
    expr := xMinusX
    box := unitBox
    innerIterations := 50
    parameters := [("repeated_occurrences", "2")]
  }
]

private def heavyWorkloads : List Workload := [
  {
    name := "polynomial_75"
    family := "arithmetic"
    expr := mkPolynomial 75
    box := unitBox
    innerIterations := 1
    parameters := [("degree", "75")]
  },
  {
    name := "nested_sin_16"
    family := "transcendental"
    expr := mkNestedSin 16
    box := unitBox
    innerIterations := 1
    parameters := [("nesting_depth", "16")]
  },
  {
    name := "rational_affine_chain_160"
    family := "representation"
    expr := mkRationalAffineChain 160
    box := unitBox
    innerIterations := 1
    parameters := [("chain_length", "160"), ("coefficient_bits", "20")]
  },
  {
    name := "repeated_cancellation_128"
    family := "dependency"
    expr := mkRepeatedCancellation 128
    box := unitBox
    innerIterations := 1
    parameters := [("repeated_occurrences", "256")]
  }
]

def cases : List Case :=
  (baselineWorkloads.flatMap fun workload =>
    workloadCases workload ["evaluation", "full"] true) ++
  (heavyWorkloads.flatMap fun workload =>
    workloadCases workload ["heavy", "full"] false)

end LeanCert.Benchmark.Evaluation
