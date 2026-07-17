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
    (isSmoke : Bool) : Case := {
  name := s!"eval.{workload.name}.internal.{backendName backend}"
  family := workload.family
  layer := .internal
  backendRequested := backendName backend
  suites := if isSmoke then ["smoke", "evaluation"] else ["evaluation"]
  parameters := workload.parameters ++ internalParameters backend
  input := inputMetrics workload.expr
  innerIterations := workload.innerIterations
  run := match backend with
    | .rational => internalRational workload.expr workload.box
    | .dyadic => internalDyadic workload.expr workload.box
    | .affine => internalAffine workload.expr workload.box
}

private def checkedCase (workload : Workload) (requested : String)
    (backend : BackendChoice) (expected : ConcreteBackend) (isSmoke : Bool) : Case := {
  name := s!"eval.{workload.name}.checked.{requested}"
  family := workload.family
  layer := .checkedAPI
  backendRequested := requested
  suites := if isSmoke then ["smoke", "evaluation"] else ["evaluation"]
  parameters := workload.parameters ++ checkedParameters
  input := inputMetrics workload.expr
  innerIterations := workload.innerIterations
  run := checked backend expected workload.expr workload.box
}

private def workloadCases (workload : Workload) : List Case := [
  internalCase workload .rational true,
  internalCase workload .dyadic true,
  internalCase workload .affine (workload.name = "x_minus_x"),
  checkedCase workload "auto" .auto .dyadic true,
  checkedCase workload "rational" .rational .rational false,
  checkedCase workload "dyadic" .dyadic .dyadic false,
  checkedCase workload "affine" .affine .affine (workload.name = "x_minus_x")
]

private def workloads : List Workload := [
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

def cases : List Case := workloads.flatMap workloadCases

end LeanCert.Benchmark.Evaluation
