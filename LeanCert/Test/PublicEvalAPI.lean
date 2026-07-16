/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert

/-!
# Public evaluation API smoke tests

This file intentionally imports only the umbrella module. It guards the
authoritative checked façade, backend selection, structured failures, and the
backend-independent golden theorem.
-/

namespace LeanCert.Test.PublicEvalAPI

open LeanCert
open LeanCert.Core

def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩
def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
def identity : Expr := .var 0

def invalidDyadicOptions : EvalOptions := {
  backend := .dyadic
  precisionOptions := { dyadicExponent := 1 }
}

def usedBackend (expected : ConcreteBackend)
    (result : EvalResult IntervalOutcome) : Bool :=
  match result with
  | .ok outcome => decide (outcome.backend = expected)
  | .error _ => false

def failed (result : EvalResult IntervalOutcome) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

def oneStepSearch : SearchOptions := {
  maxIterations := 1
  tolerance := 1 / 100
  useMonotonicity := false
}

def optimizationOptions (backend : BackendChoice) : GlobalOptOptions := {
  evaluation := { backend }
  search := oneStepSearch
}

def usedOptimizationBackend (expected : ConcreteBackend)
    (result : EvalResult GlobalOutcome) : Bool :=
  match result with
  | .ok outcome => decide (outcome.backend = expected)
  | .error _ => false

def optimizationFailed (result : EvalResult GlobalOutcome) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

#guard usedBackend .dyadic (evalInterval identity [unitInterval])
#guard usedBackend .rational
  (evalInterval identity [unitInterval] { backend := .rational })
#guard usedBackend .dyadic
  (evalInterval identity [unitInterval] { backend := .dyadic })
#guard usedBackend .affine
  (evalInterval identity [unitInterval] { backend := .affine })

#guard decide ((LeanCert.Engine.EvalError.unsupportedFeature "x") =
  LeanCert.Engine.EvalError.unsupportedFeature "x")
#guard decide (({ interval := unitInterval, backend := .rational } : IntervalOutcome) =
  { interval := unitInterval, backend := .rational })

#guard failed (evalInterval (.log identity) [crossesZero])
#guard failed
  (evalInterval identity [unitInterval] invalidDyadicOptions)

#guard usedOptimizationBackend .dyadic
  (globalMinimize identity [unitInterval] (optimizationOptions .auto))
#guard usedOptimizationBackend .rational
  (globalMinimize identity [unitInterval] (optimizationOptions .rational))
#guard usedOptimizationBackend .dyadic
  (globalMaximize identity [unitInterval] (optimizationOptions .dyadic))
#guard usedOptimizationBackend .affine
  (globalMaximize identity [unitInterval] (optimizationOptions .affine))
#guard optimizationFailed (globalMinimize (.inv identity) [crossesZero])

example (e : Expr) (box : List IntervalRat) (options : EvalOptions) (outcome : IntervalOutcome)
    (hsuccess : evalInterval e box options = .ok outcome)
    (rho : Nat → ℝ)
    (hrho : BoxEnvMem rho box) :
    Expr.eval rho e ∈ outcome.interval :=
  evalInterval_correct hsuccess hrho

example (outcome : IntervalOutcome)
    (hsuccess : evalInterval1 identity unitInterval = .ok outcome)
    (x : ℝ) (hx : x ∈ unitInterval) :
    Expr.eval (pointEnv1 x) identity ∈ outcome.interval :=
  evalInterval1_correct hsuccess hx

example (result : IntervalRat)
    (hsuccess : Backend.Rational.eval identity [unitInterval] = .ok result)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unitInterval]) :
    Expr.eval rho identity ∈ result :=
  Backend.Rational.eval_correct hsuccess hrho

example (result : IntervalDyadic)
    (hsuccess : Backend.Dyadic.eval identity [unitInterval] = .ok result)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unitInterval]) :
    Expr.eval rho identity ∈ result :=
  Backend.Dyadic.eval_correct hsuccess hrho

example (result : Engine.Affine.AffineForm)
    (hsuccess : Backend.Affine.eval identity [unitInterval] = .ok result)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unitInterval]) :
    Expr.eval rho identity ∈ result.toInterval :=
  Backend.Affine.eval_correct hsuccess hrho

example (outcome : GlobalOutcome)
    (hsuccess : globalMinimize identity [unitInterval] = .ok outcome)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unitInterval]) :
    (outcome.result.lowerBound : ℝ) ≤ Expr.eval rho identity :=
  globalMinimize_correct hsuccess hrho

example (outcome : GlobalOutcome)
    (hsuccess : globalMaximize identity [unitInterval] = .ok outcome)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unitInterval]) :
    Expr.eval rho identity ≤ (outcome.result.upperBound : ℝ) :=
  globalMaximize_correct hsuccess hrho

end LeanCert.Test.PublicEvalAPI
