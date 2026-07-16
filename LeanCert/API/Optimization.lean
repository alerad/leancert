/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval
import LeanCert.Engine.Optimization.Backend

/-!
# Public checked global optimization

Global optimization composes the same evaluation options used by
`LeanCert.evalInterval` with backend-independent branch-and-bound search
options. Concrete backend configuration types remain implementation details.
-/

namespace LeanCert

open LeanCert.Core

/-- Stable, backend-independent optimization result.

Engine queue state is intentionally omitted: callers that need resumable
branch-and-bound state should use the advanced engine API directly. -/
structure GlobalResult where
  lowerBound : ℚ
  upperBound : ℚ
  bestBox : List IntervalRat
  iterations : Nat
  deriving Repr

/-- Public optimization result together with the concrete backend selected. -/
structure GlobalOutcome where
  result : GlobalResult
  backend : ConcreteBackend
  deriving Repr

/-- Backend-independent branch-and-bound controls. -/
structure SearchOptions where
  maxIterations : Nat := 1000
  tolerance : ℚ := 1 / 1000
  useMonotonicity : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Public global-optimization configuration, composed from evaluation and
search concerns. -/
structure GlobalOptOptions where
  evaluation : EvalOptions := {}
  search : SearchOptions := {}
  deriving Repr, DecidableEq, Inhabited

private def GlobalOptOptions.toEngineConfig
    (options : GlobalOptOptions) : Engine.Optimization.BackendGlobalOptConfig := {
  backend := options.evaluation.backend
  taylorDepth := options.evaluation.precisionOptions.taylorDepth
  dyadicPrecision := options.evaluation.precisionOptions.dyadicExponent
  maxNoiseSymbols := options.evaluation.precisionOptions.maxNoiseSymbols
  maxIterations := options.search.maxIterations
  tolerance := options.search.tolerance
  useMonotonicity := options.search.useMonotonicity
}

private def GlobalResult.ofEngine
    (result : Engine.Optimization.GlobalResult) : GlobalResult := {
  lowerBound := result.bound.lo
  upperBound := result.bound.hi
  bestBox := result.bound.bestBox
  iterations := result.bound.iterations
}

private def GlobalOutcome.ofEngine
    (outcome : Engine.Optimization.GlobalOutcome) : GlobalOutcome := {
  result := GlobalResult.ofEngine outcome.result
  backend := outcome.backend
}

/-- Checked global minimization over a rational box. -/
def globalMinimize (e : Expr) (box : List IntervalRat)
    (options : GlobalOptOptions := {}) : EvalResult GlobalOutcome := do
  return GlobalOutcome.ofEngine
    (← Engine.Optimization.globalMinimizeWith options.toEngineConfig e box)

/-- Checked global maximization over a rational box. -/
def globalMaximize (e : Expr) (box : List IntervalRat)
    (options : GlobalOptOptions := {}) : EvalResult GlobalOutcome := do
  return GlobalOutcome.ofEngine
    (← Engine.Optimization.globalMaximizeWith options.toEngineConfig e box)

/-- A successful minimization returns a certified lower bound. -/
theorem globalMinimize_correct {e : Expr} {box : List IntervalRat}
    {options : GlobalOptOptions} {outcome : GlobalOutcome}
    (hsuccess : globalMinimize e box options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    (outcome.result.lowerBound : ℝ) ≤ Expr.eval rho e := by
  cases hengine : Engine.Optimization.globalMinimizeWith
      options.toEngineConfig e box with
  | error err =>
      simp [globalMinimize, hengine] at hsuccess
  | ok engineOutcome =>
      have hout : outcome = GlobalOutcome.ofEngine engineOutcome := by
        simpa [globalMinimize, hengine] using hsuccess.symm
      subst outcome
      apply Engine.Optimization.globalMinimizeWith_lower_correct
        options.toEngineConfig e box engineOutcome hengine rho
      · intro i
        exact hrho.get i.val i.isLt
      · exact fun i hi => hrho.eq_zero i hi

/-- A successful maximization returns a certified upper bound. -/
theorem globalMaximize_correct {e : Expr} {box : List IntervalRat}
    {options : GlobalOptOptions} {outcome : GlobalOutcome}
    (hsuccess : globalMaximize e box options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    Expr.eval rho e ≤ (outcome.result.upperBound : ℝ) := by
  cases hengine : Engine.Optimization.globalMaximizeWith
      options.toEngineConfig e box with
  | error err =>
      simp [globalMaximize, hengine] at hsuccess
  | ok engineOutcome =>
      have hout : outcome = GlobalOutcome.ofEngine engineOutcome := by
        simpa [globalMaximize, hengine] using hsuccess.symm
      subst outcome
      apply Engine.Optimization.globalMaximizeWith_upper_correct
        options.toEngineConfig e box engineOutcome hengine rho
      · intro i
        exact hrho.get i.val i.isLt
      · exact fun i hi => hrho.eq_zero i hi

end LeanCert
