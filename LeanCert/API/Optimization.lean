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

export LeanCert.Engine.Optimization (GlobalOutcome GlobalResult)

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

/-- Checked global minimization over a rational box. -/
def globalMinimize (e : Expr) (box : List IntervalRat)
    (options : GlobalOptOptions := {}) : EvalResult GlobalOutcome :=
  Engine.Optimization.globalMinimizeWith options.toEngineConfig e box

/-- Checked global maximization over a rational box. -/
def globalMaximize (e : Expr) (box : List IntervalRat)
    (options : GlobalOptOptions := {}) : EvalResult GlobalOutcome :=
  Engine.Optimization.globalMaximizeWith options.toEngineConfig e box

/-- A successful minimization returns a certified lower bound. -/
theorem globalMinimize_correct {e : Expr} {box : List IntervalRat}
    {options : GlobalOptOptions} {outcome : GlobalOutcome}
    (hsuccess : globalMinimize e box options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    (outcome.result.bound.lo : ℝ) ≤ Expr.eval rho e := by
  apply Engine.Optimization.globalMinimizeWith_lower_correct
    options.toEngineConfig e box outcome hsuccess rho
  · intro i
    exact hrho.get i.val i.isLt
  · exact fun i hi => hrho.eq_zero i hi

/-- A successful maximization returns a certified upper bound. -/
theorem globalMaximize_correct {e : Expr} {box : List IntervalRat}
    {options : GlobalOptOptions} {outcome : GlobalOutcome}
    (hsuccess : globalMaximize e box options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    Expr.eval rho e ≤ (outcome.result.bound.hi : ℝ) := by
  apply Engine.Optimization.globalMaximizeWith_upper_correct
    options.toEngineConfig e box outcome hsuccess rho
  · intro i
    exact hrho.get i.val i.isLt
  · exact fun i hi => hrho.eq_zero i hi

end LeanCert
