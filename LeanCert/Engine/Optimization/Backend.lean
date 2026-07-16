/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Backend
import LeanCert.Engine.Optimization.Global

/-!
# Unified global-optimization backends

This is the optimization counterpart of the checked evaluation dispatcher. It
owns backend selection and translates common options to concrete optimizer
configurations.
-/

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine

/-- Common options for certified global optimization. -/
structure BackendGlobalOptConfig extends BackendOptions where
  maxIterations : Nat := 1000
  tolerance : ℚ := 1 / 1000
  useMonotonicity : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Successful optimization result together with the backend that produced it. -/
structure GlobalOutcome where
  result : GlobalResult
  backend : ConcreteBackend

private def rationalConfig (cfg : BackendGlobalOptConfig) : GlobalOptConfig := {
  maxIterations := cfg.maxIterations
  tolerance := cfg.tolerance
  useMonotonicity := cfg.useMonotonicity
  taylorDepth := cfg.taylorDepth
}

private def dyadicConfig (cfg : BackendGlobalOptConfig) : GlobalOptConfigDyadic := {
  maxIterations := cfg.maxIterations
  tolerance := cfg.tolerance
  useMonotonicity := cfg.useMonotonicity
  taylorDepth := cfg.taylorDepth
  precision := cfg.dyadicPrecision
}

private def affineConfig (cfg : BackendGlobalOptConfig) : GlobalOptConfigAffine := {
  maxIterations := cfg.maxIterations
  tolerance := cfg.tolerance
  useMonotonicity := cfg.useMonotonicity
  taylorDepth := cfg.taylorDepth
  maxNoiseSymbols := cfg.maxNoiseSymbols
}

private def globalOptimizeWith (minimize : Bool) (cfg : BackendGlobalOptConfig)
    (e : Expr) (box : Box) : EvalResult GlobalOutcome := do
  let backend ← resolveBackend cfg.backend .globalOptimization
  let result ← match backend with
    | .rational =>
        if cfg.taylorDepth != 10 then
          throw (.invalidConfiguration
            "checked Rational optimization has fixed Taylor depth 10")
        if minimize then globalMinimizeRationalChecked e box (rationalConfig cfg)
        else globalMaximizeRationalChecked e box (rationalConfig cfg)
    | .dyadic =>
        if cfg.dyadicPrecision > 0 then
          throw (.invalidConfiguration
            "dyadicPrecision must be nonpositive for certified outward rounding")
        if minimize then globalMinimizeDyadicChecked e box (dyadicConfig cfg)
        else globalMaximizeDyadicChecked e box (dyadicConfig cfg)
    | .affine =>
        if minimize then globalMinimizeAffineChecked e box (affineConfig cfg)
        else globalMaximizeAffineChecked e box (affineConfig cfg)
  return { result, backend }

/-- Global minimization with unified backend selection. -/
def globalMinimizeWith (cfg : BackendGlobalOptConfig) (e : Expr) (box : Box) :
    EvalResult GlobalOutcome :=
  globalOptimizeWith true cfg e box

/-- Global maximization with unified backend selection. -/
def globalMaximizeWith (cfg : BackendGlobalOptConfig) (e : Expr) (box : Box) :
    EvalResult GlobalOutcome :=
  globalOptimizeWith false cfg e box

/-- Successful unified minimization returns a certified lower bound, regardless
of the concrete backend selected by the dispatcher. -/
theorem globalMinimizeWith_lower_correct (cfg : BackendGlobalOptConfig)
    (e : Expr) (box : Box) (outcome : GlobalOutcome)
    (hsuccess : globalMinimizeWith cfg e box = .ok outcome) :
    ∀ rho, Box.envMem rho box → (∀ i, i ≥ box.length → rho i = 0) →
      (outcome.result.bound.lo : ℝ) ≤ Expr.eval rho e := by
  cases hbackend : resolveBackend cfg.backend .globalOptimization with
  | error err =>
      simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend] at hsuccess
  | ok backend =>
      cases backend with
      | rational =>
          have hdepth : cfg.taylorDepth = 10 := by
            by_contra h
            simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend, h] at hsuccess
          cases hrun : globalMinimizeRationalChecked e box (rationalConfig cfg) with
          | error err =>
              simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend, hdepth,
                hrun] at hsuccess
          | ok result =>
              have hout : outcome.result = result := by
                simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend, hdepth,
                  hrun] at hsuccess
                injection hsuccess with h
                exact congrArg GlobalOutcome.result h.symm
              subst result
              exact globalMinimizeRationalChecked_lo_correct e box (rationalConfig cfg)
                outcome.result hrun
      | dyadic =>
          have hprec : cfg.dyadicPrecision ≤ 0 := by
            by_contra h
            have hpos : cfg.dyadicPrecision > 0 := lt_of_not_ge h
            simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend, hpos] at hsuccess
          cases hrun : globalMinimizeDyadicChecked e box (dyadicConfig cfg) with
          | error err =>
              simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend,
                show ¬cfg.dyadicPrecision > 0 from not_lt.mpr hprec, hrun] at hsuccess
          | ok result =>
              have hout : outcome.result = result := by
                simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend,
                  show ¬cfg.dyadicPrecision > 0 from not_lt.mpr hprec, hrun] at hsuccess
                injection hsuccess with h
                exact congrArg GlobalOutcome.result h.symm
              subst result
              exact globalMinimizeDyadicChecked_lo_correct e box (dyadicConfig cfg)
                (by simpa [dyadicConfig] using hprec) outcome.result hrun
      | affine =>
          cases hrun : globalMinimizeAffineChecked e box (affineConfig cfg) with
          | error err =>
              simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend, hrun] at hsuccess
          | ok result =>
              have hout : outcome.result = result := by
                simp [Except.bind, bind, globalMinimizeWith, globalOptimizeWith, hbackend, hrun] at hsuccess
                injection hsuccess with h
                exact congrArg GlobalOutcome.result h.symm
              subst result
              exact globalMinimizeAffineChecked_lo_correct e box (affineConfig cfg)
                outcome.result hrun

/-- Successful unified maximization returns a certified upper bound. -/
theorem globalMaximizeWith_upper_correct (cfg : BackendGlobalOptConfig)
    (e : Expr) (box : Box) (outcome : GlobalOutcome)
    (hsuccess : globalMaximizeWith cfg e box = .ok outcome) :
    ∀ rho, Box.envMem rho box → (∀ i, i ≥ box.length → rho i = 0) →
      Expr.eval rho e ≤ (outcome.result.bound.hi : ℝ) := by
  cases hbackend : resolveBackend cfg.backend .globalOptimization with
  | error err => simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend] at hsuccess
  | ok backend =>
      cases backend with
      | rational =>
          have hdepth : cfg.taylorDepth = 10 := by
            by_contra h
            simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend, h] at hsuccess
          cases hrun : globalMaximizeRationalChecked e box (rationalConfig cfg) with
          | error err =>
              simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend, hdepth,
                hrun] at hsuccess
          | ok result =>
              have hout : outcome.result = result := by
                simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend, hdepth,
                  hrun] at hsuccess
                injection hsuccess with h
                exact congrArg GlobalOutcome.result h.symm
              subst result
              exact globalMaximizeRationalChecked_hi_correct e box (rationalConfig cfg)
                outcome.result hrun
      | dyadic =>
          have hprec : cfg.dyadicPrecision ≤ 0 := by
            by_contra h
            have hpos : cfg.dyadicPrecision > 0 := lt_of_not_ge h
            simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend, hpos] at hsuccess
          cases hrun : globalMaximizeDyadicChecked e box (dyadicConfig cfg) with
          | error err =>
              simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend,
                show ¬cfg.dyadicPrecision > 0 from not_lt.mpr hprec, hrun] at hsuccess
          | ok result =>
              have hout : outcome.result = result := by
                simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend,
                  show ¬cfg.dyadicPrecision > 0 from not_lt.mpr hprec, hrun] at hsuccess
                injection hsuccess with h
                exact congrArg GlobalOutcome.result h.symm
              subst result
              exact globalMaximizeDyadicChecked_hi_correct e box (dyadicConfig cfg)
                (by simpa [dyadicConfig] using hprec) outcome.result hrun
      | affine =>
          cases hrun : globalMaximizeAffineChecked e box (affineConfig cfg) with
          | error err =>
              simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend, hrun] at hsuccess
          | ok result =>
              have hout : outcome.result = result := by
                simp [Except.bind, bind, globalMaximizeWith, globalOptimizeWith, hbackend, hrun] at hsuccess
                injection hsuccess with h
                exact congrArg GlobalOutcome.result h.symm
              subst result
              exact globalMaximizeAffineChecked_hi_correct e box (affineConfig cfg)
                outcome.result hrun

end LeanCert.Engine.Optimization
