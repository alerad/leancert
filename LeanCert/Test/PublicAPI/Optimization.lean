/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Optimization

/-! # Narrow public optimization API contract -/

namespace LeanCert.Test.PublicAPI.Optimization

open LeanCert LeanCert.Core

def unit : IntervalRat := ⟨0, 1, by norm_num⟩
def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
def identity : Expr := .var 0

def failed (result : EvalResult GlobalOutcome) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

#guard failed (globalMinimize (.inv identity) [crossesZero])

example (outcome : GlobalOutcome)
    (h : globalMinimize identity [unit] = .ok outcome)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unit]) :
    (outcome.result.lowerBound : ℝ) ≤ Expr.eval rho identity :=
  globalMinimize_correct h hrho

example (outcome : GlobalOutcome)
    (h : globalMaximize identity [unit] = .ok outcome)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unit]) :
    Expr.eval rho identity ≤ (outcome.result.upperBound : ℝ) :=
  globalMaximize_correct h hrho

end LeanCert.Test.PublicAPI.Optimization
