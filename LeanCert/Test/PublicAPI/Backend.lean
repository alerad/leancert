/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Backend

/-! # Narrow backend-native API contract -/

namespace LeanCert.Test.PublicAPI.Backend

open LeanCert LeanCert.Core

def unit : IntervalRat := ⟨0, 1, by norm_num⟩
def identity : Expr := .var 0

example (result : IntervalRat)
    (h : LeanCert.Backend.Rational.eval identity [unit] = .ok result)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unit]) :
    Expr.eval rho identity ∈ result :=
  LeanCert.Backend.Rational.eval_correct h hrho

example (result : IntervalDyadic)
    (h : LeanCert.Backend.Dyadic.eval identity [unit] = .ok result)
    (rho : Nat → ℝ) (hrho : BoxEnvMem rho [unit]) :
    Expr.eval rho identity ∈ result :=
  LeanCert.Backend.Dyadic.eval_correct h hrho

end LeanCert.Test.PublicAPI.Backend
