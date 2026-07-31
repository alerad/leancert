/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Bounds

/-! # Computable support-free public Bool checker contract -/

namespace LeanCert.Test.PublicAPI.Bounds

open LeanCert LeanCert.Core LeanCert.API.Bounds

def positive : IntervalRat := ⟨1, 2, by norm_num⟩
def logarithm : Expr := .log (.var 0)
def unit : IntervalRat := ⟨0, 1, by norm_num⟩
def sum2 : Expr := .add (.var 0) (.var 1)

example : checkUpperBound logarithm positive 1 = true := by
  native_decide

example : checkLowerBound logarithm positive 0 = true := by
  native_decide

example : checkUpperBound logarithm positive 1
    { dyadicExponent := 1 } = false := by
  native_decide

example (h : checkUpperBound logarithm positive 1 = true) :
    ∀ x ∈ positive, Expr.eval (fun _ => x) logarithm ≤ 1 :=
  by simpa using (verifyUpperBound h)

example (h : checkBounds logarithm positive 0 1 = true) :
    ∀ x ∈ positive,
      0 ≤ Expr.eval (fun _ => x) logarithm ∧
        Expr.eval (fun _ => x) logarithm ≤ 1 := by
  simpa using (verifyBounds h)

example :
    checkUpperBoundBox sum2 [unit, unit] 2 { backend := .rational } =
      .ok ⟨⟨0, 2, by norm_num⟩, .rational, true⟩ := by
  native_decide

example {outcome : BoundCheckOutcome}
    (hcheck : checkUpperBoundBox sum2 [unit, unit] 2 { backend := .rational } = .ok outcome)
    (hverified : outcome.verified = true) :
    ∀ rho, BoxEnvMem rho [unit, unit] → Expr.eval rho sum2 ≤ 2 :=
  verifyUpperBoundBox hcheck hverified

example :
    checkLowerBoundBox sum2 [unit, unit] 0 { backend := .rational } =
      .ok ⟨⟨0, 2, by norm_num⟩, .rational, true⟩ := by
  native_decide

example {outcome : BoundCheckOutcome}
    (hcheck : checkLowerBoundBox sum2 [unit, unit] 0 { backend := .rational } = .ok outcome)
    (hverified : outcome.verified = true) :
    ∀ rho, BoxEnvMem rho [unit, unit] → 0 ≤ Expr.eval rho sum2 :=
  by simpa using verifyLowerBoundBox hcheck hverified

example :
    checkUpperBoundBox sum2 [unit, unit] 1 { backend := .rational } =
      .ok ⟨⟨0, 2, by norm_num⟩, .rational, false⟩ := by
  native_decide

example :
    (match checkLowerBoundBox (.log (.var 0)) [unit] 0 { backend := .rational } with
    | .error _ => true
    | .ok _ => false) = true := by
  native_decide

end LeanCert.Test.PublicAPI.Bounds
