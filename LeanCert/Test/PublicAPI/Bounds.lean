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

end LeanCert.Test.PublicAPI.Bounds
