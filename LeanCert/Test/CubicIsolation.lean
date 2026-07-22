/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Algebra

/-! # Complete cubic-isolation certificate regressions -/

namespace LeanCert.Test.CubicIsolation

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Algebra
open LeanCert.Validity.Algebra

/-- `x³ - x`, with roots `-1`, `0`, and `1`. -/
def threeRoots : QCubic := ⟨1, 0, -1, 0⟩

def isolation : CubicIsolationCert where
  left := ⟨-11 / 10, -9 / 10, by norm_num⟩
  middle := ⟨-1 / 10, 1 / 10, by norm_num⟩
  right := ⟨9 / 10, 11 / 10, by norm_num⟩

example : cubicIsolationCheck threeRoots isolation = true := by native_decide

example :
    (∃! x, x ∈ isolation.left ∧ Expr.eval (fun _ => x) threeRoots.toExpr = 0) ∧
    (∃! x, x ∈ isolation.middle ∧ Expr.eval (fun _ => x) threeRoots.toExpr = 0) ∧
    (∃! x, x ∈ isolation.right ∧ Expr.eval (fun _ => x) threeRoots.toExpr = 0) ∧
    cubicZeroSet threeRoots.toReal ⊆
      intervalSet isolation.left ∪ intervalSet isolation.middle ∪ intervalSet isolation.right := by
  exact verify_complete_cubic_isolation threeRoots isolation (by native_decide)

example : threeRoots.cauchyRadius = 2 := by native_decide

example : threeRoots.separationMeshCheck threeRoots.automaticSeparationMesh = true := by
  native_decide

/-- Reversing two intervals corrupts the global certificate. -/
def misordered : CubicIsolationCert where
  left := isolation.middle
  middle := isolation.left
  right := isolation.right

example : cubicIsolationCheck threeRoots misordered = false := by native_decide

/-- A nonpositive mesh width is rejected independently of the polynomial. -/
example : threeRoots.separationMeshCheck 0 = false := by native_decide

end LeanCert.Test.CubicIsolation
