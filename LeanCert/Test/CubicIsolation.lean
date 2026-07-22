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
  exact threeRoots.automaticSeparationMesh_check (by norm_num [threeRoots])
    (by norm_num [threeRoots, QCubic.discr])

/-- The same automatic construction works away from monic centered cubics. -/
def shiftedRoots : QCubic := ⟨1, -6, 11, -6⟩ -- roots 1, 2, 3

example : shiftedRoots.cauchyRadius = 24 := by native_decide

example : shiftedRoots.separationMeshCheck shiftedRoots.automaticSeparationMesh = true := by
  exact shiftedRoots.automaticSeparationMesh_check (by norm_num [shiftedRoots])
    (by norm_num [shiftedRoots, QCubic.discr])

example : (threeRoots.automaticSeparationMesh : ℝ) < |(-1 : ℝ) - 0| := by
  apply verify_cubic_distinct_roots_separated threeRoots
  · native_decide
  · exact threeRoots.automaticSeparationMesh_check (by norm_num [threeRoots])
      (by norm_num [threeRoots, QCubic.discr])
  · norm_num [threeRoots, cubicZeroSet, QCubic.toReal]
  · norm_num [threeRoots, cubicZeroSet, QCubic.toReal]
  · norm_num

/-- Reversing two intervals corrupts the global certificate. -/
def misordered : CubicIsolationCert where
  left := isolation.middle
  middle := isolation.left
  right := isolation.right

example : cubicIsolationCheck threeRoots misordered = false := by native_decide

/-- Duplicating an otherwise valid isolating interval is rejected. -/
def duplicated : CubicIsolationCert where
  left := isolation.left
  middle := isolation.middle
  right := isolation.middle

example : cubicIsolationCheck threeRoots duplicated = false := by native_decide

/-- Closed intervals that touch at an endpoint are not pairwise disjoint. -/
def touching : CubicIsolationCert where
  left := ⟨-11 / 10, -1 / 10, by norm_num⟩
  middle := ⟨-1 / 10, 1 / 10, by norm_num⟩
  right := isolation.right

example : cubicIsolationCheck threeRoots touching = false := by native_decide

/-- Overlap is rejected even if each interval is declared left-to-right. -/
def overlapping : CubicIsolationCert where
  left := isolation.left
  middle := ⟨-1 / 10, 11 / 10, by norm_num⟩
  right := isolation.right

example : cubicIsolationCheck threeRoots overlapping = false := by native_decide

/-- A local interval with no root cannot complete a valid global certificate. -/
def missingLeftRoot : CubicIsolationCert where
  left := ⟨-2, -3 / 2, by norm_num⟩
  middle := isolation.middle
  right := isolation.right

example : cubicIsolationCheck threeRoots missingLeftRoot = false := by native_decide

/-- Strict Newton contraction rejects this root-at-the-boundary certificate. -/
def endpointRoot : CubicIsolationCert where
  left := ⟨-1, -9 / 10, by norm_num⟩
  middle := isolation.middle
  right := isolation.right

example : cubicIsolationCheck threeRoots endpointRoot = false := by native_decide

def negativeDiscr : QCubic := ⟨1, 0, 1, 0⟩
def zeroDiscr : QCubic := ⟨1, 0, 0, 0⟩
def degenerate : QCubic := ⟨0, 1, 0, -1⟩

example : cubicIsolationCheck negativeDiscr isolation = false := by native_decide
example : cubicIsolationCheck zeroDiscr isolation = false := by native_decide
example : cubicIsolationCheck degenerate isolation = false := by native_decide

/-- A nonpositive mesh width is rejected independently of the polynomial. -/
example : threeRoots.separationMeshCheck 0 = false := by native_decide
example : threeRoots.separationMeshCheck (-1 / 100) = false := by native_decide
example : threeRoots.separationMeshCheck 1 = false := by native_decide
example : zeroDiscr.separationMeshCheck (1 / 100) = false := by native_decide
example : degenerate.separationMeshCheck (1 / 100) = false := by native_decide

/-- Fractional and negative leading coefficients exercise the radius formula. -/
def fractionalLeading : QCubic := ⟨1 / 2, 0, 0, -4⟩
def negativeLeading : QCubic := ⟨-1, 0, 1, 0⟩

example : fractionalLeading.cauchyRadius = 9 := by native_decide
example : negativeLeading.cauchyRadius = 2 := by native_decide

example : |(2 : ℝ)| ≤ fractionalLeading.cauchyRadius := by
  apply verify_cubic_root_radius fractionalLeading (by norm_num [fractionalLeading])
  norm_num [fractionalLeading, cubicZeroSet, QCubic.toReal]

end LeanCert.Test.CubicIsolation
