/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicCell

/-!
# Dyadic midpoint and subdivision regression tests

These tests pin the semantic value of exact dyadic midpoints. In particular,
they catch implementations that shift an odd mantissa right and silently round
instead of decreasing the represented power-of-two exponent.
-/

namespace LeanCert.Test.DyadicSubdivision

open LeanCert.Core

private def unitInterval : IntervalDyadic :=
  ⟨LeanCert.Core.Dyadic.ofInt 0, LeanCert.Core.Dyadic.ofInt 1,
    by norm_num [LeanCert.Core.Dyadic.toRat_ofInt]⟩

private def negativeUnitInterval : IntervalDyadic :=
  ⟨LeanCert.Core.Dyadic.ofInt (-1), LeanCert.Core.Dyadic.ofInt 0,
    by norm_num [LeanCert.Core.Dyadic.toRat_ofInt]⟩

private def symmetricInterval : IntervalDyadic :=
  ⟨LeanCert.Core.Dyadic.ofInt (-1), LeanCert.Core.Dyadic.ofInt 1,
    by norm_num [LeanCert.Core.Dyadic.toRat_ofInt]⟩

/-- `[1/4, 2]`, with endpoints at different exponents. -/
private def mixedExponentInterval : IntervalDyadic :=
  ⟨⟨1, -2⟩, ⟨1, 1⟩, by native_decide⟩

/-- `[-3/2, 1/2]`, exercising a negative odd mantissa. -/
private def negativeOddInterval : IntervalDyadic :=
  ⟨⟨-3, -1⟩, ⟨1, -1⟩, by native_decide⟩

private def singletonInterval : IntervalDyadic :=
  ⟨⟨3, -2⟩, ⟨3, -2⟩, le_rfl⟩

example : unitInterval.midpoint.toRat = 1 / 2 := by
  native_decide

example : negativeUnitInterval.midpoint.toRat = -1 / 2 := by
  native_decide

example : symmetricInterval.midpoint.toRat = 0 := by
  native_decide

example : mixedExponentInterval.midpoint.toRat = 9 / 8 := by
  native_decide

example : negativeOddInterval.midpoint.toRat = -1 / 2 := by
  native_decide

example : singletonInterval.midpoint.toRat = 3 / 4 := by
  native_decide

/-! ### Exact bisection and seam semantics -/

example : unitInterval.bisect.1.lo.toRat = 0 := by native_decide
example : unitInterval.bisect.1.hi.toRat = 1 / 2 := by native_decide
example : unitInterval.bisect.2.lo.toRat = 1 / 2 := by native_decide
example : unitInterval.bisect.2.hi.toRat = 1 := by native_decide

example : unitInterval.bisect.1.width.toRat = 1 / 2 := by native_decide
example : unitInterval.bisect.2.width.toRat = 1 / 2 := by native_decide

example (I : IntervalDyadic) :
    (I.midpoint.toRat : ℝ) ∈ I.bisect.1 ∧ (I.midpoint.toRat : ℝ) ∈ I.bisect.2 :=
  I.midpoint_mem_bisect_both

example (I : IntervalDyadic) :
    I.bisect.1.toSet ∩ I.bisect.2.toSet = {I.midpoint.toReal} :=
  I.bisect_intersection

example (I : IntervalDyadic) (x : ℝ) (hx : x ∈ I) :
    x ∈ I.bisect.1 ∨ x ∈ I.bisect.2 :=
  IntervalDyadic.mem_bisect_or hx

/-! ### Finite paths and directly decoded cells -/

example : DyadicPath.index [false, true] = 1 := by native_decide
example : DyadicPath.index [true, false, true] = 5 := by native_decide

example : (DyadicCell.ofPath [true, false, true]).depth = 3 := by native_decide
example : (DyadicCell.ofPath [true, false, true]).index.val = 5 := by native_decide

example : ((DyadicCell.ofPath [false, true]).decodeDirect unitInterval).lo.toRat = 1 / 4 := by
  native_decide

example : ((DyadicCell.ofPath [false, true]).decodeDirect unitInterval).hi.toRat = 1 / 2 := by
  native_decide

example : ((DyadicCell.ofPath [true, false, true]).decodeDirect unitInterval).lo.toRat = 5 / 8 := by
  native_decide

example : ((DyadicCell.ofPath [true, false, true]).decodeDirect unitInterval).hi.toRat = 3 / 4 := by
  native_decide

example (path : DyadicPath) :
    DyadicCell.ofPath (path ++ [false]) = (DyadicCell.ofPath path).childLeft := by
  simp

example (path : DyadicPath) :
    DyadicCell.ofPath (path ++ [true]) = (DyadicCell.ofPath path).childRight := by
  simp

example (I : IntervalDyadic) (path : DyadicPath) :
    (path.decodeByBisection I).ValueEq ((DyadicCell.ofPath path).decodeDirect I) :=
  DyadicCell.decodeByBisection_valueEq_decodeDirect I path

example :
    (DyadicPath.decodeByBisection mixedExponentInterval [true, false, true]).ValueEq
      ((DyadicCell.ofPath [true, false, true]).decodeDirect mixedExponentInterval) := by
  exact DyadicCell.decodeByBisection_valueEq_decodeDirect _ _

end LeanCert.Test.DyadicSubdivision
