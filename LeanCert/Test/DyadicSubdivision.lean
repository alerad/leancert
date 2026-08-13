/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicFrontier
import LeanCert.Core.DyadicCellDomain
import LeanCert.Core.RationalCellDomain

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

/-! ### Semantic dyadic identity -/

example : (⟨1, 0⟩ : LeanCert.Core.Dyadic).ValueEq ⟨2, -1⟩ := by native_decide

example : (⟨1, 0⟩ : LeanCert.Core.Dyadic) ≠ ⟨2, -1⟩ := by native_decide

example :
    (⟨1, 0⟩ : LeanCert.Core.Dyadic).canonicalKey =
      (⟨2, -1⟩ : LeanCert.Core.Dyadic).canonicalKey := by
  native_decide

example :
    (⟨0, 37⟩ : LeanCert.Core.Dyadic).canonicalKey =
      (0 : LeanCert.Core.Dyadic).canonicalKey := by
  native_decide

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

/-! ### Generic certified cell geometry -/

#synth CertifiedCellDomain IntervalDyadic ℝ
#synth CertifiedCellDomain IntervalRat ℝ

example (I : IntervalDyadic) :
    CertifiedCellDomain.children I = [I.bisect.1, I.bisect.2] := by
  rfl

example (I : IntervalDyadic) :
    CertifiedCellDomain.diameter I = I.width.toRat := by
  rfl

example (I : IntervalDyadic) (depth : Nat) (x : ℝ) (hx : x ∈ I) :
    ∃ child,
      child ∈ CertifiedCellDomain.refineLevel (Point := ℝ) depth I ∧ x ∈ child := by
  exact CertifiedCellDomain.exists_mem_refineLevel hx

example (I child : IntervalDyadic) (depth : Nat) (x : ℝ)
    (hchild : child ∈ CertifiedCellDomain.refineLevel (Point := ℝ) depth I)
    (hx : x ∈ child) : x ∈ I := by
  exact CertifiedCellDomain.contains_of_mem_refineLevel hchild hx

example :
    (CertifiedCellDomain.refineLevel (Point := ℝ) 2 unitInterval).length = 4 := by
  native_decide

example (I : IntervalRat) (depth : Nat) (x : ℝ) (hx : x ∈ I) :
    ∃ child,
      child ∈ CertifiedCellDomain.refineLevel (Point := ℝ) depth I ∧ x ∈ child := by
  exact CertifiedCellDomain.exists_mem_refineLevel hx

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

/-! ### Prepared fixed-depth decoding -/

private def preparedUnitDepth3 : DyadicCell.PreparedDyadicLevel :=
  DyadicCell.PreparedDyadicLevel.prepare unitInterval 3

example : preparedUnitDepth3.cellCount = 8 := by native_decide

example : (preparedUnitDepth3.intervalAt ⟨5, by native_decide⟩).lo.toRat = 5 / 8 := by
  native_decide

example : (preparedUnitDepth3.intervalAt ⟨5, by native_decide⟩).hi.toRat = 3 / 4 := by
  native_decide

example : preparedUnitDepth3.materialize.length = 8 := by native_decide

example : preparedUnitDepth3.materialize.map (fun I => I.lo.toRat) =
    [0, 1 / 8, 1 / 4, 3 / 8, 1 / 2, 5 / 8, 3 / 4, 7 / 8] := by
  native_decide

example (I : IntervalDyadic) (depth : Nat)
    (index : Fin (DyadicCell.PreparedDyadicLevel.prepare I depth).cellCount) :
    ((DyadicCell.PreparedDyadicLevel.prepare I depth).intervalAt index).ValueEq
      ((DyadicCell.mk depth index).decodeDirect I) :=
  DyadicCell.PreparedDyadicLevel.intervalAt_valueEq_decodeDirect _ _

/-! ### Closed proof cells and canonical ownership -/

open DyadicCell.Ownership

example (I : IntervalDyadic) (depth : Nat) (x : ℝ) (hx : x ∈ I) :
    ∃! index : Fin (2 ^ depth), Owns I depth index x :=
  exists_unique_owner I depth hx

example (I : IntervalDyadic) (depth : Nat) (i j : Fin (2 ^ depth)) (hij : i ≠ j) :
    Disjoint (ownerSet I depth i) (ownerSet I depth j) :=
  ownerSet_disjoint hij

example (I : IntervalDyadic) (depth : Nat) (i j : Fin (2 ^ depth))
    (x : ℝ) (hij : i < j) (hxj : x ∈ closedCell I depth j) :
    ¬ Owns I depth i x :=
  not_owns_of_mem_higher hij hxj

private theorem midpoint_mem_depthOneRight :
    (1 / 2 : ℝ) ∈ closedCell unitInterval 1 ⟨1, by norm_num⟩ := by
  have hlo : (closedCell unitInterval 1 ⟨1, by norm_num⟩).lo.toRat = 1 / 2 := by
    native_decide
  have hhi : (closedCell unitInterval 1 ⟨1, by norm_num⟩).hi.toRat = 1 := by
    native_decide
  change ((closedCell unitInterval 1 ⟨1, by norm_num⟩).lo.toRat : ℝ) ≤ 1 / 2 ∧
    (1 / 2 : ℝ) ≤ (closedCell unitInterval 1 ⟨1, by norm_num⟩).hi.toRat
  rw [hlo, hhi]
  norm_num

example : ¬ Owns unitInterval 1 ⟨0, by norm_num⟩ (1 / 2 : ℝ) := by
  exact not_owns_of_mem_higher (i := ⟨0, by norm_num⟩) (j := ⟨1, by norm_num⟩)
    (by norm_num) midpoint_mem_depthOneRight

example : Owns unitInterval 1 (lastIndex 1) (1 / 2 : ℝ) := by
  apply last_owns_of_mem
  simpa [lastIndex] using midpoint_mem_depthOneRight

private theorem singleton_mem_lastDepthThree :
    (3 / 4 : ℝ) ∈ closedCell singletonInterval 3 (lastIndex 3) := by
  have hlo : (closedCell singletonInterval 3 (lastIndex 3)).lo.toRat = 3 / 4 := by
    native_decide
  have hhi : (closedCell singletonInterval 3 (lastIndex 3)).hi.toRat = 3 / 4 := by
    native_decide
  change ((closedCell singletonInterval 3 (lastIndex 3)).lo.toRat : ℝ) ≤ 3 / 4 ∧
    (3 / 4 : ℝ) ≤ (closedCell singletonInterval 3 (lastIndex 3)).hi.toRat
  rw [hlo, hhi]
  norm_num

example : Owns singletonInterval 3 (lastIndex 3) (3 / 4 : ℝ) :=
  last_owns_of_mem singleton_mem_lastDepthThree

example : ¬ Owns singletonInterval 3 ⟨0, by norm_num⟩ (3 / 4 : ℝ) := by
  apply not_owns_of_mem_higher (j := lastIndex 3) (by native_decide)
  exact singleton_mem_lastDepthThree

/-! ### Checked addressed frontiers -/

open DyadicSubdivisionTree DyadicFrontier

example : DyadicFrontier.check [[]] = some .leaf := by native_decide

example : DyadicFrontier.check [[false], [true]] =
    some (.split .leaf .leaf) := by
  native_decide

example : DyadicFrontier.check [[false], [true, false], [true, true]] =
    some (.split .leaf (.split .leaf .leaf)) := by
  native_decide

-- Missing branch: not a complete prefix code.
example : DyadicFrontier.check [[false]] = none := by native_decide

-- A leaf cannot coexist with one of its descendants.
example : DyadicFrontier.check [[], [false]] = none := by native_decide

-- Duplicate leaves are rejected.
example : DyadicFrontier.check [[false], [false], [true]] = none := by native_decide

-- The serialized flat format has deterministic left-to-right ordering.
example : DyadicFrontier.check [[true], [false]] = none := by native_decide

example (leaves : List DyadicPath) (tree : DyadicSubdivisionTree)
    (hcheck : DyadicFrontier.check leaves = some tree) (I : IntervalDyadic)
    (x : ℝ) (hx : x ∈ I) :
    ∃ path ∈ leaves, x ∈ path.decodeByBisection I :=
  DyadicFrontier.exists_mem_decode_of_check hcheck I hx

end LeanCert.Test.DyadicSubdivision
