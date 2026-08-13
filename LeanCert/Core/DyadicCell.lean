/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalDyadic

/-!
# Finite dyadic addresses

Finite Boolean paths are convenient for adaptive provenance. Indexed cells are
convenient for fixed-depth arithmetic, serialization, and integration. This
module provides both views and exact decoding into closed dyadic intervals.
-/

namespace LeanCert.Core

namespace IntervalDyadic

/-- Semantic equality of dyadic intervals, independent of endpoint representation. -/
def ValueEq (I J : IntervalDyadic) : Prop :=
  I.lo.toRat = J.lo.toRat ∧ I.hi.toRat = J.hi.toRat

namespace ValueEq

@[refl] theorem refl (I : IntervalDyadic) : I.ValueEq I := ⟨rfl, rfl⟩

theorem symm {I J : IntervalDyadic} (h : I.ValueEq J) : J.ValueEq I :=
  ⟨h.1.symm, h.2.symm⟩

theorem trans {I J K : IntervalDyadic} (hIJ : I.ValueEq J) (hJK : J.ValueEq K) :
    I.ValueEq K := ⟨hIJ.1.trans hJK.1, hIJ.2.trans hJK.2⟩

end ValueEq

end IntervalDyadic

/-- A finite sequence of left (`false`) and right (`true`) decisions. -/
abbrev DyadicPath := List Bool

namespace DyadicPath

/-- The ordinary binary integer encoded by a path, most-significant bit first. -/
def index : DyadicPath → Nat
  | [] => 0
  | bit :: rest => (if bit then 2 ^ rest.length else 0) + index rest

/-- A finite binary path always denotes an index at its depth. -/
theorem index_lt_pow_length (path : DyadicPath) : path.index < 2 ^ path.length := by
  induction path with
  | nil => simp [index]
  | cons bit rest ih =>
      cases bit <;> simp [index, pow_succ] <;> omega

@[simp] theorem index_append_false (path : DyadicPath) :
    (path ++ [false]).index = 2 * path.index := by
  induction path with
  | nil => simp [index]
  | cons bit rest ih =>
      cases bit <;> simp [index, ih, pow_succ] <;> omega

@[simp] theorem index_append_true (path : DyadicPath) :
    (path ++ [true]).index = 2 * path.index + 1 := by
  induction path with
  | nil => simp [index]
  | cons bit rest ih =>
      cases bit <;> simp [index, ih, pow_succ] <;> omega

/-- Decode a path operationally by following exact interval bisections. -/
def decodeByBisection (root : IntervalDyadic) : DyadicPath → IntervalDyadic
  | [] => root
  | bit :: rest =>
      let children := root.bisect
      decodeByBisection (if bit then children.2 else children.1) rest

@[simp] theorem decodeByBisection_append_false (root : IntervalDyadic) (path : DyadicPath) :
    decodeByBisection root (path ++ [false]) = (decodeByBisection root path).bisect.1 := by
  induction path generalizing root with
  | nil => simp [decodeByBisection]
  | cons bit rest ih => cases bit <;> simp [decodeByBisection, ih]

@[simp] theorem decodeByBisection_append_true (root : IntervalDyadic) (path : DyadicPath) :
    decodeByBisection root (path ++ [true]) = (decodeByBisection root path).bisect.2 := by
  induction path generalizing root with
  | nil => simp [decodeByBisection]
  | cons bit rest ih => cases bit <;> simp [decodeByBisection, ih]

end DyadicPath

/-- A fixed-depth dyadic cell, with its index bounded by the number of cells. -/
structure DyadicCell where
  depth : Nat
  index : Fin (2 ^ depth)
  deriving Repr, DecidableEq

namespace DyadicCell

/-- Cells are equal when their depths and numeric indices agree. -/
@[ext] theorem ext' {a b : DyadicCell} (hdepth : a.depth = b.depth)
    (hindex : a.index.val = b.index.val) : a = b := by
  cases a with
  | mk da ia =>
      cases b with
      | mk db ib =>
          simp only at hdepth hindex
          subst db
          congr
          exact Fin.ext hindex

/-- The root cell at depth zero. -/
def root : DyadicCell := ⟨0, ⟨0, by norm_num⟩⟩

/-- The left child has index `2k`. -/
def childLeft (cell : DyadicCell) : DyadicCell :=
  ⟨cell.depth + 1, ⟨2 * cell.index, by
    rw [pow_succ]
    omega⟩⟩

/-- The right child has index `2k + 1`. -/
def childRight (cell : DyadicCell) : DyadicCell :=
  ⟨cell.depth + 1, ⟨2 * cell.index + 1, by
    rw [pow_succ]
    omega⟩⟩

@[simp] theorem childLeft_depth (cell : DyadicCell) :
    cell.childLeft.depth = cell.depth + 1 := rfl

@[simp] theorem childRight_depth (cell : DyadicCell) :
    cell.childRight.depth = cell.depth + 1 := rfl

@[simp] theorem childLeft_index (cell : DyadicCell) :
    cell.childLeft.index.val = 2 * cell.index.val := rfl

@[simp] theorem childRight_index (cell : DyadicCell) :
    cell.childRight.index.val = 2 * cell.index.val + 1 := rfl

/-- Convert a path into the corresponding bounded fixed-depth cell. -/
def ofPath (path : DyadicPath) : DyadicCell :=
  ⟨path.length, ⟨path.index, path.index_lt_pow_length⟩⟩

@[simp] theorem ofPath_depth (path : DyadicPath) :
    (ofPath path).depth = path.length := rfl

@[simp] theorem ofPath_index (path : DyadicPath) :
    (ofPath path).index.val = path.index := rfl

@[simp] theorem ofPath_append_false (path : DyadicPath) :
    ofPath (path ++ [false]) = (ofPath path).childLeft := by
  apply ext'
  · simp
  · simp

@[simp] theorem ofPath_append_true (path : DyadicPath) :
    ofPath (path ++ [true]) = (ofPath path).childRight := by
  apply ext'
  · simp
  · simp

/-- Exact width of one cell at this depth. -/
def step (root : IntervalDyadic) (cell : DyadicCell) : Dyadic :=
  root.width.scale2 (-(cell.depth : Int))

/-- Decode an indexed cell directly from its affine endpoint formula. -/
def decodeDirect (root : IntervalDyadic) (cell : DyadicCell) : IntervalDyadic :=
  let width := cell.step root
  let lo := root.lo.add (width.mul (Dyadic.ofInt cell.index.val))
  let hi := root.lo.add (width.mul (Dyadic.ofInt (cell.index.val + 1)))
  ⟨lo, hi, by
    change
      (root.lo.add (width.mul (Dyadic.ofInt cell.index.val))).toRat ≤
        (root.lo.add (width.mul (Dyadic.ofInt (cell.index.val + 1)))).toRat
    simp only [Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast Nat.le_succ cell.index.val
    · change 0 ≤ (root.width.scale2 (-(cell.depth : Int))).toRat
      rw [Dyadic.toRat_scale2]
      have hwidth : 0 ≤ root.width.toRat := by
        rw [IntervalDyadic.width_toRat]
        linarith [root.le]
      exact mul_nonneg hwidth (zpow_nonneg (by norm_num) _)⟩

@[simp] theorem step_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.step root).toRat = root.width.toRat * (2 : ℚ) ^ (-(cell.depth : Int)) := by
  simp [step, Dyadic.toRat_scale2]

@[simp] theorem decodeDirect_lo_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.decodeDirect root).lo.toRat =
      root.lo.toRat + (cell.step root).toRat * cell.index.val := by
  simp [decodeDirect, Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]

@[simp] theorem decodeDirect_hi_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.decodeDirect root).hi.toRat =
      root.lo.toRat + (cell.step root).toRat * (cell.index.val + 1) := by
  simp [decodeDirect, Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]

/-- Direct decoding gives every depth-`n` cell the root width divided by `2^n`. -/
theorem decodeDirect_width_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.decodeDirect root).width.toRat = (cell.step root).toRat := by
  rw [IntervalDyadic.width_toRat, decodeDirect_hi_toRat, decodeDirect_lo_toRat]
  ring

theorem childLeft_step_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.childLeft.step root).toRat = (cell.step root).toRat / 2 := by
  rw [step_toRat, step_toRat]
  rw [childLeft_depth]
  have hexp : -((cell.depth + 1 : Nat) : Int) = -(cell.depth : Int) - 1 := by omega
  rw [hexp, zpow_sub_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num
  ring

theorem childRight_step_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.childRight.step root).toRat = (cell.step root).toRat / 2 := by
  rw [step_toRat, step_toRat]
  rw [childRight_depth]
  have hexp : -((cell.depth + 1 : Nat) : Int) = -(cell.depth : Int) - 1 := by omega
  rw [hexp, zpow_sub_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num
  ring

/-- Directly decoding the left child agrees semantically with bisecting the parent. -/
theorem decodeDirect_childLeft (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.childLeft.decodeDirect root).ValueEq (cell.decodeDirect root).bisect.1 := by
  constructor
  · change (cell.childLeft.decodeDirect root).lo.toRat =
        (cell.decodeDirect root).lo.toRat
    rw [decodeDirect_lo_toRat, decodeDirect_lo_toRat, childLeft_step_toRat,
      childLeft_index]
    push_cast
    ring
  · change (cell.childLeft.decodeDirect root).hi.toRat =
        (cell.decodeDirect root).midpoint.toRat
    rw [decodeDirect_hi_toRat, IntervalDyadic.midpoint_toRat,
      decodeDirect_lo_toRat, decodeDirect_hi_toRat, childLeft_step_toRat,
      childLeft_index]
    push_cast
    ring

/-- Directly decoding the right child agrees semantically with bisecting the parent. -/
theorem decodeDirect_childRight (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.childRight.decodeDirect root).ValueEq (cell.decodeDirect root).bisect.2 := by
  constructor
  · change (cell.childRight.decodeDirect root).lo.toRat =
        (cell.decodeDirect root).midpoint.toRat
    rw [decodeDirect_lo_toRat, IntervalDyadic.midpoint_toRat,
      decodeDirect_lo_toRat, decodeDirect_hi_toRat, childRight_step_toRat,
      childRight_index]
    push_cast
    ring
  · change (cell.childRight.decodeDirect root).hi.toRat =
        (cell.decodeDirect root).hi.toRat
    rw [decodeDirect_hi_toRat, decodeDirect_hi_toRat, childRight_step_toRat,
      childRight_index]
    push_cast
    ring

theorem valueEq_bisect_left {I J : IntervalDyadic} (h : I.ValueEq J) :
    I.bisect.1.ValueEq J.bisect.1 := by
  constructor
  · exact h.1
  · change I.midpoint.toRat = J.midpoint.toRat
    rw [IntervalDyadic.midpoint_toRat, IntervalDyadic.midpoint_toRat, h.1, h.2]

theorem valueEq_bisect_right {I J : IntervalDyadic} (h : I.ValueEq J) :
    I.bisect.2.ValueEq J.bisect.2 := by
  constructor
  · change I.midpoint.toRat = J.midpoint.toRat
    rw [IntervalDyadic.midpoint_toRat, IntervalDyadic.midpoint_toRat, h.1, h.2]
  · exact h.2

theorem decodeDirect_root (root : IntervalDyadic) :
    (DyadicCell.root.decodeDirect root).ValueEq root := by
  constructor
  · simp [DyadicCell.root]
  · rw [decodeDirect_hi_toRat]
    simp only [DyadicCell.root, step, Dyadic.toRat_scale2, IntervalDyadic.width_toRat]
    norm_num

/-- Recursive bisection and direct affine decoding agree at every finite address. -/
theorem decodeByBisection_valueEq_decodeDirect (root : IntervalDyadic) (path : DyadicPath) :
    (path.decodeByBisection root).ValueEq ((ofPath path).decodeDirect root) := by
  induction path using List.reverseRecOn with
  | nil => exact (decodeDirect_root root).symm
  | append_singleton path bit ih =>
      cases bit
      · rw [DyadicPath.decodeByBisection_append_false, ofPath_append_false]
        exact (valueEq_bisect_left ih).trans (decodeDirect_childLeft root (ofPath path)).symm
      · rw [DyadicPath.decodeByBisection_append_true, ofPath_append_true]
        exact (valueEq_bisect_right ih).trans (decodeDirect_childRight root (ofPath path)).symm

end DyadicCell

end LeanCert.Core
