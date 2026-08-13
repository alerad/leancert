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

theorem mem_iff {I J : IntervalDyadic} (h : I.ValueEq J) (x : ℝ) :
    x ∈ I ↔ x ∈ J := by
  simp only [IntervalDyadic.mem_def]
  have hlo : (I.lo.toRat : ℝ) = J.lo.toRat := by exact_mod_cast h.1
  have hhi : (I.hi.toRat : ℝ) = J.hi.toRat := by exact_mod_cast h.2
  rw [hlo, hhi]

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
  let hi := lo.add width
  ⟨lo, hi, by
    change
      (root.lo.add (width.mul (Dyadic.ofInt cell.index.val))).toRat ≤
        ((root.lo.add (width.mul (Dyadic.ofInt cell.index.val))).add width).toRat
    simp only [Dyadic.toRat_add]
    apply le_add_of_nonneg_right
    change 0 ≤ (root.width.scale2 (-(cell.depth : Int))).toRat
    rw [Dyadic.toRat_scale2]
    have hwidth : 0 ≤ root.width.toRat := by
      rw [IntervalDyadic.width_toRat]
      linarith [root.le]
    exact mul_nonneg hwidth (zpow_nonneg (by norm_num) _)⟩

@[simp] theorem step_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.step root).toRat = root.width.toRat * (2 : ℚ) ^ (-(cell.depth : Int)) := by
  simp [step, Dyadic.toRat_scale2]

/-- The exact step at any depth is nonnegative. -/
theorem step_toRat_nonneg (root : IntervalDyadic) (depth : Nat) :
    0 ≤ (root.width.scale2 (-(depth : Int))).toRat := by
  rw [Dyadic.toRat_scale2, IntervalDyadic.width_toRat]
  exact mul_nonneg (sub_nonneg.mpr root.le) (zpow_nonneg (by norm_num) _)

/-- Fixed-depth decoding context with the common cell width prepared once. -/
structure PreparedDyadicLevel where
  root : IntervalDyadic
  depth : Nat
  step : Dyadic
  step_eq : step = root.width.scale2 (-(depth : Int))
  step_nonneg : 0 ≤ step.toRat

namespace PreparedDyadicLevel

/-- Prepare the shared arithmetic for every cell at one subdivision depth. -/
def prepare (root : IntervalDyadic) (depth : Nat) : PreparedDyadicLevel := {
  root
  depth
  step := root.width.scale2 (-(depth : Int))
  step_eq := rfl
  step_nonneg := step_toRat_nonneg root depth
}

/-- Number of cells at the prepared level. -/
def cellCount (level : PreparedDyadicLevel) : Nat := 2 ^ level.depth

/-- Random-access decoding using the shared precomputed cell width. -/
def intervalAt (level : PreparedDyadicLevel) (index : Fin level.cellCount) : IntervalDyadic :=
  let lo := level.root.lo.add (level.step.mul (Dyadic.ofInt index.val))
  let hi := lo.add level.step
  ⟨lo, hi, by
    change
      (level.root.lo.add (level.step.mul (Dyadic.ofInt index.val))).toRat ≤
        ((level.root.lo.add (level.step.mul (Dyadic.ofInt index.val))).add level.step).toRat
    simp only [Dyadic.toRat_add]
    exact le_add_of_nonneg_right level.step_nonneg⟩

@[simp] theorem intervalAt_lo_toRat (level : PreparedDyadicLevel)
    (index : Fin level.cellCount) :
    (level.intervalAt index).lo.toRat =
      level.root.lo.toRat + level.step.toRat * index.val := by
  simp [intervalAt, Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]

@[simp] theorem intervalAt_hi_toRat (level : PreparedDyadicLevel)
    (index : Fin level.cellCount) :
    (level.intervalAt index).hi.toRat =
      level.root.lo.toRat + level.step.toRat * (index.val + 1) := by
  simp [intervalAt, Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]
  ring

/-- Prepared random access agrees with the original direct decoder. -/
theorem intervalAt_valueEq_decodeDirect (level : PreparedDyadicLevel)
    (index : Fin level.cellCount) :
    (level.intervalAt index).ValueEq
      ((DyadicCell.mk level.depth index).decodeDirect level.root) := by
  constructor
  · change
      (level.root.lo.add (level.step.mul (Dyadic.ofInt index.val))).toRat =
        (level.root.lo.add
          ((level.root.width.scale2 (-(level.depth : Int))).mul
            (Dyadic.ofInt index.val))).toRat
    rw [level.step_eq]
  · change
      ((level.root.lo.add (level.step.mul (Dyadic.ofInt index.val))).add level.step).toRat =
        ((level.root.lo.add
          ((level.root.width.scale2 (-(level.depth : Int))).mul
            (Dyadic.ofInt index.val))).add
              (level.root.width.scale2 (-(level.depth : Int)))).toRat
    rw [level.step_eq]

/-- Build adjacent cells with one endpoint addition per cell. -/
private def materializeFrom (level : PreparedDyadicLevel) : Nat → Dyadic → List IntervalDyadic
  | 0, _ => []
  | count + 1, lo =>
      let hi := lo.add level.step
      ⟨lo, hi, by
        change lo.toRat ≤ (lo.add level.step).toRat
        rw [Dyadic.toRat_add]
        exact le_add_of_nonneg_right level.step_nonneg⟩ ::
        materializeFrom level count hi

/-- Materialize a complete fixed-depth level by advancing adjacent endpoints. -/
def materialize (level : PreparedDyadicLevel) : List IntervalDyadic :=
  materializeFrom level level.cellCount level.root.lo

@[simp] theorem materializeFrom_length (level : PreparedDyadicLevel) (count : Nat) (lo : Dyadic) :
    (materializeFrom level count lo).length = count := by
  induction count generalizing lo with
  | zero => rfl
  | succ count ih => simp [materializeFrom, ih]

@[simp] theorem materialize_length (level : PreparedDyadicLevel) :
    level.materialize.length = level.cellCount := by
  simp [materialize]

end PreparedDyadicLevel

@[simp] theorem decodeDirect_lo_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.decodeDirect root).lo.toRat =
      root.lo.toRat + (cell.step root).toRat * cell.index.val := by
  simp [decodeDirect, Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]

@[simp] theorem decodeDirect_hi_toRat (root : IntervalDyadic) (cell : DyadicCell) :
    (cell.decodeDirect root).hi.toRat =
      root.lo.toRat + (cell.step root).toRat * (cell.index.val + 1) := by
  simp [decodeDirect, Dyadic.toRat_add, Dyadic.toRat_mul, Dyadic.toRat_ofInt]
  ring

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

/-! ### Closed proof semantics and canonical ownership -/

namespace Ownership

/-- The closed proof cell at a fixed level. This is the interval supplied to
certified numerical evaluation. -/
def closedCell (root : IntervalDyadic) (depth : Nat) (index : Fin (2 ^ depth)) :
    IntervalDyadic :=
  (PreparedDyadicLevel.prepare root depth).intervalAt index

/-- Canonical ownership assigns a point to the greatest-index closed cell that
contains it. Thus an interior seam belongs to the cell on its right, matching
the half-open convention `[lo, hi)`, while the final cell retains the root's
right endpoint. -/
def Owns (root : IntervalDyadic) (depth : Nat) (index : Fin (2 ^ depth)) (x : ℝ) : Prop :=
  x ∈ closedCell root depth index ∧
    ∀ other : Fin (2 ^ depth), x ∈ closedCell root depth other → other ≤ index

/-- The set canonically owned by one fixed-depth cell. -/
def ownerSet (root : IntervalDyadic) (depth : Nat) (index : Fin (2 ^ depth)) : Set ℝ :=
  {x | Owns root depth index x}

/-- The final index of a nonempty dyadic level. -/
def lastIndex (depth : Nat) : Fin (2 ^ depth) :=
  ⟨2 ^ depth - 1, Nat.sub_lt (by positivity) (by norm_num)⟩

/-- Canonical ownership never enlarges the closed proof cell. -/
theorem ownerSet_subset_closedCell (root : IntervalDyadic) (depth : Nat)
    (index : Fin (2 ^ depth)) :
    ownerSet root depth index ⊆ (closedCell root depth index).toSet := by
  intro x hx
  exact hx.1

/-- Distinct cells cannot canonically own the same point. -/
theorem ownerSet_disjoint {root : IntervalDyadic} {depth : Nat}
    {i j : Fin (2 ^ depth)} (hne : i ≠ j) :
    Disjoint (ownerSet root depth i) (ownerSet root depth j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hji : j ≤ i := hxi.2 j hxj.1
  have hij : i ≤ j := hxj.2 i hxi.1
  exact hne (le_antisymm hij hji)

/-- A point contained in a higher-index cell cannot be owned by a lower cell.
This is the abstract seam-welding rule. -/
theorem not_owns_of_mem_higher {root : IntervalDyadic} {depth : Nat}
    {i j : Fin (2 ^ depth)} {x : ℝ} (hij : i < j)
    (hj : x ∈ closedCell root depth j) :
    ¬ Owns root depth i x := by
  intro hi
  exact (not_le_of_gt hij) (hi.2 j hj)

/-- Any point in the final closed cell is owned by that cell. In particular,
the root's right endpoint remains owned rather than being discarded. -/
theorem last_owns_of_mem {root : IntervalDyadic} {depth : Nat} {x : ℝ}
    (hx : x ∈ closedCell root depth (lastIndex depth)) :
    Owns root depth (lastIndex depth) x := by
  refine ⟨hx, ?_⟩
  intro other _
  apply Fin.le_iff_val_le_val.mpr
  simp only [lastIndex]
  omega

private theorem exists_path_mem (root : IntervalDyadic) (depth : Nat) {x : ℝ}
    (hx : x ∈ root) :
    ∃ path : DyadicPath, path.length = depth ∧ x ∈ path.decodeByBisection root := by
  induction depth generalizing root with
  | zero => exact ⟨[], rfl, hx⟩
  | succ depth ih =>
      rcases IntervalDyadic.mem_bisect_or hx with hleft | hright
      · obtain ⟨path, hlen, hmem⟩ := ih (root := root.bisect.1) hleft
        exact ⟨false :: path, by simp [hlen], by simpa [DyadicPath.decodeByBisection] using hmem⟩
      · obtain ⟨path, hlen, hmem⟩ := ih (root := root.bisect.2) hright
        exact ⟨true :: path, by simp [hlen], by simpa [DyadicPath.decodeByBisection] using hmem⟩

/-- Every point of the root lies in at least one fixed-depth closed proof cell. -/
theorem exists_mem_closedCell (root : IntervalDyadic) (depth : Nat) {x : ℝ}
    (hx : x ∈ root) :
    ∃ index : Fin (2 ^ depth), x ∈ closedCell root depth index := by
  obtain ⟨path, hlen, hmem⟩ := exists_path_mem root depth hx
  subst depth
  let index : Fin (2 ^ path.length) := (ofPath path).index
  refine ⟨index, ?_⟩
  have hrecursive :
      (path.decodeByBisection root).ValueEq ((ofPath path).decodeDirect root) :=
    decodeByBisection_valueEq_decodeDirect root path
  have hprepared :
      ((PreparedDyadicLevel.prepare root path.length).intervalAt index).ValueEq
        ((ofPath path).decodeDirect root) := by
    apply PreparedDyadicLevel.intervalAt_valueEq_decodeDirect
  exact (hprepared.mem_iff x).mpr ((hrecursive.mem_iff x).mp hmem)

/-- Every root point has a unique canonical owner at each fixed depth. -/
theorem exists_unique_owner (root : IntervalDyadic) (depth : Nat) {x : ℝ}
    (hx : x ∈ root) :
    ∃! index : Fin (2 ^ depth), Owns root depth index x := by
  classical
  obtain ⟨someIndex, hsome⟩ := exists_mem_closedCell root depth hx
  let candidates := Finset.univ.filter fun index : Fin (2 ^ depth) =>
    x ∈ closedCell root depth index
  have hcandidates : candidates.Nonempty := by
    exact Finset.filter_nonempty_iff.mpr ⟨someIndex, Finset.mem_univ _, hsome⟩
  let owner := candidates.max' hcandidates
  have hownerMem : x ∈ closedCell root depth owner := by
    exact (Finset.mem_filter.mp (candidates.max'_mem hcandidates)).2
  refine ⟨owner, ⟨hownerMem, ?_⟩, ?_⟩
  · intro other hother
    apply candidates.le_max'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩
  · intro other hother
    exact le_antisymm ((by
      apply candidates.le_max'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother.1⟩) : other ≤ owner)
      (hother.2 owner hownerMem)

/-- Canonical ownership covers the entire root interval. -/
theorem mem_ownerSet_of_mem_root (root : IntervalDyadic) (depth : Nat) {x : ℝ}
    (hx : x ∈ root) :
    ∃ index : Fin (2 ^ depth), x ∈ ownerSet root depth index := by
  obtain ⟨index, hindex, _⟩ := exists_unique_owner root depth hx
  exact ⟨index, hindex⟩

end Ownership

end DyadicCell

end LeanCert.Core
