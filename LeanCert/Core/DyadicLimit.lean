/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicCell
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Infinite dyadic paths

An infinite Boolean history determines a nested sequence of exact closed
dyadic cells. Their widths tend to zero, so their intersection contains exactly
one real point. This is the limit semantics behind finite dyadic addresses.
-/

namespace LeanCert.Core

/-- An infinite sequence of left (`false`) and right (`true`) decisions. -/
abbrev InfiniteDyadicPath := Nat → Bool

namespace InfiniteDyadicPath

/-- The finite address consisting of the first `depth` decisions. -/
def finitePrefix (bits : InfiniteDyadicPath) : Nat → DyadicPath
  | 0 => []
  | depth + 1 => finitePrefix bits depth ++ [bits depth]

/-- The closed cell reached after the first `depth` decisions. -/
def cell (root : IntervalDyadic) (bits : InfiniteDyadicPath) : Nat → IntervalDyadic
  | 0 => root
  | depth + 1 =>
      if bits depth then (cell root bits depth).bisect.2
      else (cell root bits depth).bisect.1

@[simp] theorem finitePrefix_zero (bits : InfiniteDyadicPath) : bits.finitePrefix 0 = [] := rfl

@[simp] theorem finitePrefix_succ (bits : InfiniteDyadicPath) (depth : Nat) :
    bits.finitePrefix (depth + 1) = bits.finitePrefix depth ++ [bits depth] := rfl

@[simp] theorem cell_zero (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    bits.cell root 0 = root := rfl

@[simp] theorem cell_succ (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) :
    bits.cell root (depth + 1) =
      if bits depth then (bits.cell root depth).bisect.2
      else (bits.cell root depth).bisect.1 := rfl

/-- Infinite-path decoding agrees with recursive finite-address decoding at
every finite depth. -/
theorem cell_eq_decode_finitePrefix (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) :
    bits.cell root depth = (bits.finitePrefix depth).decodeByBisection root := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [cell_succ, finitePrefix_succ]
      cases hbit : bits depth
      · simp only [Bool.false_eq_true, ↓reduceIte,
          DyadicPath.decodeByBisection_append_false, ih]
      · simp only [↓reduceIte, DyadicPath.decodeByBisection_append_true, ih]

/-- Every successor cell is contained in its predecessor. -/
theorem mem_cell_of_mem_succ {root : IntervalDyadic} {bits : InfiniteDyadicPath}
    {depth : Nat} {x : ℝ} (hx : x ∈ bits.cell root (depth + 1)) :
    x ∈ bits.cell root depth := by
  rw [cell_succ] at hx
  split at hx
  · exact IntervalDyadic.mem_of_mem_bisect_right hx
  · exact IntervalDyadic.mem_of_mem_bisect_left hx

/-- Exact semantic width after `depth` binary refinements. -/
theorem cell_width_toRat (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) :
    (bits.cell root depth).width.toRat = root.width.toRat * (1 / 2 : ℚ) ^ depth := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [cell_succ]
      split
      · rw [IntervalDyadic.bisect_right_width_toRat, ih, pow_succ]
        ring
      · rw [IntervalDyadic.bisect_left_width_toRat, ih, pow_succ]
        ring

/-- Cell widths along every infinite history converge to zero. -/
theorem cell_width_tendsto_zero (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    Filter.Tendsto (fun depth => ((bits.cell root depth).width.toRat : ℝ))
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun depth : Nat => (1 / 2 : ℝ) ^ depth)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul : Filter.Tendsto
      (fun depth : Nat => (root.width.toRat : ℝ) * (1 / 2 : ℝ) ^ depth)
      Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul (root.width.toRat : ℝ)
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun depth => by
    change (root.width.toRat : ℝ) * (1 / 2 : ℝ) ^ depth =
      ((bits.cell root depth).width.toRat : ℝ)
    rw [cell_width_toRat]
    norm_num

/-- The ordinary real endpoint width also converges to zero. -/
theorem cell_real_width_tendsto_zero (root : IntervalDyadic)
    (bits : InfiniteDyadicPath) :
    Filter.Tendsto
      (fun depth => (bits.cell root depth).hi.toReal -
        (bits.cell root depth).lo.toReal)
      Filter.atTop (nhds 0) := by
  apply (cell_width_tendsto_zero root bits).congr'
  exact Filter.Eventually.of_forall fun depth => by
    change ((bits.cell root depth).width.toRat : ℝ) =
      (bits.cell root depth).hi.toReal - (bits.cell root depth).lo.toReal
    rw [IntervalDyadic.width_toRat]
    simp only [Dyadic.toReal, Rat.cast_sub]

/-- Each closed cell is nonempty. -/
theorem cell_nonempty (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) : (bits.cell root depth).toSet.Nonempty := by
  rw [IntervalDyadic.toSet, Set.nonempty_Icc]
  change ((bits.cell root depth).lo.toRat : ℝ) ≤
    ((bits.cell root depth).hi.toRat : ℝ)
  exact_mod_cast (bits.cell root depth).le

/-- The nested closed cells along an infinite path have a common point. -/
theorem intersection_nonempty (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    (⋂ depth, (bits.cell root depth).toSet).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro depth x hx
    exact mem_cell_of_mem_succ hx
  · exact cell_nonempty root bits
  · simpa [IntervalDyadic.toSet] using
      (isCompact_Icc : IsCompact (Set.Icc (root.lo : ℝ) root.hi))
  · intro depth
    exact isClosed_Icc

/-- The intersection of all cells on one path contains at most one point. -/
theorem intersection_subsingleton (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    (⋂ depth, (bits.cell root depth).toSet).Subsingleton := by
  intro x hx y hy
  have hdist : ∀ depth,
      dist x y ≤ ((bits.cell root depth).width.toRat : ℝ) := by
    intro depth
    have hxCell := Set.mem_iInter.mp hx depth
    have hyCell := Set.mem_iInter.mp hy depth
    have h := Real.dist_le_of_mem_Icc hxCell hyCell
    simpa [IntervalDyadic.toSet, IntervalDyadic.width_toRat, Dyadic.toReal] using h
  have hzero : dist x y ≤ 0 :=
    ge_of_tendsto' (cell_width_tendsto_zero root bits) hdist
  exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)

/-- Every infinite dyadic history denotes exactly one real point. -/
theorem exists_unique_limit (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    ∃! x : ℝ, ∀ depth, x ∈ bits.cell root depth := by
  obtain ⟨x, hx⟩ := intersection_nonempty root bits
  refine ⟨x, Set.mem_iInter.mp hx, ?_⟩
  intro y hy
  exact intersection_subsingleton root bits (Set.mem_iInter.mpr hy) hx

/-- The real point decoded by an infinite history. -/
noncomputable def decode (root : IntervalDyadic) (bits : InfiniteDyadicPath) : ℝ :=
  Classical.choose (exists_unique_limit root bits)

/-- The decoded point belongs to every finite prefix cell. -/
theorem decode_mem_cell (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) : bits.decode root ∈ bits.cell root depth :=
  (Classical.choose_spec (exists_unique_limit root bits)).1 depth

/-- Any choice of representatives from the nested cells converges to the point
decoded by the history. -/
theorem tendsto_decode_of_mem_cell (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (points : Nat → ℝ) (hpoints : ∀ depth, points depth ∈ bits.cell root depth) :
    Filter.Tendsto points Filter.atTop (nhds (bits.decode root)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero
  · exact fun _ => dist_nonneg
  · intro depth
    have h := Real.dist_le_of_mem_Icc (hpoints depth) (decode_mem_cell root bits depth)
    simpa [IntervalDyadic.toSet, Dyadic.toReal] using h
  · exact cell_real_width_tendsto_zero root bits

end InfiniteDyadicPath

end LeanCert.Core
