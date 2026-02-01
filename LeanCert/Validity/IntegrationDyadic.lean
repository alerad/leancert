/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.Integrate

/-!
# Dyadic Interval Integration

High-performance integration using Dyadic interval arithmetic.

This module provides a drop-in replacement for the rational `integratePartitionWithInv`
that uses `evalIntervalDyadic` instead of `evalInterval?`. Since `evalIntervalDyadic` is
total (returns wide bounds on domain violations rather than `none`), the integration
functions are also total — domain violations manifest as wide bounds that cause the
checker to return `false`, which is safe for the `native_decide` workflow.

## Performance

Dyadic arithmetic avoids GCD normalization overhead that dominates rational arithmetic
for complex expressions. Expected 10-50x speedup for expressions with deep
transcendental nesting (like the Li2 integrand).
-/

open MeasureTheory
open LeanCert.Core
open LeanCert.Engine

namespace LeanCert.Validity.IntegrationDyadic

/-! ### Single-interval integration -/

/-- Evaluate expression on a single `IntervalRat` subinterval using the Dyadic backend.
    Converts the rational interval to Dyadic, evaluates, converts result back to Rat. -/
def evalDyadic1 (e : Expr) (I : IntervalRat) (cfg : DyadicConfig := {}) : IntervalRat :=
  let Idyad := IntervalDyadic.ofIntervalRat I cfg.precision
  (evalIntervalDyadic e (fun _ => Idyad) cfg).toIntervalRat

/-- Single-interval integration using Dyadic evaluation.
    Returns `width(I) × evalDyadic1(e, I)` as a rational interval. -/
def integrateInterval1Dyadic (e : Expr) (I : IntervalRat) (cfg : DyadicConfig := {}) : IntervalRat :=
  IntervalRat.mul (IntervalRat.singleton I.width) (evalDyadic1 e I cfg)

/-- Correctness of single-interval Dyadic integration.
    If domain validity holds, the integral is contained in the computed bound. -/
theorem integrateInterval1Dyadic_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat I cfg.precision) cfg)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
      integrateInterval1Dyadic e I cfg := by
  -- Get bounds from Dyadic evaluation
  set J := evalDyadic1 e I cfg with hJ_def
  have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ J := by
    intro x hx
    have hmem_dyad : x ∈ IntervalDyadic.ofIntervalRat I cfg.precision :=
      IntervalDyadic.mem_ofIntervalRat hx cfg.precision hprec
    have henv : envMemDyadic (fun _ => x) (fun _ => IntervalDyadic.ofIntervalRat I cfg.precision) :=
      fun _ => hmem_dyad
    have heval := evalIntervalDyadic_correct_withInv e hsupp _ _ henv cfg hprec hdom
    show Expr.eval (fun _ => x) e ∈ J
    simp only [hJ_def, evalDyadic1]
    exact IntervalDyadic.mem_toIntervalRat.mpr heval
  have hlo : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ),
      (J.lo : ℝ) ≤ Expr.eval (fun _ => x) e := by
    intro x hx; exact (hbounds x hx).1
  have hhi : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ),
      Expr.eval (fun _ => x) e ≤ (J.hi : ℝ) := by
    intro x hx; exact (hbounds x hx).2
  have hIle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have ⟨h_lower, h_upper⟩ := LeanCert.Engine.integral_bounds_of_bounds hIle hInt hlo hhi
  have hwidth : (I.width : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
    simp only [IntervalRat.width, Rat.cast_sub]
  have hwidth_nn : (0 : ℝ) ≤ I.width := by exact_mod_cast IntervalRat.width_nonneg I
  have hJ_le : (J.lo : ℝ) ≤ J.hi := by exact_mod_cast J.le
  have h_lo' : (I.width : ℝ) * J.lo ≤
      ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := by
    calc (I.width : ℝ) * J.lo = J.lo * I.width := by ring
       _ = J.lo * ((I.hi : ℝ) - I.lo) := by rw [hwidth]
       _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lower
  have h_hi' : ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e ≤
      (I.width : ℝ) * J.hi := by
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
       ≤ J.hi * ((I.hi : ℝ) - I.lo) := h_upper
     _ = J.hi * I.width := by rw [hwidth]
     _ = (I.width : ℝ) * J.hi := by ring
  have h1 : (I.width : ℝ) * J.lo ≤ I.width * J.hi :=
    mul_le_mul_of_nonneg_left hJ_le hwidth_nn
  show ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Dyadic e I cfg
  simp only [integrateInterval1Dyadic, ← hJ_def, IntervalRat.mem_def]
  constructor
  · have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) J).lo =
        min (min (I.width * J.lo) (I.width * J.hi))
            (min (I.width * J.lo) (I.width * J.hi)) := rfl
    simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
    calc (↑I.width * ↑J.lo) ⊓ (↑I.width * ↑J.hi)
        = ↑I.width * ↑J.lo := min_eq_left h1
      _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lo'
  · have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) J).hi =
        max (max (I.width * J.lo) (I.width * J.hi))
            (max (I.width * J.lo) (I.width * J.hi)) := rfl
    simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
        ≤ ↑I.width * ↑J.hi := h_hi'
      _ = (↑I.width * ↑J.lo) ⊔ (↑I.width * ↑J.hi) := (max_eq_right h1).symm

/-! ### Partitioned integration -/

/-- Collect per-subinterval Dyadic integration bounds. Total (no Option). -/
def collectBoundsDyadic (e : Expr) (parts : List IntervalRat)
    (cfg : DyadicConfig := {}) : List IntervalRat :=
  parts.map (integrateInterval1Dyadic e · cfg)

/-- Sum bounds over a uniform partition using Dyadic evaluation. Total (no Option). -/
def integratePartitionDyadic (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : DyadicConfig := {}) : IntervalRat :=
  let parts := uniformPartition I n hn
  let bounds := collectBoundsDyadic e parts cfg
  bounds.foldl IntervalRat.add (IntervalRat.singleton 0)

/-! ### Domain validity -/

/-- Domain validity for all subintervals in a partition. -/
def partitionDomainValid (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : DyadicConfig) : Prop :=
  ∀ k (hk : k < n),
    let Ik := (uniformPartition I n hn)[k]'(by simp [uniformPartition]; exact hk)
    evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat Ik cfg.precision) cfg

/-- Computable check for partition domain validity. -/
def checkPartitionDomainValid (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : DyadicConfig) : Bool :=
  (uniformPartition I n hn).all fun Ik =>
    checkDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat Ik cfg.precision) cfg

theorem checkPartitionDomainValid_correct (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : DyadicConfig) :
    checkPartitionDomainValid e I n hn cfg = true → partitionDomainValid e I n hn cfg := by
  intro hcheck k hk
  unfold checkPartitionDomainValid at hcheck
  rw [List.all_eq_true] at hcheck
  set parts := uniformPartition I n hn with hparts
  have hk' : k < parts.length := by simp [hparts, uniformPartition]; exact hk
  have hmem : parts[k] ∈ parts := List.getElem_mem hk'
  have := hcheck _ hmem
  exact checkDomainValidDyadic_correct _ _ _ this

/-! ### Boolean checkers for native_decide -/

/-- Boolean checker for integral lower bounds using Dyadic evaluation. -/
def checkIntegralLowerBoundDyadic (e : Expr) (I : IntervalRat) (n : ℕ)
    (c : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  if hn : 0 < n then
    decide (c ≤ (integratePartitionDyadic e I n hn cfg).lo)
  else
    false

/-- Boolean checker for integral upper bounds using Dyadic evaluation. -/
def checkIntegralUpperBoundDyadic (e : Expr) (I : IntervalRat) (n : ℕ)
    (c : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  if hn : 0 < n then
    decide ((integratePartitionDyadic e I n hn cfg).hi ≤ c)
  else
    false

/-- Combined checker: verifies both domain validity and integral lower bound.
    This allows a single `native_decide` call. -/
def checkIntegralLowerBoundDyadicFull (e : Expr) (I : IntervalRat) (n : ℕ)
    (c : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  if hn : 0 < n then
    checkPartitionDomainValid e I n hn cfg &&
    decide (c ≤ (integratePartitionDyadic e I n hn cfg).lo)
  else
    false

/-- Combined checker: verifies both domain validity and integral upper bound. -/
def checkIntegralUpperBoundDyadicFull (e : Expr) (I : IntervalRat) (n : ℕ)
    (c : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  if hn : 0 < n then
    checkPartitionDomainValid e I n hn cfg &&
    decide ((integratePartitionDyadic e I n hn cfg).hi ≤ c)
  else
    false

/-! ### Bridge lemmas -/

private theorem integral_mem_bound_dyadic (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hdomall : partitionDomainValid e I n hn cfg)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
      integratePartitionDyadic e I n hn cfg := by
  rw [integral_partition_sum e I n hn hInt]
  set integrals := List.ofFn (fun k : Fin n =>
    ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
      Expr.eval (fun _ => x) e) with hintegrals_def
  set bounds := collectBoundsDyadic e (uniformPartition I n hn) cfg with hbounds_def
  have hlen : integrals.length = bounds.length := by
    simp [hintegrals_def, hbounds_def, collectBoundsDyadic, uniformPartition]
  have hmem_each : ∀ i (hi : i < integrals.length),
      integrals[i] ∈ bounds[i]'(hlen ▸ hi) := by
    intro i hi
    have hi' : i < n := by simpa [hintegrals_def] using hi
    simp only [hintegrals_def]
    rw [List.getElem_ofFn]
    rw [partitionPoints_eq_lo I n hn i hi', partitionPoints_eq_hi I n hn i hi']
    have hpart_eq : bounds[i]'(hlen ▸ hi) =
        integrateInterval1Dyadic e (partitionInterval I n hn i hi') cfg := by
      simp [hbounds_def, collectBoundsDyadic, partitionInterval, uniformPartition]
    rw [hpart_eq]
    apply integrateInterval1Dyadic_correct e hsupp _ cfg hprec
    · exact hdomall i hi'
    · exact intervalIntegrable_on_partition e I n hn hInt i hi'
  have hsum_eq : ∑ k ∈ Finset.range n,
      ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
        Expr.eval (fun _ => x) e = integrals.sum := by
    simp only [hintegrals_def, Finset.sum_range, List.sum_ofFn]
  rw [hsum_eq]
  exact sum_mem_foldl_add hlen hmem_each

/-- Bridge theorem (lower bound) using the combined checker. -/
theorem integral_lower_of_check_dyadic (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (c : ℚ)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hcheck : checkIntegralLowerBoundDyadicFull e I n c cfg = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  unfold checkIntegralLowerBoundDyadicFull at hcheck
  simp only [hn, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hdomall := checkPartitionDomainValid_correct e I n hn cfg hcheck.1
  have hmem := integral_mem_bound_dyadic e hsupp I n hn cfg hprec hdomall hInt
  simp only [IntervalRat.mem_def] at hmem
  calc (c : ℝ) ≤ ((integratePartitionDyadic e I n hn cfg).lo : ℝ) := by exact_mod_cast hcheck.2
    _ ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := hmem.1

/-- Bridge theorem (upper bound) using the combined checker. -/
theorem integral_upper_of_check_dyadic (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (c : ℚ)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hcheck : checkIntegralUpperBoundDyadicFull e I n c cfg = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  unfold checkIntegralUpperBoundDyadicFull at hcheck
  simp only [hn, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hdomall := checkPartitionDomainValid_correct e I n hn cfg hcheck.1
  have hmem := integral_mem_bound_dyadic e hsupp I n hn cfg hprec hdomall hInt
  simp only [IntervalRat.mem_def] at hmem
  calc ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e
      ≤ ((integratePartitionDyadic e I n hn cfg).hi : ℝ) := hmem.2
    _ ≤ (c : ℝ) := by exact_mod_cast hcheck.2

/-! ### List-based (non-uniform) partition integration -/

/-- Integrate over an arbitrary list of subintervals using Dyadic evaluation. -/
def integratePartitionDyadicList (e : Expr) (parts : List IntervalRat)
    (cfg : DyadicConfig := {}) : IntervalRat :=
  let bounds := collectBoundsDyadic e parts cfg
  bounds.foldl IntervalRat.add (IntervalRat.singleton 0)

/-- Domain validity check for an arbitrary list of subintervals. -/
def checkPartitionDomainValidList (e : Expr) (parts : List IntervalRat)
    (cfg : DyadicConfig) : Bool :=
  parts.all fun Ik =>
    checkDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat Ik cfg.precision) cfg

/-- Combined checker (lower bound) for arbitrary partition. -/
def checkIntegralLowerBoundDyadicList (e : Expr) (parts : List IntervalRat)
    (c : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  checkPartitionDomainValidList e parts cfg &&
  decide (c ≤ (integratePartitionDyadicList e parts cfg).lo)

/-- Combined checker (upper bound) for arbitrary partition. -/
def checkIntegralUpperBoundDyadicList (e : Expr) (parts : List IntervalRat)
    (c : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  checkPartitionDomainValidList e parts cfg &&
  decide ((integratePartitionDyadicList e parts cfg).hi ≤ c)

/-! ### Bridge lemmas for list-based partition -/

/-- Bridge theorem (lower bound) for arbitrary partition. -/
theorem integral_lower_of_check_dyadic_list (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (parts : List IntervalRat)
    (c : ℚ) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hcheck : checkIntegralLowerBoundDyadicList e parts c cfg = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  sorry

/-- Bridge theorem (upper bound) for arbitrary partition. -/
theorem integral_upper_of_check_dyadic_list (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (parts : List IntervalRat)
    (c : ℚ) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hcheck : checkIntegralUpperBoundDyadicList e parts c cfg = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  sorry

end LeanCert.Validity.IntegrationDyadic
