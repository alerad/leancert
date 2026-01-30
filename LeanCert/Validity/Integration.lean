/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.Integrate
import LeanCert.Meta.ProveContinuous

/-!
# Integration Certificates

This module provides certificate-driven verification for definite integrals using
interval arithmetic with both computable (Core) and noncomputable (WithInv) evaluation.

## Main definitions

### Computable Integration (Core)
* `uniformPartitionCore` - Computable uniform partition
* `integrateInterval1Core` - Single-interval integration
* `integrateIntervalCore` - Multi-partition integration
* `checkIntegralBoundsCore` - Boolean checker for integral bounds
* `verify_integral_bound` - Golden theorem for integration bounds

### Integration with Inverse Support (WithInv)
* `integrateInterval1WithInv` - Single-interval integration with inv/log support
* `integratePartitionWithInv` - Partitioned integration with inv/log support
* `collectBoundsWithInv` - Collect bounds over partition

### Adaptive Integration
* `AdaptiveResultWithInv` - Result structure for adaptive integration
* `integrateAdaptiveWithInv` - Adaptive integration with error tolerance
* `checkIntegralAdaptiveLowerBound` - Boolean checker for adaptive lower bounds
* `checkIntegralAdaptiveUpperBound` - Boolean checker for adaptive upper bounds

### Exponential Search
* `searchPartitionLower` - Find minimum partitions for lower bound
* `searchPartitionUpper` - Find minimum partitions for upper bound
* `checkIntegralSearchLowerBound` - Boolean checker using exponential search
* `checkIntegralSearchUpperBound` - Boolean checker using exponential search
-/

namespace LeanCert.Validity.Integration

open LeanCert.Core
open LeanCert.Engine
open MeasureTheory

/-! ### Computable Integration Infrastructure

For `interval_integrate` tactic, we need:
1. A computable integration function using `evalIntervalCore1`
2. A theorem that `ExprSupportedCore` implies `IntervalIntegrable`
3. A verification theorem linking the computation to the real integral
-/

/-- Computable uniform partition using evalIntervalCore1 -/
def uniformPartitionCore (I : IntervalRat) (n : ℕ) (hn : 0 < n) : List IntervalRat :=
  let width := (I.hi - I.lo) / n
  List.ofFn fun i : Fin n =>
    { lo := I.lo + width * i
      hi := I.lo + width * (i + 1)
      le := by
        simp only [add_le_add_iff_left]
        apply mul_le_mul_of_nonneg_left
        · have : (i : ℚ) ≤ (i : ℚ) + 1 := le_add_of_nonneg_right (by norm_num)
          exact this
        · apply div_nonneg
          · linarith [I.le]
          · have : (0 : ℚ) < n := by exact_mod_cast hn
            linarith }

/-- Sum of interval bounds over a partition using computable evalIntervalCore1 -/
def sumIntervalBoundsCore (e : Expr) (parts : List IntervalRat) (cfg : EvalConfig) : IntervalRat :=
  parts.foldl
    (fun acc I =>
      let fBound := evalIntervalCore1 e I cfg
      let contribution := IntervalRat.mul
        (IntervalRat.singleton I.width)
        fBound
      IntervalRat.add acc contribution)
    (IntervalRat.singleton 0)

/-- Computable interval bounds on ∫_a^b f(x) dx using uniform partitioning -/
def integrateIntervalCore (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : EvalConfig := default) : IntervalRat :=
  sumIntervalBoundsCore e (uniformPartitionCore I n hn) cfg

/-- For single-interval integration (n=1), computable version -/
def integrateInterval1Core (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : IntervalRat :=
  let fBound := evalIntervalCore1 e I cfg
  IntervalRat.mul (IntervalRat.singleton I.width) fBound

/-! ### IntervalIntegrable from ExprSupportedCore

All `ExprSupportedCore` expressions are continuous, hence integrable on compact intervals. -/

/-- All ExprSupportedCore expressions are interval integrable on any compact interval.

This follows because ExprSupportedCore expressions are continuous (see exprSupportedCore_continuousOn),
and continuous functions on compact intervals are integrable.

Note: Requires domain validity for expressions with log. -/
theorem exprSupportedCore_intervalIntegrable (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat)
    (hdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi := by
  have hCont := LeanCert.Meta.exprSupportedCore_continuousOn e hsupp hdom
  -- Continuous functions on compact intervals are integrable
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  exact hCont.intervalIntegrable_of_Icc hle

/-! ### Correctness of Computable Integration -/

/-- Single-interval integration correctness for ExprSupportedCore.

This is proved directly using the same structure as integrateInterval1_correct but
with the computable evalIntervalCore1 instead of noncomputable evalInterval1.

The `hdom` hypothesis ensures evaluation domain validity (e.g., log arguments have positive interval bounds).
The `hcontdom` hypothesis ensures continuity domain validity (e.g., log arguments are positive on the set). -/
theorem integrateInterval1Core_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hdom : evalDomainValid1 e I cfg)
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg := by
  unfold integrateInterval1Core
  -- Get bounds from interval evaluation
  set fBound := evalIntervalCore1 e I cfg with hfBound_def
  have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ fBound := fun x hx =>
    evalIntervalCore1_correct e hsupp x I hx cfg hdom
  have hlo : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), (fBound.lo : ℝ) ≤ Expr.eval (fun _ => x) e := by
    intro x hx; exact (hbounds x hx).1
  have hhi : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (fBound.hi : ℝ) := by
    intro x hx; exact (hbounds x hx).2
  have hIle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have hInt := exprSupportedCore_intervalIntegrable e hsupp I hcontdom
  have ⟨h_lower, h_upper⟩ := LeanCert.Engine.integral_bounds_of_bounds hIle hInt hlo hhi
  -- Show membership in the product interval
  have hwidth : (I.width : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
    simp only [IntervalRat.width, Rat.cast_sub]
  have hwidth_nn : (0 : ℝ) ≤ I.width := by exact_mod_cast IntervalRat.width_nonneg I
  have hfBound_le : (fBound.lo : ℝ) ≤ fBound.hi := by exact_mod_cast fBound.le
  -- Convert integral bounds to width-first form
  have h_lo' : (I.width : ℝ) * fBound.lo ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := by
    calc (I.width : ℝ) * fBound.lo = fBound.lo * I.width := by ring
       _ = fBound.lo * ((I.hi : ℝ) - I.lo) := by rw [hwidth]
       _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lower
  have h_hi' : ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e ≤ (I.width : ℝ) * fBound.hi := by
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
       ≤ fBound.hi * ((I.hi : ℝ) - I.lo) := h_upper
     _ = fBound.hi * I.width := by rw [hwidth]
     _ = (I.width : ℝ) * fBound.hi := by ring
  -- Show membership
  have h1 : (I.width : ℝ) * fBound.lo ≤ I.width * fBound.hi :=
    mul_le_mul_of_nonneg_left hfBound_le hwidth_nn
  rw [IntervalRat.mem_def]
  constructor
  · -- Lower bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).lo =
        min (min (I.width * fBound.lo) (I.width * fBound.hi))
            (min (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
    calc (↑I.width * ↑fBound.lo) ⊓ (↑I.width * ↑fBound.hi)
        = ↑I.width * ↑fBound.lo := min_eq_left h1
      _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lo'
  · -- Upper bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).hi =
        max (max (I.width * fBound.lo) (I.width * fBound.hi))
            (max (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
        ≤ ↑I.width * ↑fBound.hi := h_hi'
      _ = (↑I.width * ↑fBound.lo) ⊔ (↑I.width * ↑fBound.hi) := (max_eq_right h1).symm

/-- Check if the integral bound contains a given rational value.
    Returns true if domain is valid and the computed integral bound contains the target value. -/
def checkIntegralBoundsCore (e : Expr) (I : IntervalRat) (target : ℚ)
    (cfg : EvalConfig := default) : Bool :=
  checkDomainValid1 e I cfg &&
  let bound := integrateInterval1Core e I cfg
  decide (bound.lo ≤ target && target ≤ bound.hi)

/-- **Golden Theorem for Integration Bounds**

If `checkIntegralBoundsCore e I target cfg = true`, then the integral is bounded by the
computed interval.

Note: The `target` parameter and `h_cert` hypothesis are used for the `native_decide` workflow
where we verify at compile time that target is in the computed interval. The actual proof
of interval membership uses `integrateInterval1Core_correct` directly.

This theorem allows proving statements like "∫_a^b f(x) dx ∈ [lo, hi]".

Note: Requires continuity domain validity for expressions with log. -/
theorem verify_integral_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (_target : ℚ) (cfg : EvalConfig)
    (h_cert : checkIntegralBoundsCore e I _target cfg = true)
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg := by
  simp only [checkIntegralBoundsCore, Bool.and_eq_true] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  exact integrateInterval1Core_correct e hsupp I cfg hdom hcontdom

/-- Extract the computed integral bound as an interval -/
def getIntegralBound (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : IntervalRat :=
  integrateInterval1Core e I cfg

/-- The integral lies within the computed bound (computable version)

Note: Requires continuity domain validity for expressions with log. -/
theorem integral_in_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hdom : evalDomainValid1 e I cfg)
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    (getIntegralBound e I cfg).lo ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∧
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (getIntegralBound e I cfg).hi := by
  have hmem := integrateInterval1Core_correct e hsupp I cfg hdom hcontdom
  simp only [IntervalRat.mem_def, getIntegralBound] at hmem ⊢
  exact hmem

/-! ### Single-interval integration for ExprSupportedWithInv -/

/-- Computable single-interval integration using evalInterval?1.
    Returns `none` if interval evaluation fails (e.g., log domain invalid). -/
def integrateInterval1WithInv (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  match evalInterval?1 e I with
  | some J => some (IntervalRat.mul (IntervalRat.singleton I.width) J)
  | none => none

/-- Single-interval integration correctness for ExprSupportedWithInv.
    Requires that evalInterval?1 succeeds on the interval. -/
theorem integrateInterval1WithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (bound : IntervalRat)
    (hsome : integrateInterval1WithInv e I = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound := by
  unfold integrateInterval1WithInv at hsome
  cases h_eval : evalInterval?1 e I with
  | none =>
    simp only [h_eval] at hsome
    cases hsome
  | some J =>
    simp only [h_eval] at hsome
    cases hsome
    -- Bounds from evalInterval?1
    have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ J := fun x hx =>
      evalInterval?1_correct e hsupp I J h_eval x hx
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
    rw [IntervalRat.mem_def]
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

/-- Check if the computed integration bound contains a target value.
    Returns false if interval evaluation fails. -/
def checkIntegralBoundsWithInv (e : Expr) (I : IntervalRat) (target : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J =>
      let bound := IntervalRat.mul (IntervalRat.singleton I.width) J
      decide (bound.lo ≤ target && target ≤ bound.hi)
  | none => false

/-- **Golden Theorem for Integration Bounds (WithInv)**

If `checkIntegralBoundsWithInv e I target = true`, then the integral lies in the
computed bound. The `target` parameter is for the `native_decide` workflow. -/
theorem verify_integral_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (_target : ℚ)
    (h_cert : checkIntegralBoundsWithInv e I _target = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∃ bound, integrateInterval1WithInv e I = some bound ∧
      ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound := by
  simp only [checkIntegralBoundsWithInv] at h_cert
  cases h_eval : evalInterval?1 e I with
  | none =>
    simp only [h_eval] at h_cert
    cases h_cert
  | some J =>
    have hbound : integrateInterval1WithInv e I =
        some (IntervalRat.mul (IntervalRat.singleton I.width) J) := by
      simp only [integrateInterval1WithInv, h_eval]
    refine ⟨IntervalRat.mul (IntervalRat.singleton I.width) J, hbound, ?_⟩
    exact integrateInterval1WithInv_correct e hsupp I
      (IntervalRat.mul (IntervalRat.singleton I.width) J) hbound hInt

/-! ### Partitioned integration for ExprSupportedWithInv -/

/-- Collect per-subinterval bounds using evalInterval?1.
    Returns `none` if any subinterval fails. -/
def collectBoundsWithInv (e : Expr) (parts : List IntervalRat) : Option (List IntervalRat) :=
  match parts with
  | [] => some []
  | I :: Is =>
      match integrateInterval1WithInv e I, collectBoundsWithInv e Is with
      | some J, some Js => some (J :: Js)
      | _, _ => none

/-- Sum bounds over a uniform partition using evalInterval?1. -/
def integratePartitionWithInv (e : Expr) (I : IntervalRat) (n : ℕ) : Option IntervalRat :=
  if hn : 0 < n then
    match collectBoundsWithInv e (uniformPartition I n hn) with
    | some bounds => some (bounds.foldl IntervalRat.add (IntervalRat.singleton 0))
    | none => none
  else
    none

theorem collectBoundsWithInv_length (e : Expr) :
    ∀ parts bounds,
      collectBoundsWithInv e parts = some bounds →
      bounds.length = parts.length := by
  intro parts
  induction parts with
  | nil =>
    intro bounds h
    simp [collectBoundsWithInv] at h
    cases h
    rfl
  | cons I Is ih =>
    intro bounds h
    simp [collectBoundsWithInv] at h
    cases hI : integrateInterval1WithInv e I <;>
      cases hIs : collectBoundsWithInv e Is <;>
      simp [hI, hIs] at h
    cases h
    have hlen := ih _ hIs
    simp [hlen]

theorem collectBoundsWithInv_getElem (e : Expr) :
    ∀ parts bounds (h : collectBoundsWithInv e parts = some bounds),
      ∀ i (hi : i < parts.length),
        integrateInterval1WithInv e (parts[i]'(by simpa using hi)) =
          some (bounds[i]'(by
          have hlen := collectBoundsWithInv_length e parts bounds h
          exact hlen ▸ hi)) := by
  intro parts
  induction parts with
  | nil =>
    intro bounds h i hi
    simp [collectBoundsWithInv] at h
    cases h
    simp at hi
  | cons I Is ih =>
    intro bounds h i hi
    simp [collectBoundsWithInv] at h
    cases hI : integrateInterval1WithInv e I <;>
      cases hIs : collectBoundsWithInv e Is <;>
      simp [hI, hIs] at h
    cases h
    cases i with
    | zero =>
      simp [List.getElem_cons, hI]
    | succ i =>
      have hi' : i < Is.length := by
        simpa [List.length] using hi
      have hrec := ih _ hIs i hi'
      simp [hrec]

theorem integral_subinterval_bounded_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (bound : IntervalRat)
    (hsome : integrateInterval1WithInv e (partitionInterval I n hn k hk) = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
      Expr.eval (fun _ => x) e ∈ bound := by
  rw [partitionPoints_eq_lo I n hn k hk, partitionPoints_eq_hi I n hn k hk]
  exact integrateInterval1WithInv_correct e hsupp _ bound hsome
    (intervalIntegrable_on_partition e I n hn hInt k hk)

theorem integratePartitionWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (bound : IntervalRat)
    (hsome : integratePartitionWithInv e I n = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound := by
  -- Decompose integral into sum over subintervals
  rw [integral_partition_sum e I n hn hInt]
  -- Unpack the computed bounds list
  unfold integratePartitionWithInv at hsome
  simp only [hn, ↓reduceDIte] at hsome
  cases hbounds : collectBoundsWithInv e (uniformPartition I n hn) with
  | none =>
    simp [hbounds] at hsome
  | some bounds =>
    have hbound_eq : bounds.foldl IntervalRat.add (IntervalRat.singleton 0) = bound := by
      simpa [hbounds] using hsome
    -- Express the Finset sum as a List sum
    have hsum_eq : ∑ k ∈ Finset.range n,
        ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
          Expr.eval (fun _ => x) e =
        (List.ofFn (fun k : Fin n =>
          ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
            Expr.eval (fun _ => x) e)).sum := by
      simp only [Finset.sum_range, List.sum_ofFn]
    rw [hsum_eq, ← hbound_eq]
    -- Set integrals list and bounds list
    set integrals := List.ofFn (fun k : Fin n =>
      ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
        Expr.eval (fun _ => x) e) with hintegrals_def
    -- Show lengths match
    have hlen : integrals.length = bounds.length := by
      have hlen_bounds := collectBoundsWithInv_length e _ _ hbounds
      simp [hintegrals_def, uniformPartition] at hlen_bounds ⊢
      exact hlen_bounds.symm
    -- Each integral is bounded by the corresponding bound
    have hmem : ∀ i (hi : i < integrals.length),
        integrals[i] ∈ bounds[i]'(hlen ▸ hi) := by
      intro i hi
      have hi' : i < n := by
        simpa [hintegrals_def, List.length_ofFn] using hi
      simp only [hintegrals_def]
      rw [List.getElem_ofFn]
      have hparts :
          integrateInterval1WithInv e ((uniformPartition I n hn)[i]'(by
            simp [uniformPartition]; exact hi')) = some (bounds[i]'(hlen ▸ hi)) := by
        exact collectBoundsWithInv_getElem e _ _ hbounds i (by
          simpa [uniformPartition] using hi')
      have hpart_eq :
          (uniformPartition I n hn)[i]'(by simp [uniformPartition]; exact hi') =
            partitionInterval I n hn i hi' := by
        simp [partitionInterval, uniformPartition]
      rw [hpart_eq] at hparts
      exact integral_subinterval_bounded_withInv e hsupp I n hn i hi' _ hparts hInt
    -- Apply sum_mem_foldl_add
    exact sum_mem_foldl_add hlen hmem

/-! ### Adaptive Integration for ExprSupportedWithInv

Adaptive integration concentrates partitions where the error is high (near singularities),
dramatically reducing the number of function evaluations compared to uniform partitioning.

The algorithm:
1. Compute a refined bound (n=2) on the current interval
2. If error (width of bound) is below tolerance, return
3. Otherwise, split at midpoint and recurse with half tolerance
4. Sum the bounds from sub-intervals

This naturally concentrates partitions near singularities where the function varies rapidly.
-/

/-- Result of adaptive integration with inverse support -/
structure AdaptiveResultWithInv where
  /-- Interval containing the integral -/
  bound : IntervalRat
  /-- Number of subintervals used -/
  partitions : ℕ
  deriving Repr

/-- Error estimate for adaptive integration: width of the refined bound -/
def adaptiveErrorEstimate (bound : IntervalRat) : ℚ := bound.width

/-- Compute a refined bound (n=2) on a single interval using WithInv support.
    Returns `none` if evaluation fails (domain issues). -/
def integrateRefinedWithInv (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  integratePartitionWithInv e I 2

/-- Recursive adaptive integration with inverse support.
    At each level, computes refined bound and either:
    - Returns if error ≤ tol or maxDepth = 0
    - Subdivides and recurses -/
def integrateAdaptiveAuxWithInv (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : Option AdaptiveResultWithInv :=
  match maxDepth with
  | 0 =>
    -- Base case: return the best bound we can compute
    match integrateRefinedWithInv e I with
    | some refined => some { bound := refined, partitions := 2 }
    | none => none
  | n + 1 =>
    match integrateRefinedWithInv e I with
    | none => none
    | some refined =>
      if adaptiveErrorEstimate refined ≤ tol then
        -- Error is acceptable, return
        some { bound := refined, partitions := 2 }
      else
        -- Subdivide and recurse
        let (I₁, I₂) := splitMid I
        let localTol := tol / 2  -- Split tolerance between halves
        match integrateAdaptiveAuxWithInv e I₁ localTol n,
              integrateAdaptiveAuxWithInv e I₂ localTol n with
        | some r₁, some r₂ =>
          some {
            bound := IntervalRat.add r₁.bound r₂.bound
            partitions := r₁.partitions + r₂.partitions
          }
        | _, _ => none

/-- Adaptive integration with inverse support and error tolerance.
    Keeps subdividing until the uncertainty is below `tol`. -/
def integrateAdaptiveWithInv (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : Option AdaptiveResultWithInv :=
  integrateAdaptiveAuxWithInv e I tol maxDepth

/-! #### Correctness proofs for adaptive integration with inverse support -/

/-- integrateRefinedWithInv is correct (direct from integratePartitionWithInv_correct) -/
theorem integrateRefinedWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (bound : IntervalRat)
    (hsome : integrateRefinedWithInv e I = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound :=
  integratePartitionWithInv_correct e hsupp I 2 (by norm_num) bound hsome hInt

/-- Integrability on left half after midpoint split -/
theorem intervalIntegrable_splitMid_left_withInv (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (splitMid I).1.lo (splitMid I).1.hi := by
  simp only [splitMid_left_lo, splitMid_left_hi]
  exact hInt.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (midpoint_mem_uIcc I))

/-- Integrability on right half after midpoint split -/
theorem intervalIntegrable_splitMid_right_withInv (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (splitMid I).2.lo (splitMid I).2.hi := by
  simp only [splitMid_right_lo, splitMid_right_hi]
  exact hInt.mono_set (Set.uIcc_subset_uIcc (midpoint_mem_uIcc I) (Set.right_mem_uIcc))

/-- Integral over split interval equals sum of integrals over halves -/
theorem integral_split_mid_withInv (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e =
    (∫ x in (I.lo : ℝ)..(I.midpoint : ℝ), Expr.eval (fun _ => x) e) +
    (∫ x in (I.midpoint : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e) := by
  have hInt1 : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.midpoint :=
    hInt.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (midpoint_mem_uIcc I))
  have hInt2 : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.midpoint I.hi :=
    hInt.mono_set (Set.uIcc_subset_uIcc (midpoint_mem_uIcc I) (Set.right_mem_uIcc))
  exact (intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2).symm

/-- Main soundness theorem: adaptive integration returns a bound containing the true integral.
    This is proved by induction on maxDepth. -/
theorem integrateAdaptiveAuxWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (result : AdaptiveResultWithInv)
    (hsome : integrateAdaptiveAuxWithInv e I tol maxDepth = some result)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ result.bound := by
  induction maxDepth generalizing I tol result with
  | zero =>
    -- Base case: returns integrateRefinedWithInv, which is correct
    simp only [integrateAdaptiveAuxWithInv] at hsome
    cases hrefined : integrateRefinedWithInv e I with
    | none => simp [hrefined] at hsome
    | some refined =>
      simp only [hrefined, Option.some.injEq] at hsome
      cases hsome
      exact integrateRefinedWithInv_correct e hsupp I refined hrefined hInt
  | succ n ih =>
    simp only [integrateAdaptiveAuxWithInv] at hsome
    cases hrefined : integrateRefinedWithInv e I with
    | none => simp [hrefined] at hsome
    | some refined =>
      simp only [hrefined] at hsome
      split_ifs at hsome with herr
      · -- Error acceptable: returns integrateRefinedWithInv
        simp only [Option.some.injEq] at hsome
        cases hsome
        exact integrateRefinedWithInv_correct e hsupp I refined hrefined hInt
      · -- Subdivide case
        cases hr1 : integrateAdaptiveAuxWithInv e (splitMid I).1 (tol / 2) n with
        | none => simp [hr1] at hsome
        | some r1 =>
          cases hr2 : integrateAdaptiveAuxWithInv e (splitMid I).2 (tol / 2) n with
          | none => simp [hr1, hr2] at hsome
          | some r2 =>
            simp only [hr1, hr2, Option.some.injEq] at hsome
            cases hsome
            -- Split the integral
            have hsplit := integral_split_mid_withInv e I hInt
            rw [hsplit]
            -- Get bounds for each half
            have hInt₁ := intervalIntegrable_splitMid_left_withInv e I hInt
            have hInt₂ := intervalIntegrable_splitMid_right_withInv e I hInt
            have h1 := ih (splitMid I).1 (tol / 2) r1 hr1 hInt₁
            have h2 := ih (splitMid I).2 (tol / 2) r2 hr2 hInt₂
            -- The bounds are correct, so their sum contains the sum of integrals
            simp only [splitMid_left_lo, splitMid_left_hi,
                       splitMid_right_lo, splitMid_right_hi] at h1 h2
            exact IntervalRat.mem_add h1 h2

/-- Soundness of the main adaptive integration function with inverse support -/
theorem integrateAdaptiveWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (result : AdaptiveResultWithInv)
    (hsome : integrateAdaptiveWithInv e I tol maxDepth = some result)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ result.bound :=
  integrateAdaptiveAuxWithInv_correct e hsupp I tol maxDepth result hsome hInt

/-! #### Adaptive integral bound checkers for native_decide -/

/-- Boolean checker for adaptive integral lower bounds.
    More efficient than uniform partitioning for functions with singularities. -/
def checkIntegralAdaptiveLowerBound (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) (c : ℚ) : Bool :=
  match integrateAdaptiveWithInv e I tol maxDepth with
  | some result => decide (c ≤ result.bound.lo)
  | none => false

/-- Boolean checker for adaptive integral upper bounds.
    More efficient than uniform partitioning for functions with singularities. -/
def checkIntegralAdaptiveUpperBound (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) (c : ℚ) : Bool :=
  match integrateAdaptiveWithInv e I tol maxDepth with
  | some result => decide (result.bound.hi ≤ c)
  | none => false

/-- Bridge theorem: if `checkIntegralAdaptiveLowerBound` returns true, the integral is ≥ c. -/
theorem integral_adaptive_lower_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (c : ℚ)
    (hcheck : checkIntegralAdaptiveLowerBound e I tol maxDepth c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  unfold checkIntegralAdaptiveLowerBound at hcheck
  cases hbound : integrateAdaptiveWithInv e I tol maxDepth with
  | none => simp [hbound] at hcheck
  | some result =>
    simp only [hbound, decide_eq_true_eq] at hcheck
    have hmem := integrateAdaptiveWithInv_correct e hsupp I tol maxDepth result hbound hInt
    simp only [IntervalRat.mem_def] at hmem
    calc (c : ℝ) ≤ (result.bound.lo : ℝ) := by exact_mod_cast hcheck
      _ ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := hmem.1

/-- Bridge theorem: if `checkIntegralAdaptiveUpperBound` returns true, the integral is ≤ c. -/
theorem integral_adaptive_upper_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (c : ℚ)
    (hcheck : checkIntegralAdaptiveUpperBound e I tol maxDepth c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  unfold checkIntegralAdaptiveUpperBound at hcheck
  cases hbound : integrateAdaptiveWithInv e I tol maxDepth with
  | none => simp [hbound] at hcheck
  | some result =>
    simp only [hbound, decide_eq_true_eq] at hcheck
    have hmem := integrateAdaptiveWithInv_correct e hsupp I tol maxDepth result hbound hInt
    simp only [IntervalRat.mem_def] at hmem
    calc ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (result.bound.hi : ℝ) := hmem.2
      _ ≤ (c : ℝ) := by exact_mod_cast hcheck

/-! ### Exponential Search for Optimal Partition Count

Instead of using a fixed large N or deep adaptive recursion, we can search for
the minimum partition count that achieves the desired bound. This is often
much faster because many integrals only need N=100-500 instead of N=3000.

Algorithm:
1. Start with N=startN (e.g., 32)
2. Double N until the bound is achieved (exponential search)
3. Return the first N that works

This finds the optimal N in O(log(N)) integration attempts.
-/

/-- Exponential search with explicit fuel for termination.
    Returns the computed bound if found within fuel doublings, or `none` otherwise. -/
def searchPartitionLowerAux (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) : Option IntervalRat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if n > maxN then none
    else if _hn : 0 < n then
      match integratePartitionWithInv e I n with
      | some J =>
        if decide (c ≤ J.lo) then some J
        else searchPartitionLowerAux e I (2 * n) maxN c fuel'
      | none => none
    else none

/-- Exponential search for minimum partition count that achieves a lower bound. -/
def searchPartitionLower (e : Expr) (I : IntervalRat) (startN maxN : ℕ) (c : ℚ) :
    Option IntervalRat :=
  searchPartitionLowerAux e I startN maxN c 20  -- 20 doublings allows up to startN * 2^20

/-- Exponential search with explicit fuel for upper bounds. -/
def searchPartitionUpperAux (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) : Option IntervalRat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if n > maxN then none
    else if _hn : 0 < n then
      match integratePartitionWithInv e I n with
      | some J =>
        if decide (J.hi ≤ c) then some J
        else searchPartitionUpperAux e I (2 * n) maxN c fuel'
      | none => none
    else none

/-- Exponential search for minimum partition count that achieves an upper bound. -/
def searchPartitionUpper (e : Expr) (I : IntervalRat) (startN maxN : ℕ) (c : ℚ) :
    Option IntervalRat :=
  searchPartitionUpperAux e I startN maxN c 20

/-- Check lower bound using exponential search to find optimal N.
    Much faster than fixed large N when fewer partitions suffice.
    startN: initial partition count (e.g., 32)
    maxN: maximum partitions to try (e.g., 8192) -/
def checkIntegralSearchLowerBound (e : Expr) (I : IntervalRat)
    (startN maxN : ℕ) (c : ℚ) : Bool :=
  (searchPartitionLower e I startN maxN c).isSome

/-- Check upper bound using exponential search to find optimal N. -/
def checkIntegralSearchUpperBound (e : Expr) (I : IntervalRat)
    (startN maxN : ℕ) (c : ℚ) : Bool :=
  (searchPartitionUpper e I startN maxN c).isSome

/-- Helper: if searchPartitionLowerAux succeeds, the result satisfies the bound. -/
theorem searchPartitionLowerAux_spec (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) (J : IntervalRat) (hfind : searchPartitionLowerAux e I n maxN c fuel = some J) :
    c ≤ J.lo := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionLowerAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionLowerAux] at hfind
    split at hfind
    · simp at hfind
    · split at hfind
      · cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          split at hfind
          · simp only [Option.some.injEq] at hfind
            subst hfind
            simp_all only [decide_eq_true_eq]
          · exact ih (2 * n) hfind
      · simp at hfind

/-- Helper: if searchPartitionUpperAux succeeds, the result satisfies the bound. -/
theorem searchPartitionUpperAux_spec (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) (J : IntervalRat) (hfind : searchPartitionUpperAux e I n maxN c fuel = some J) :
    J.hi ≤ c := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionUpperAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionUpperAux] at hfind
    split at hfind
    · simp at hfind
    · split at hfind
      · cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          split at hfind
          · simp only [Option.some.injEq] at hfind
            subst hfind
            simp_all only [decide_eq_true_eq]
          · exact ih (2 * n) hfind
      · simp at hfind

/-- Helper: searchPartitionLowerAux returns a valid integration bound. -/
theorem searchPartitionLowerAux_valid (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n maxN : ℕ) (_hn : 0 < n) (c : ℚ) (fuel : ℕ) (J : IntervalRat)
    (hfind : searchPartitionLowerAux e I n maxN c fuel = some J)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ J := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionLowerAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionLowerAux] at hfind
    by_cases hle : n > maxN
    · simp [hle] at hfind
    · simp only [hle, ↓reduceIte] at hfind
      by_cases hn' : 0 < n
      · simp only [hn', ↓reduceDIte] at hfind
        cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          by_cases hdec : c ≤ J'.lo
          · simp only [decide_eq_true hdec, ↓reduceIte, Option.some.injEq] at hfind
            subst hfind
            exact integratePartitionWithInv_correct e hsupp I n hn' J' hint hInt
          · simp only [decide_eq_false hdec, Bool.false_eq_true, ↓reduceIte] at hfind
            have h2n_pos : 0 < 2 * n := by omega
            exact ih (2 * n) h2n_pos hfind
      · simp [hn'] at hfind

/-- Helper: searchPartitionUpperAux returns a valid integration bound. -/
theorem searchPartitionUpperAux_valid (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n maxN : ℕ) (_hn : 0 < n) (c : ℚ) (fuel : ℕ) (J : IntervalRat)
    (hfind : searchPartitionUpperAux e I n maxN c fuel = some J)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ J := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionUpperAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionUpperAux] at hfind
    by_cases hle : n > maxN
    · simp [hle] at hfind
    · simp only [hle, ↓reduceIte] at hfind
      by_cases hn' : 0 < n
      · simp only [hn', ↓reduceDIte] at hfind
        cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          by_cases hdec : J'.hi ≤ c
          · simp only [decide_eq_true hdec, ↓reduceIte, Option.some.injEq] at hfind
            subst hfind
            exact integratePartitionWithInv_correct e hsupp I n hn' J' hint hInt
          · simp only [decide_eq_false hdec, Bool.false_eq_true, ↓reduceIte] at hfind
            have h2n_pos : 0 < 2 * n := by omega
            exact ih (2 * n) h2n_pos hfind
      · simp [hn'] at hfind

/-- Bridge theorem: if exponential search succeeds, the integral satisfies the lower bound. -/
theorem integral_search_lower_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (startN maxN : ℕ) (hstart : 0 < startN) (c : ℚ)
    (hcheck : checkIntegralSearchLowerBound e I startN maxN c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  unfold checkIntegralSearchLowerBound searchPartitionLower at hcheck
  simp only [Option.isSome_iff_exists] at hcheck
  obtain ⟨J, hJ⟩ := hcheck
  have hcJ := searchPartitionLowerAux_spec e I startN maxN c 20 J hJ
  have hmem := searchPartitionLowerAux_valid e hsupp I startN maxN hstart c 20 J hJ hInt
  simp only [IntervalRat.mem_def] at hmem
  calc (c : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hcJ
    _ ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := hmem.1

/-- Bridge theorem: if exponential search succeeds, the integral satisfies the upper bound. -/
theorem integral_search_upper_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (startN maxN : ℕ) (hstart : 0 < startN) (c : ℚ)
    (hcheck : checkIntegralSearchUpperBound e I startN maxN c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  unfold checkIntegralSearchUpperBound searchPartitionUpper at hcheck
  simp only [Option.isSome_iff_exists] at hcheck
  obtain ⟨J, hJ⟩ := hcheck
  have hcJ := searchPartitionUpperAux_spec e I startN maxN c 20 J hJ
  have hmem := searchPartitionUpperAux_valid e hsupp I startN maxN hstart c 20 J hJ hInt
  simp only [IntervalRat.mem_def] at hmem
  calc ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (J.hi : ℝ) := hmem.2
    _ ≤ (c : ℝ) := by exact_mod_cast hcJ

end LeanCert.Validity.Integration
