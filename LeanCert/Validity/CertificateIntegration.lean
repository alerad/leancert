/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Integration

/-!
# Certificate-Based Integration (Proof by Reflection)

This implements the "mega-theorem" approach where:
1. **Search (untrusted)**: Pre-compute partition list via adaptive algorithm
2. **Certificate**: Store the list of (domain, bound) pairs
3. **Verify (trusted)**: Linear checker verifies each bound is valid

Why this is faster:
- No branching/recursion in kernel - just linear iteration
- Certificate can be saved/loaded (checkpointing)
- Separates algorithm complexity from verification complexity

## Main definitions

### Structures
* `PartitionEntry` - A single partition entry in an integral certificate
* `IntegralCertificate` - Certificate for a definite integral computation

### Boolean Checkers
* `checkCoverage` - Check partition domains cover the overall domain contiguously
* `checkPartitionBound` - Check a single partition bound is valid
* `checkAllBounds` - Check all partition bounds are valid
* `verifyCertificate` - Main certificate verifier

### Golden Theorems
* `verify_certificate_correct` - Main soundness theorem for certificate-based integration
* `verify_integral_cert_lower_bound` - Certificate-verified integral lower bound
* `verify_integral_cert_upper_bound` - Certificate-verified integral upper bound

### Certificate Generation
* `mkPartitionEntry` - Build a certificate entry from a successful interval evaluation
* `buildCertificate` - Build an integration certificate using adaptive partitioning
-/

namespace LeanCert.Validity.CertificateIntegration

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity.Integration

/-- A single partition entry in an integral certificate -/
structure PartitionEntry where
  /-- The domain interval for this partition -/
  domain : IntervalRat
  /-- The claimed bound on the integral over this partition -/
  bound : IntervalRat
  deriving Repr

instance : Inhabited PartitionEntry where
  default := ⟨⟨0, 0, le_refl 0⟩, ⟨0, 0, le_refl 0⟩⟩

/-- Certificate for a definite integral computation.
    Contains pre-computed partitions and their bounds. -/
structure IntegralCertificate where
  /-- The expression being integrated -/
  expr_id : String  -- For documentation/debugging only
  /-- The overall integration domain [a, b] -/
  domain : IntervalRat
  /-- List of partition entries -/
  partitions : List PartitionEntry
  deriving Repr

/-! ### Certificate Verification (Linear Checker)

These functions are what the kernel actually executes.
They are purely linear - no recursion, no branching on computed values.
-/

/-- Check that partition domains cover [a, b] contiguously.
    Returns true iff domains are [a, t₁], [t₁, t₂], ..., [tₙ₋₁, b] -/
def checkCoverage (entries : List PartitionEntry) (domain : IntervalRat) : Bool :=
  match entries with
  | [] => false  -- Empty partition doesn't cover anything
  | e :: es =>
    -- First partition must start at domain.lo
    if decide (e.domain.lo ≠ domain.lo) then false
    else
      let rec checkContiguous : List PartitionEntry → ℚ → Bool
        | [], lastHi => decide (lastHi = domain.hi)
        | e :: es, lastHi =>
          if decide (e.domain.lo ≠ lastHi) then false
          else checkContiguous es e.domain.hi
      checkContiguous es e.domain.hi

/-- Check that a single partition bound is valid using evalInterval?1.
    This is the core soundness check for each partition. -/
def checkPartitionBound (e : Expr) (entry : PartitionEntry) : Bool :=
  match evalInterval?1 e entry.domain with
  | none => false  -- Domain invalid
  | some computed =>
    -- The computed integral bound must be contained in the claimed bound
    -- Integral bound = computed * width
    let width := entry.domain.hi - entry.domain.lo
    let integralLo := computed.lo * width
    let integralHi := computed.hi * width
    decide (entry.bound.lo ≤ integralLo ∧ integralHi ≤ entry.bound.hi)

/-- Check all partition bounds are valid -/
def checkAllBounds (e : Expr) (entries : List PartitionEntry) : Bool :=
  entries.all (checkPartitionBound e)

/-- Sum all partition bounds -/
def sumBounds (entries : List PartitionEntry) : IntervalRat :=
  entries.foldl (fun acc entry => IntervalRat.add acc entry.bound)
    ⟨0, 0, le_refl 0⟩

/-- Check that the sum of bounds is contained in a target interval -/
def checkSumInTarget (entries : List PartitionEntry) (target : IntervalRat) : Bool :=
  let sum := sumBounds entries
  decide (target.lo ≤ sum.lo ∧ sum.hi ≤ target.hi)

/-- The main certificate verifier - LINEAR, no recursion in control flow.
    Returns true iff:
    1. Coverage: partition domains cover the overall domain contiguously
    2. Soundness: each partition bound is valid (evalInterval ⊆ bound)
    3. Target: sum of bounds is contained in target -/
def verifyCertificate (e : Expr) (cert : IntegralCertificate) (target : IntervalRat) : Bool :=
  checkCoverage cert.partitions cert.domain &&
  checkAllBounds e cert.partitions &&
  checkSumInTarget cert.partitions target

/-! ### Soundness Theorems

These theorems prove that if verifyCertificate returns true,
the actual integral is contained in the target interval.
-/

/-- Coverage implies the partition intervals form a valid partition -/
theorem coverage_implies_partition (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true) :
    entries ≠ [] := by
  cases entries with
  | nil => simp [checkCoverage] at hcov
  | cons e es => simp

/-! ### Singleton Multiplication Lemmas

These lemmas characterize the behavior of IntervalRat.mul when one operand
is a singleton interval [w, w]. For w ≥ 0, multiplying [w, w] × [lo, hi]
gives [w·lo, w·hi]. -/

/-- For singleton multiplication, .lo equals min of corner products,
    which simplifies to min (w*lo) (w*hi) since singleton has equal endpoints. -/
theorem singleton_mul_lo_eq_min (w : ℚ) (J : IntervalRat) :
    (IntervalRat.mul (IntervalRat.singleton w) J).lo = min (w * J.lo) (w * J.hi) := by
  -- The mul definition uses min4 of all corner products
  -- For singleton, corner products are (w*lo), (w*hi), (w*lo), (w*hi)
  -- min4 a b a b = min (min a b) (min a b) = min a b
  simp only [IntervalRat.mul, IntervalRat.singleton]
  -- Goal: min4 (w*J.lo) (w*J.hi) (w*J.lo) (w*J.hi) = min (w*J.lo) (w*J.hi)
  -- min4 is defined as: min (min a b) (min c d)
  -- So min4 a b a b = min (min a b) (min a b) = min a b
  show min (min (w * J.lo) (w * J.hi)) (min (w * J.lo) (w * J.hi)) = min (w * J.lo) (w * J.hi)
  rw [min_self]

/-- For singleton multiplication, .hi equals max of corner products,
    which simplifies to max (w*lo) (w*hi) since singleton has equal endpoints. -/
theorem singleton_mul_hi_eq_max (w : ℚ) (J : IntervalRat) :
    (IntervalRat.mul (IntervalRat.singleton w) J).hi = max (w * J.lo) (w * J.hi) := by
  simp only [IntervalRat.mul, IntervalRat.singleton]
  show max (max (w * J.lo) (w * J.hi)) (max (w * J.lo) (w * J.hi)) = max (w * J.lo) (w * J.hi)
  rw [max_self]

/-- For singleton multiplication with non-negative width, the lower bound
    equals width times the interval's lower bound. -/
theorem singleton_mul_lo_nonneg (w : ℚ) (J : IntervalRat) (hw : 0 ≤ w) :
    (IntervalRat.mul (IntervalRat.singleton w) J).lo = w * J.lo := by
  rw [singleton_mul_lo_eq_min]
  have h := J.le
  have hwmul : w * J.lo ≤ w * J.hi := mul_le_mul_of_nonneg_left h hw
  exact min_eq_left hwmul

/-- For singleton multiplication with non-negative width, the upper bound
    equals width times the interval's upper bound. -/
theorem singleton_mul_hi_nonneg (w : ℚ) (J : IntervalRat) (hw : 0 ≤ w) :
    (IntervalRat.mul (IntervalRat.singleton w) J).hi = w * J.hi := by
  rw [singleton_mul_hi_eq_max]
  have h := J.le
  have hwmul : w * J.lo ≤ w * J.hi := mul_le_mul_of_nonneg_left h hw
  exact max_eq_right hwmul

/-- Single partition bound correctness.

The proof uses `integrateInterval1WithInv_correct` which shows that for
`evalInterval?1 e I = some J`, the integral ∫[I.lo, I.hi] f ∈ I.width * J.

Since `checkPartitionBound` verifies that `entry.bound` contains `width * computed`,
we get that the integral is in `entry.bound`. -/
theorem partition_bound_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (entry : PartitionEntry)
    (hcheck : checkPartitionBound e entry = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (entry.domain.lo : ℝ) (entry.domain.hi : ℝ)) :
    ∫ x in (entry.domain.lo : ℝ)..(entry.domain.hi : ℝ),
      Expr.eval (fun _ => x) e ∈ entry.bound := by
  -- Extract the computed interval from checkPartitionBound
  simp only [checkPartitionBound] at hcheck
  cases heval : evalInterval?1 e entry.domain with
  | none => simp [heval] at hcheck
  | some computed =>
    simp only [heval, decide_eq_true_eq] at hcheck
    obtain ⟨hlo_check, hhi_check⟩ := hcheck
    -- Use integrateInterval1WithInv_correct to get integral bounds
    have hsome : integrateInterval1WithInv e entry.domain =
        some (IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed) := by
      simp only [integrateInterval1WithInv, heval]
    have hmem := integrateInterval1WithInv_correct e hsupp entry.domain
      (IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed) hsome hInt
    -- hmem says: integral ∈ IntervalRat.mul (singleton width) computed
    -- hlo_check says: entry.bound.lo ≤ computed.lo * width
    -- hhi_check says: computed.hi * width ≤ entry.bound.hi
    -- The interval mul (singleton w) J gives [w*J.lo, w*J.hi] when w ≥ 0
    -- So we need: entry.bound contains [width * computed.lo, width * computed.hi]
    -- which contains the integral.
    rw [IntervalRat.mem_def] at hmem ⊢
    have hwidth_nn : (0 : ℚ) ≤ entry.domain.width := IntervalRat.width_nonneg entry.domain
    have hcomp_le : computed.lo ≤ computed.hi := computed.le
    -- Technical lemmas about interval multiplication bounds
    have hmul_lo_le : (entry.domain.width * computed.lo : ℝ) ≤
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).lo : ℝ) ∨
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).lo : ℝ) ≤
        (entry.domain.width * computed.lo : ℝ) := le_total _ _
    have hmul_hi_le : (entry.domain.width * computed.hi : ℝ) ≤
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).hi : ℝ) ∨
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).hi : ℝ) ≤
        (entry.domain.width * computed.hi : ℝ) := le_total _ _
    -- The interval bound from integrateInterval1WithInv satisfies:
    -- lo ≤ width * computed.lo and width * computed.hi ≤ hi (when width ≥ 0)
    -- This follows from how IntervalRat.mul is defined for singletons
    have hlo_eq : (computed.lo * (entry.domain.hi - entry.domain.lo) : ℚ) =
        entry.domain.width * computed.lo := by unfold IntervalRat.width; ring
    have hhi_eq : (computed.hi * (entry.domain.hi - entry.domain.lo) : ℚ) =
        entry.domain.width * computed.hi := by unfold IntervalRat.width; ring
    constructor
    · -- entry.bound.lo ≤ integral
      have h1 : (entry.bound.lo : ℝ) ≤ (entry.domain.width * computed.lo : ℝ) := by
        have h := hlo_check
        rw [hlo_eq] at h
        exact_mod_cast h
      -- Use singleton_mul_lo_nonneg: for w ≥ 0, (singleton w).mul J).lo = w * J.lo
      have hmul_bound_lo_eq : ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).lo : ℝ) =
          (entry.domain.width * computed.lo : ℝ) := by
        simp only [singleton_mul_lo_nonneg entry.domain.width computed hwidth_nn, Rat.cast_mul]
      linarith [hmem.1]
    · -- integral ≤ entry.bound.hi
      have h1 : (entry.domain.width * computed.hi : ℝ) ≤ (entry.bound.hi : ℝ) := by
        have h := hhi_check
        rw [hhi_eq] at h
        exact_mod_cast h
      -- Use singleton_mul_hi_nonneg: for w ≥ 0, (singleton w).mul J).hi = w * J.hi
      have hmul_bound_hi_eq : ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).hi : ℝ) =
          (entry.domain.width * computed.hi : ℝ) := by
        simp only [singleton_mul_hi_nonneg entry.domain.width computed hwidth_nn, Rat.cast_mul]
      linarith [hmem.2]

/-- Helper: foldl add accumulates correctly -/
private theorem foldl_add_mem (acc : IntervalRat) (accVal : ℝ) (hacc : accVal ∈ acc)
    (vals : List ℝ) (intervals : List IntervalRat)
    (hlen : vals.length = intervals.length)
    (hmem : ∀ i (hi : i < vals.length),
      (vals[i] : ℝ) ∈ (intervals[i]'(hlen ▸ hi) : IntervalRat)) :
    accVal + vals.sum ∈ (intervals.foldl (fun a I => IntervalRat.add a I) acc) := by
  induction vals generalizing acc accVal intervals with
  | nil =>
    simp only [List.length_nil] at hlen
    cases intervals with
    | nil => simp [hacc]
    | cons h t => simp at hlen
  | cons v vs ih =>
    cases intervals with
    | nil => simp at hlen
    | cons I Is =>
      simp only [List.length_cons, add_left_inj] at hlen
      simp only [List.foldl_cons, List.sum_cons]
      -- accVal + (v + vs.sum) = (accVal + v) + vs.sum
      rw [← add_assoc]
      -- Show accVal + v ∈ IntervalRat.add acc I
      have hacc' : accVal + v ∈ IntervalRat.add acc I := by
        apply IntervalRat.mem_add hacc
        exact hmem 0 (by simp)
      -- Show remaining membership
      have hmem' : ∀ (i : ℕ) (hi : i < vs.length), vs[i] ∈ Is[i] := by
        intro i hi
        have h := hmem (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h
        convert h using 1
      exact ih (IntervalRat.add acc I) (accVal + v) hacc' Is hlen hmem'

/-- Sum of values in intervals is in the sum interval -/
theorem sum_mem_sum_intervals (vals : List ℝ) (intervals : List IntervalRat)
    (hlen : vals.length = intervals.length)
    (hmem : ∀ i (hi : i < vals.length),
      (vals[i] : ℝ) ∈ (intervals[i]'(hlen ▸ hi) : IntervalRat)) :
    vals.sum ∈ (intervals.foldl (fun acc I => IntervalRat.add acc I) ⟨0, 0, le_refl 0⟩) := by
  have h := foldl_add_mem ⟨0, 0, le_refl 0⟩ 0 (by simp [IntervalRat.mem_def]) vals intervals hlen hmem
  simp at h
  exact h

/-- Coverage implies the first entry starts at domain.lo -/
theorem coverage_first_starts (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (hne : entries ≠ []) :
    (entries.head hne).domain.lo = domain.lo := by
  cases entries with
  | nil => simp at hne
  | cons e es =>
    simp only [List.head_cons]
    simp only [checkCoverage] at hcov
    by_cases h : e.domain.lo = domain.lo
    · exact h
    · -- Contradiction: checkCoverage would return false
      exfalso
      simp only [ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte] at hcov
      exact Bool.noConfusion hcov

/-- Helper: checkContiguous ending at domain.hi means the last entry ends there -/
private theorem checkContiguous_last_ends_aux (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true)
    (hne : es ≠ []) :
    (es.getLast hne).domain.hi = domain.hi := by
  induction es generalizing lastHi with
  | nil => simp at hne
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous] at hcheck
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
      cases es' with
      | nil =>
        simp only [List.getLast_singleton]
        simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcheck
        exact hcheck
      | cons e' es'' =>
        simp only [List.getLast_cons_cons]
        exact ih e.domain.hi hcheck (by simp)
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck

/-- Coverage implies the last entry ends at domain.hi -/
theorem coverage_last_ends (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (hne : entries ≠ []) :
    (entries.getLast hne).domain.hi = domain.hi := by
  cases entries with
  | nil => simp at hne
  | cons e es =>
    simp only [checkCoverage] at hcov
    by_cases h : e.domain.lo = domain.lo
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcov
      cases es with
      | nil =>
        simp only [List.getLast_singleton]
        simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcov
        exact hcov
      | cons e' es' =>
        simp only [List.getLast_cons_cons]
        exact checkContiguous_last_ends_aux (e' :: es') e.domain.hi domain hcov (by simp)
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov

/-- Helper: checkContiguous implies adjacency within the list -/
private theorem checkContiguous_adjacent_aux (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true)
    (i : ℕ) (hi : i + 1 < es.length) :
    (es[i]'(by omega)).domain.hi = (es[i + 1]'hi).domain.lo := by
  induction es generalizing lastHi i with
  | nil => simp at hi
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous] at hcheck
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
      cases i with
      | zero =>
        -- Need to show e.domain.hi = (es'[0]).domain.lo
        cases es' with
        | nil => simp at hi
        | cons e' es'' =>
          -- From checkContiguous, e'.domain.lo = e.domain.hi (lastHi for next iteration)
          simp only [checkCoverage.checkContiguous] at hcheck
          by_cases h' : e'.domain.lo = e.domain.hi
          · exact h'.symm
          · simp only [ne_eq, h', not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck
      | succ j =>
        -- Use IH for es' with index j
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        exact ih e.domain.hi hcheck j hi
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck

/-- Coverage implies consecutive entries are adjacent -/
theorem coverage_adjacent (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (i : ℕ) (hi : i + 1 < entries.length) :
    (entries[i]'(by omega)).domain.hi = (entries[i + 1]'hi).domain.lo := by
  cases entries with
  | nil => simp at hi
  | cons e es =>
    simp only [checkCoverage] at hcov
    by_cases h : e.domain.lo = domain.lo
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcov
      cases i with
      | zero =>
        cases es with
        | nil => simp at hi
        | cons e' es' =>
          simp only [checkCoverage.checkContiguous] at hcov
          by_cases h' : e'.domain.lo = e.domain.hi
          · exact h'.symm
          · simp only [ne_eq, h', not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov
      | succ j =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        exact checkContiguous_adjacent_aux es e.domain.hi domain hcov j hi
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov

/-- Helper: integrability on a subinterval -/
private theorem integrable_subinterval (f : ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b)
    (hInt : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable f MeasureTheory.volume c d := by
  apply IntervalIntegrable.mono_set hInt
  rw [Set.uIcc_subset_uIcc_iff_le]
  simp only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
  exact ⟨hac, hdb⟩

/-- Coverage implies list is nonempty -/
private theorem coverage_nonempty (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) : entries ≠ [] := by
  intro h
  simp only [h, checkCoverage, Bool.false_eq_true] at hcov

/-- Helper: coverage on cons implies checkContiguous on tail -/
private theorem coverage_tail_contiguous (e : PartitionEntry) (es : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage (e :: es) domain = true) :
    checkCoverage.checkContiguous domain es e.domain.hi = true := by
  simp only [checkCoverage] at hcov
  by_cases h : e.domain.lo = domain.lo
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcov
    exact hcov
  · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov

/-- Helper: every entry's hi ≤ domain.hi when checkContiguous holds -/
private theorem contiguous_all_hi_le_domain_hi (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true) :
    ∀ e ∈ es, e.domain.hi ≤ domain.hi := by
  induction es generalizing lastHi with
  | nil => intro e he; simp at he
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous] at hcheck
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
      intro e' he'
      simp only [List.mem_cons] at he'
      cases he' with
      | inl heq =>
        rw [heq]
        cases es' with
        | nil =>
          simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcheck
          exact le_of_eq hcheck
        | cons e'' es'' =>
          have hrec := ih e.domain.hi hcheck
          have he''_mem : e'' ∈ (e'' :: es'') := by simp
          have he''_hi := hrec e'' he''_mem
          simp only [checkCoverage.checkContiguous] at hcheck
          by_cases h' : e''.domain.lo = e.domain.hi
          · calc e.domain.hi = e''.domain.lo := h'.symm
              _ ≤ e''.domain.hi := e''.domain.le
              _ ≤ domain.hi := he''_hi
          · simp only [ne_eq, h', not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck
      | inr hmem =>
        exact ih e.domain.hi hcheck e' hmem
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck

/-- Helper: monotonicity of entry endpoints in a contiguous partition -/
private theorem contiguous_entry_le_domain_hi (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true)
    (i : ℕ) (hi : i < es.length) :
    (es[i]'hi).domain.hi ≤ domain.hi := by
  have hall := contiguous_all_hi_le_domain_hi es lastHi domain hcheck
  exact hall (es[i]'hi) (List.getElem_mem hi)

/-- Helper: first entry hi ≤ domain.hi -/
private theorem coverage_first_hi_le (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (hne : entries ≠ []) :
    (entries.head hne).domain.hi ≤ domain.hi := by
  cases entries with
  | nil => simp at hne
  | cons e es =>
    simp only [List.head_cons]
    have hcontig := coverage_tail_contiguous e es domain hcov
    cases es with
    | nil =>
      simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcontig
      exact le_of_eq hcontig
    | cons e' es' =>
      exact contiguous_entry_le_domain_hi (e' :: es') e.domain.hi domain hcontig 0 (by simp) |>
        fun h => le_trans (by
          have := coverage_adjacent (e :: e' :: es') domain hcov 0 (by simp)
          simp at this
          calc e.domain.hi = e'.domain.lo := this
            _ ≤ e'.domain.hi := e'.domain.le) h

/-- Helper: every entry's hi ≤ domain.hi when coverage holds -/
private theorem coverage_entry_hi_le_domain_hi (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true)
    (i : ℕ) (hi : i < entries.length) :
    (entries[i]'hi).domain.hi ≤ domain.hi := by
  cases entries with
  | nil => simp at hi
  | cons e es =>
    have hcontig := coverage_tail_contiguous e es domain hcov
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact coverage_first_hi_le (e :: es) domain hcov (by simp)
    | succ j =>
      simp only [List.getElem_cons_succ]
      exact contiguous_entry_le_domain_hi es e.domain.hi domain hcontig j (by simp at hi; omega)

/-- Helper: every entry's lo ≥ domain.lo when coverage holds -/
private theorem coverage_entry_lo_ge_domain_lo (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true)
    (i : ℕ) (hi : i < entries.length) :
    domain.lo ≤ (entries[i]'hi).domain.lo := by
  cases i with
  | zero =>
    cases entries with
    | nil => simp at hi
    | cons e es =>
      simp only [List.getElem_cons_zero]
      have hfirst := coverage_first_starts (e :: es) domain hcov (by simp)
      simp only [List.head_cons] at hfirst
      exact le_of_eq hfirst.symm
  | succ j =>
    cases entries with
    | nil => simp at hi
    | cons e es =>
      simp only [List.getElem_cons_succ]
      have hfirst := coverage_first_starts (e :: es) domain hcov (by simp)
      simp only [List.head_cons] at hfirst
      -- entry[j+1].lo = entry[j].hi by adjacency, and entry[j].hi ≥ domain.lo
      -- by induction on j
      have hadj : ∀ k (hk : k + 1 < (e :: es).length),
          (e :: es)[k].domain.hi = (e :: es)[k + 1].domain.lo :=
        coverage_adjacent (e :: es) domain hcov
      have hentry_lo : domain.lo ≤ e.domain.lo := le_of_eq hfirst.symm
      -- Show by induction: domain.lo ≤ entry[k].lo for all k
      have hrec : ∀ k (hk : k < es.length), domain.lo ≤ es[k].domain.lo := by
        intro k hk
        induction k with
        | zero =>
          cases es with
          | nil => simp at hk
          | cons e' es' =>
            simp only [List.getElem_cons_zero]
            have h01 := hadj 0 (by simp)
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h01
            calc domain.lo ≤ e.domain.lo := hentry_lo
              _ ≤ e.domain.hi := e.domain.le
              _ = e'.domain.lo := h01
        | succ m ih =>
          have hm : m < es.length := by omega
          have hm1 : m + 1 < (e :: es).length := by simp; omega
          have hk1 := hadj (m + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at hk1
          calc domain.lo ≤ es[m].domain.lo := ih hm
            _ ≤ es[m].domain.hi := es[m].domain.le
            _ = es[m + 1].domain.lo := hk1
      exact hrec j (by simp at hi; omega)

/-- Helper: checkContiguous only depends on domain.hi -/
private theorem checkContiguous_depends_only_on_hi (es : List PartitionEntry)
    (dom1 dom2 : IntervalRat) (lastHi : ℚ)
    (hhi : dom1.hi = dom2.hi) :
    checkCoverage.checkContiguous dom1 es lastHi = checkCoverage.checkContiguous dom2 es lastHi := by
  induction es generalizing lastHi with
  | nil => simp only [checkCoverage.checkContiguous, hhi]
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous]
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih e.domain.hi
    · simp only [ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte]

/-- Helper: checkContiguous implies checkCoverage on tail with adjusted domain -/
private theorem contiguous_to_coverage_tail (e' : PartitionEntry) (es' : List PartitionEntry)
    (lastHi : ℚ) (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain (e' :: es') lastHi = true)
    (hlastHi_eq : e'.domain.lo = lastHi)
    (hle : lastHi ≤ domain.hi) :
    checkCoverage (e' :: es') ⟨lastHi, domain.hi, hle⟩ = true := by
  simp only [checkCoverage]
  simp only [hlastHi_eq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  simp only [checkCoverage.checkContiguous] at hcheck
  by_cases h : e'.domain.lo = lastHi
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
    -- checkContiguous only depends on domain.hi, which is the same
    rw [checkContiguous_depends_only_on_hi es' ⟨lastHi, domain.hi, hle⟩ domain e'.domain.hi rfl]
    exact hcheck
  · exact absurd hlastHi_eq h

theorem coverage_integral_sum (f : ℝ → ℝ) (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true)
    (hInt : IntervalIntegrable f MeasureTheory.volume domain.lo domain.hi) :
    ∫ x in (domain.lo : ℝ)..(domain.hi : ℝ), f x =
      (entries.map (fun e => ∫ x in (e.domain.lo : ℝ)..(e.domain.hi : ℝ), f x)).sum := by
  have hne : entries ≠ [] := coverage_nonempty entries domain hcov
  induction entries generalizing domain with
  | nil => exact absurd rfl hne
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons]
    cases es with
    | nil =>
      -- Single entry: e covers the whole domain
      simp only [List.map_nil, List.sum_nil, add_zero]
      have hfirst := coverage_first_starts [e] domain hcov (by simp)
      have hlast := coverage_last_ends [e] domain hcov (by simp)
      simp only [List.head_cons, List.getLast_singleton] at hfirst hlast
      rw [hfirst, hlast]
    | cons e' es' =>
      -- Multiple entries: use integral additivity
      have hfirst := coverage_first_starts (e :: e' :: es') domain hcov (by simp)
      simp only [List.head_cons] at hfirst
      have hadj := coverage_adjacent (e :: e' :: es') domain hcov 0 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hadj
      -- Key: split integral at e.domain.hi
      have hhi_le : e.domain.hi ≤ domain.hi := coverage_first_hi_le (e :: e' :: es') domain hcov (by simp)
      have hlo_le : domain.lo ≤ e.domain.hi := by
        have h := e.domain.le; rw [hfirst] at h; exact h
      -- Build tail domain
      let tailDomain : IntervalRat := ⟨e.domain.hi, domain.hi, hhi_le⟩
      -- Show tail has coverage
      have hcontig := coverage_tail_contiguous e (e' :: es') domain hcov
      have htail_cov : checkCoverage (e' :: es') tailDomain = true :=
        contiguous_to_coverage_tail e' es' e.domain.hi domain hcontig hadj.symm hhi_le
      -- Integrability on subintervals
      have hInt_e : IntervalIntegrable f MeasureTheory.volume e.domain.lo e.domain.hi := by
        apply integrable_subinterval f domain.lo domain.hi e.domain.lo e.domain.hi
          (Rat.cast_le.mpr domain.le) (Rat.cast_le.mpr e.domain.le)
        · exact Rat.cast_le.mpr (le_of_eq hfirst.symm)
        · exact Rat.cast_le.mpr hhi_le
        · exact hInt
      have hInt_tail : IntervalIntegrable f MeasureTheory.volume tailDomain.lo tailDomain.hi := by
        apply integrable_subinterval f domain.lo domain.hi tailDomain.lo tailDomain.hi
          (Rat.cast_le.mpr domain.le) (Rat.cast_le.mpr tailDomain.le)
        · exact Rat.cast_le.mpr hlo_le
        · exact le_refl _
        · exact hInt
      -- Use IH on tail (es = e' :: es')
      -- IH signature: domain → coverage → integrability → nonempty → result
      have hne_tail : (e' :: es') ≠ [] := by simp
      have ih_result := ih tailDomain htail_cov hInt_tail hne_tail
      -- Use integral additivity: ∫[a,b] + ∫[b,c] = ∫[a,c]
      have h_add := intervalIntegral.integral_add_adjacent_intervals hInt_e hInt_tail
      -- tailDomain = ⟨e.domain.hi, domain.hi, _⟩, so tailDomain.hi = domain.hi
      have htail_hi_eq : (tailDomain.hi : ℝ) = (domain.hi : ℝ) := rfl
      -- Substitute in h_add and ih_result
      simp only [htail_hi_eq] at h_add ih_result
      -- Goal: ∫[domain.lo, domain.hi] = ∫[e.lo, e.hi] + sum(rest)
      -- hfirst: e.domain.lo = domain.lo (in ℚ)
      -- h_add: ∫[e.lo, e.hi] + ∫[e.hi, domain.hi] = ∫[e.lo, domain.hi]
      -- ih_result: ∫[e.hi, domain.hi] = sum(rest)
      have hfirst_cast : (e.domain.lo : ℝ) = (domain.lo : ℝ) := by exact_mod_cast hfirst
      rw [← hfirst_cast]
      -- Goal: ∫[e.lo, domain.hi] = ∫[e.lo, e.hi] + sum(rest)
      rw [← h_add, ih_result]

/-- **Main Soundness Theorem for Certificate-Based Integration**

If verifyCertificate returns true, the actual integral is in the target interval.
This is the key theorem that makes certificate-based verification sound.

The proof proceeds as follows:
1. Extract the three conditions from verifyCertificate = true
2. Use coverage_integral_sum to write total integral as sum of partition integrals
3. Use partition_bound_correct to show each partition integral ∈ its bound
4. Use sum_mem_sum_intervals to show the sum of integrals ∈ sum of bounds
5. Use checkSumInTarget to show sum of bounds ⊆ target
-/
theorem verify_certificate_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (cert : IntegralCertificate) (target : IntervalRat)
    (hverify : verifyCertificate e cert target = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (cert.domain.lo : ℝ) (cert.domain.hi : ℝ)) :
    ∫ x in (cert.domain.lo : ℝ)..(cert.domain.hi : ℝ),
      Expr.eval (fun _ => x) e ∈ target := by
  -- Unpack verifyCertificate into its three conditions
  simp only [verifyCertificate, Bool.and_eq_true] at hverify
  obtain ⟨⟨hcov, hbounds⟩, hsum⟩ := hverify
  -- Extract checkAllBounds
  simp only [checkAllBounds, List.all_eq_true] at hbounds
  -- Extract checkSumInTarget
  simp only [checkSumInTarget, decide_eq_true_eq] at hsum
  -- Step 1: Rewrite integral as sum of partition integrals
  have h_sum_eq := coverage_integral_sum (fun x => Expr.eval (fun _ => x) e)
    cert.partitions cert.domain hcov hInt
  rw [h_sum_eq]
  -- Define the values and bounds lists
  set integrals := cert.partitions.map fun entry =>
    ∫ x in (entry.domain.lo : ℝ)..(entry.domain.hi : ℝ), Expr.eval (fun _ => x) e with h_integrals
  set bounds := cert.partitions.map fun entry => entry.bound with h_bounds
  -- Step 2: Each partition integral is in its bound
  have hlen : integrals.length = bounds.length := by
    simp only [h_integrals, h_bounds, List.length_map]
  have hmem : ∀ i (hi : i < integrals.length),
      integrals[i] ∈ (bounds[i]'(hlen ▸ hi)) := by
    intro i hi
    simp only [h_integrals, h_bounds, List.getElem_map]
    have hi' : i < cert.partitions.length := by
      simp only [h_integrals, List.length_map] at hi; exact hi
    let entry := cert.partitions[i]'hi'
    have hcheck := hbounds entry (List.getElem_mem hi')
    have hInt_i : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
        MeasureTheory.volume entry.domain.lo entry.domain.hi := by
      -- Integrability on subinterval - entry ⊆ domain by coverage
      have hlo := coverage_entry_lo_ge_domain_lo cert.partitions cert.domain hcov i hi'
      have hhi := coverage_entry_hi_le_domain_hi cert.partitions cert.domain hcov i hi'
      apply integrable_subinterval _ cert.domain.lo cert.domain.hi entry.domain.lo entry.domain.hi
        (Rat.cast_le.mpr cert.domain.le) (Rat.cast_le.mpr entry.domain.le)
        (Rat.cast_le.mpr hlo) (Rat.cast_le.mpr hhi) hInt
    exact partition_bound_correct e hsupp entry hcheck hInt_i
  -- Step 3: Apply sum_mem_sum_intervals
  have h_in_sum := sum_mem_sum_intervals integrals bounds hlen hmem
  -- The sumBounds equals foldl add zero bounds
  have h_sumBounds_eq : sumBounds cert.partitions =
      bounds.foldl (fun acc I => IntervalRat.add acc I) ⟨0, 0, le_refl 0⟩ := by
    simp only [sumBounds, h_bounds]
    -- Use foldl_map: foldl f init (map g l) = foldl (fun acc x => f acc (g x)) init l
    rw [List.foldl_map]
  -- Membership in sumBounds implies membership in target
  have h_in_bounds : integrals.sum ∈ sumBounds cert.partitions := by
    rw [h_sumBounds_eq]
    exact h_in_sum
  simp only [IntervalRat.mem_def] at h_in_bounds ⊢
  constructor
  · calc (target.lo : ℝ) ≤ (sumBounds cert.partitions).lo := by exact_mod_cast hsum.1
      _ ≤ integrals.sum := h_in_bounds.1
  · calc integrals.sum ≤ (sumBounds cert.partitions).hi := h_in_bounds.2
      _ ≤ target.hi := by exact_mod_cast hsum.2

/-! ### Certificate Generation

Generate certificates from the adaptive integration algorithm.
This captures the result of the search for later verification.
-/

/-- Build a certificate entry from a successful interval evaluation -/
def mkPartitionEntry (e : Expr) (domain : IntervalRat) : Option PartitionEntry :=
  match evalInterval?1 e domain with
  | none => none
  | some computed =>
    let width := domain.hi - domain.lo
    -- Use min/max to avoid ordering issues with potentially negative values
    let blo := min (computed.lo * width) (computed.hi * width)
    let bhi := max (computed.lo * width) (computed.hi * width)
    some {
      domain := domain
      bound := ⟨blo, bhi, le_max_of_le_left (min_le_left _ _)⟩
    }

/-- Helper: midpoint is between lo and hi -/
private theorem midpoint_le_hi (lo hi : ℚ) (h : lo ≤ hi) : (lo + hi) / 2 ≤ hi := by
  linarith

private theorem lo_le_midpoint (lo hi : ℚ) (h : lo ≤ hi) : lo ≤ (lo + hi) / 2 := by
  linarith

/-- Recursively build certificate from adaptive search -/
partial def buildCertificateAux (e : Expr) (domain : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : Option (List PartitionEntry) :=
  if maxDepth = 0 then
    -- Base case: try to build a single entry
    match mkPartitionEntry e domain with
    | some entry => some [entry]
    | none => none
  else
    -- Try single partition first
    match mkPartitionEntry e domain with
    | none => none  -- Domain invalid
    | some entry =>
      let width := entry.bound.hi - entry.bound.lo
      if width ≤ tol then
        some [entry]
      else
        -- Split and recurse
        let mid := (domain.lo + domain.hi) / 2
        let left : IntervalRat := ⟨domain.lo, mid, lo_le_midpoint domain.lo domain.hi domain.le⟩
        let right : IntervalRat := ⟨mid, domain.hi, midpoint_le_hi domain.lo domain.hi domain.le⟩
        match buildCertificateAux e left (tol / 2) (maxDepth - 1),
              buildCertificateAux e right (tol / 2) (maxDepth - 1) with
        | some leftEntries, some rightEntries => some (leftEntries ++ rightEntries)
        | _, _ => none

/-- Build an integration certificate using adaptive partitioning -/
def buildCertificate (e : Expr) (domain : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ := 20) (name : String := "integral") : Option IntegralCertificate :=
  match buildCertificateAux e domain tol maxDepth with
  | some entries => some {
      expr_id := name
      domain := domain
      partitions := entries
    }
  | none => none

/-! ### Golden Theorems for Certificate-Based Integration -/

/-- Check if an integral lower bound holds via certificate verification -/
def checkIntegralCertLowerBound (e : Expr) (cert : IntegralCertificate) (c : ℚ) : Bool :=
  checkCoverage cert.partitions cert.domain &&
  checkAllBounds e cert.partitions &&
  decide (c ≤ (sumBounds cert.partitions).lo)

/-- Check if an integral upper bound holds via certificate verification -/
def checkIntegralCertUpperBound (e : Expr) (cert : IntegralCertificate) (c : ℚ) : Bool :=
  checkCoverage cert.partitions cert.domain &&
  checkAllBounds e cert.partitions &&
  decide ((sumBounds cert.partitions).hi ≤ c)

/-- **Golden Theorem**: Certificate-verified integral lower bound -/
theorem verify_integral_cert_lower_bound (e : Expr) (hsupp : ExprSupportedWithInv e)
    (cert : IntegralCertificate) (c : ℚ)
    (hcheck : checkIntegralCertLowerBound e cert c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (cert.domain.lo : ℝ) (cert.domain.hi : ℝ)) :
    c ≤ ∫ x in (cert.domain.lo : ℝ)..(cert.domain.hi : ℝ), Expr.eval (fun _ => x) e := by
  simp only [checkIntegralCertLowerBound, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hcov, hbounds⟩, hlo⟩ := hcheck
  -- Build target interval [c, ∞) represented as [c, sumBounds.hi]
  let target : IntervalRat := ⟨c, (sumBounds cert.partitions).hi, by
    calc c ≤ (sumBounds cert.partitions).lo := hlo
      _ ≤ (sumBounds cert.partitions).hi := (sumBounds cert.partitions).le⟩
  -- checkSumInTarget target holds
  have hsum : checkSumInTarget cert.partitions target = true := by
    simp only [checkSumInTarget, decide_eq_true_eq]
    exact ⟨hlo, le_refl _⟩
  have hverify : verifyCertificate e cert target = true := by
    simp only [verifyCertificate, Bool.and_eq_true]
    exact ⟨⟨hcov, hbounds⟩, hsum⟩
  have hmem := verify_certificate_correct e hsupp cert target hverify hInt
  simp only [IntervalRat.mem_def] at hmem
  exact_mod_cast hmem.1

/-- **Golden Theorem**: Certificate-verified integral upper bound -/
theorem verify_integral_cert_upper_bound (e : Expr) (hsupp : ExprSupportedWithInv e)
    (cert : IntegralCertificate) (c : ℚ)
    (hcheck : checkIntegralCertUpperBound e cert c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (cert.domain.lo : ℝ) (cert.domain.hi : ℝ)) :
    ∫ x in (cert.domain.lo : ℝ)..(cert.domain.hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkIntegralCertUpperBound, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hcov, hbounds⟩, hhi⟩ := hcheck
  -- Build target interval (-∞, c] represented as [sumBounds.lo, c]
  let target : IntervalRat := ⟨(sumBounds cert.partitions).lo, c, by
    calc (sumBounds cert.partitions).lo ≤ (sumBounds cert.partitions).hi := (sumBounds cert.partitions).le
      _ ≤ c := hhi⟩
  -- checkSumInTarget target holds
  have hsum : checkSumInTarget cert.partitions target = true := by
    simp only [checkSumInTarget, decide_eq_true_eq]
    exact ⟨le_refl _, hhi⟩
  have hverify : verifyCertificate e cert target = true := by
    simp only [verifyCertificate, Bool.and_eq_true]
    exact ⟨⟨hcov, hbounds⟩, hsum⟩
  have hmem := verify_certificate_correct e hsupp cert target hverify hInt
  simp only [IntervalRat.mem_def] at hmem
  exact_mod_cast hmem.2

end LeanCert.Validity.CertificateIntegration
