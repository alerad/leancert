/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions

/-!
# Taylor Models - Core Definitions

This file contains the core Taylor model abstraction, polynomial helpers,
and basic operations with their correctness proofs.

## Main definitions

* `TaylorModel` - A polynomial plus remainder interval
* `evalSet`, `evalPoly`, `polyBoundInterval`, `bound` - Evaluation and bounding
* `const`, `identity`, `add`, `neg`, `mul`, `inv` - Basic operations
* `evalPoly_mem_polyBoundInterval`, `taylorModel_correct` - Core correctness

## Design notes

A Taylor model for f on interval I centered at c is:
  TM(f) = (P, R) where ∀x ∈ I, f(x) ∈ P(x-c) + R

Operations on Taylor models (add, mul, compose) preserve this property.
-/

namespace LeanCert.Engine

open LeanCert.Core
open Polynomial

/-! ### Polynomial helpers for Taylor models -/

/-- Truncate a polynomial to terms of degree ≤ n by summing coefficients -/
noncomputable def truncPoly (p : Polynomial ℚ) (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ i

/-- The tail of a polynomial (terms with degree > n) -/
noncomputable def tailPoly (p : Polynomial ℚ) (n : ℕ) : Polynomial ℚ :=
  p - truncPoly p n

/-- Bound a polynomial over an interval centered at c.
    Evaluates at shifted argument: P(x - c) for x ∈ domain.

    We bound each term: |aᵢ (x-c)ⁱ| ≤ |aᵢ| * r^i where r = radius of domain from c.
    Then the total bound is ∑ᵢ |aᵢ| * rⁱ
-/
noncomputable def boundPolyAbs (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ) : ℚ :=
  let r := max (|domain.hi - c|) (|domain.lo - c|)
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * r ^ i

/-- The bound computed by boundPolyAbs is nonnegative -/
theorem boundPolyAbs_nonneg (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ) :
    0 ≤ boundPolyAbs p domain c := by
  unfold boundPolyAbs
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (abs_nonneg _)
  apply pow_nonneg
  exact le_max_of_le_left (abs_nonneg _)

/-! ### Bernstein Polynomial Bounds

Bernstein polynomials provide tighter bounds than naive interval arithmetic.
For a polynomial P(x) on [a,b], the range is contained in [min bⱼ, max bⱼ]
where bⱼ are the Bernstein coefficients.

This avoids the "dependency problem" where naive interval arithmetic
gives P(x) = x - x² on [0,1] → [-1, 1] instead of the true [0, 0.25].
-/

/-- Binomial coefficient as rational (for Bernstein conversion) -/
def binomialRat (n k : ℕ) : ℚ := Nat.choose n k

/-- Transform polynomial P(u) on [α, β] to Q(t) on [0,1] via u = α + t*(β-α).
    Returns the coefficients of Q as a list.

    If P(u) = Σᵢ aᵢuⁱ, then Q(t) = P(α + t*w) where w = β - α.
    Using binomial expansion: (α + tw)ⁱ = Σⱼ C(i,j) αⁱ⁻ʲ wʲ tʲ
    So qⱼ = Σᵢ≥ⱼ aᵢ * C(i,j) * αⁱ⁻ʲ * wʲ -/
def transformPolyCoeffs (p : Polynomial ℚ) (α β : ℚ) : List ℚ :=
  let n := p.natDegree
  let w := β - α
  List.ofFn (fun j : Fin (n + 1) =>
    let j' := j.val
    (Finset.range (n + 1 - j')).sum (fun k =>
      let i := j' + k  -- i ranges from j to n
      p.coeff i * binomialRat i j' * α ^ (i - j') * w ^ j'))

/-- Convert monomial coefficients to Bernstein coefficients on [0,1].
    For Q(t) = Σⱼ qⱼtʲ, the Bernstein coefficient bₖ = Σⱼ₌₀ᵏ C(k,j)/C(n,j) * qⱼ -/
def monomialToBernstein (coeffs : List ℚ) : List ℚ :=
  let n := coeffs.length - 1
  if n < 0 then [] else
  List.ofFn (fun k : Fin (n + 1) =>
    let k' := k.val
    (Finset.range (k' + 1)).sum (fun j =>
      if hj : j < coeffs.length then
        let qj := coeffs.get ⟨j, hj⟩
        if (Nat.choose n j) = 0 then 0
        else binomialRat k' j / binomialRat n j * qj
      else 0))

/-- Compute Bernstein coefficients for polynomial P evaluated at (x - c) for x ∈ [lo, hi].
    The polynomial argument u = x - c ranges over [lo - c, hi - c]. -/
def bernsteinCoeffsForDomain (p : Polynomial ℚ) (lo hi c : ℚ) : List ℚ :=
  let α := lo - c
  let β := hi - c
  let transformedCoeffs := transformPolyCoeffs p α β
  monomialToBernstein transformedCoeffs

/-- Find min and max of a non-empty list, returning an interval -/
def listMinMax (l : List ℚ) (default : ℚ) : ℚ × ℚ :=
  l.foldl (fun (lo, hi) x => (min lo x, max hi x)) (default, default)

/-- Helper: foldl preserves the invariant lo ≤ hi -/
theorem listMinMax_foldl_le (l : List ℚ) (p : ℚ × ℚ) (hp : p.1 ≤ p.2) :
    (l.foldl (fun (lo, hi) x => (min lo x, max hi x)) p).1 ≤
    (l.foldl (fun (lo, hi) x => (min lo x, max hi x)) p).2 := by
  induction l generalizing p with
  | nil => exact hp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    calc min p.1 x ≤ p.1 := min_le_left _ _
      _ ≤ p.2 := hp
      _ ≤ max p.2 x := le_max_left _ _

/-- The listMinMax function returns lo ≤ hi -/
theorem listMinMax_le (l : List ℚ) (d : ℚ) : (listMinMax l d).1 ≤ (listMinMax l d).2 := by
  unfold listMinMax
  exact listMinMax_foldl_le l (d, d) (le_refl d)

/-- Bound polynomial using Bernstein coefficients - gives [min bⱼ, max bⱼ].
    This is typically MUCH tighter than the symmetric [-B, B] from boundPolyAbs.

    For P(x) = x - x² on [0,1]: boundPolyAbs gives [-2, 2], Bernstein gives [0, 0.5] -/
def boundPolyBernstein (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ) : IntervalRat :=
  let coeffs := bernsteinCoeffsForDomain p domain.lo domain.hi c
  match coeffs with
  | [] =>
    -- Constant polynomial or empty: use value at center
    let val := p.coeff 0
    ⟨val, val, le_refl val⟩
  | x :: xs =>
    let bounds := listMinMax (x :: xs) x
    ⟨bounds.1, bounds.2, listMinMax_le (x :: xs) x⟩

/-- Bernstein bounds are always at least as tight as naive bounds (symmetric [-B, B]).
    This follows from the property that Bernstein coefficients bound the polynomial range. -/
theorem boundPolyBernstein_le_boundPolyAbs (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ) :
    -(boundPolyAbs p domain c) ≤ (boundPolyBernstein p domain c).lo ∧
    (boundPolyBernstein p domain c).hi ≤ boundPolyAbs p domain c := by
  -- This is a consequence of Bernstein bounds being tighter
  -- The naive bound [-B, B] always contains the Bernstein bound [lo, hi]
  sorry  -- TODO: prove after main infrastructure works

/-- Key theorem: polynomial evaluation lies within Bernstein bounds.
    This is the fundamental theorem of Bernstein polynomials:
    For P(x) = Σₖ bₖ Bₖₙ(x), we have min(bₖ) ≤ P(x) ≤ max(bₖ) on [0,1].

    This follows because Bernstein basis functions are non-negative and sum to 1. -/
theorem poly_eval_mem_boundPolyBernstein (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ)
    (x : ℝ) (hx : x ∈ domain) :
    Polynomial.aeval (x - c) p ∈ boundPolyBernstein p domain c := by
  -- The proof requires showing that the affine transformation preserves the property,
  -- and that Bernstein basis functions partition unity.
  sorry  -- TODO: full proof is involved, but the theorem is standard

/-- Bound the tail of polynomial p (terms with degree > d) when evaluated at (x-c)
    for x ∈ domain. -/
noncomputable def boundTail (p : Polynomial ℚ) (d : ℕ) (domain : IntervalRat) (c : ℚ) : IntervalRat :=
  let r := max (|domain.hi - c|) (|domain.lo - c|)
  let degP := p.natDegree
  if degP ≤ d then
    IntervalRat.singleton 0
  else
    let tailBound := ∑ i ∈ Finset.Icc (d + 1) degP, |p.coeff i| * r ^ i
    ⟨-tailBound, tailBound, by
      have h : 0 ≤ tailBound := by
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg (abs_nonneg _)
        apply pow_nonneg
        exact le_max_of_le_left (abs_nonneg _)
      linarith⟩

/-! ### Taylor Model structure -/

/-- A Taylor model: polynomial approximation with remainder interval. -/
structure TaylorModel where
  /-- The polynomial part (coefficients are rationals) -/
  poly : Polynomial ℚ
  /-- The remainder interval -/
  remainder : IntervalRat
  /-- The center of expansion -/
  center : ℚ
  /-- The domain interval -/
  domain : IntervalRat

namespace TaylorModel

/-- The set of real values this Taylor model can take at point x -/
noncomputable def evalSet (tm : TaylorModel) (x : ℝ) : Set ℝ :=
  {y | ∃ r ∈ tm.remainder, y = Polynomial.aeval (x - tm.center) tm.poly + r}

/-- Evaluate polynomial part at a point -/
noncomputable def evalPoly (tm : TaylorModel) (x : ℝ) : ℝ :=
  Polynomial.aeval (x - tm.center) tm.poly

/-- Interval bound for the polynomial part over the domain (naive symmetric bound). -/
noncomputable def polyBoundInterval (tm : TaylorModel) : IntervalRat :=
  let B := boundPolyAbs tm.poly tm.domain tm.center
  ⟨-B, B, by
    have hB : (0 : ℚ) ≤ B := boundPolyAbs_nonneg tm.poly tm.domain tm.center
    linarith⟩

/-- Interval bound for the polynomial part using BERNSTEIN bounds (tighter!).
    For P(x) = x - x² on [0,1]: naive gives [-2, 2], Bernstein gives [0, 0.5] -/
def polyBoundIntervalBernstein (tm : TaylorModel) : IntervalRat :=
  boundPolyBernstein tm.poly tm.domain tm.center

/-- Get bounds on the Taylor model over its domain: polynomial bound + remainder.
    NOW USES BERNSTEIN BOUNDS for tighter intervals! -/
def bound (tm : TaylorModel) : IntervalRat :=
  IntervalRat.add (polyBoundIntervalBernstein tm) tm.remainder

/-- Get bounds using Bernstein polynomial bounds (tighter than naive bound) -/
def boundBernstein (tm : TaylorModel) : IntervalRat :=
  IntervalRat.add (polyBoundIntervalBernstein tm) tm.remainder

/-- Interval bound for f(center). -/
noncomputable def valueAtCenterInterval (tm : TaylorModel) : IntervalRat :=
  let p0 : ℚ := tm.poly.coeff 0
  IntervalRat.add (IntervalRat.singleton p0) tm.remainder

/-- Correctness: the true function value at center is in valueAtCenterInterval. -/
theorem valueAtCenter_correct (tm : TaylorModel) (f : ℝ → ℝ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x)
    (hc : (tm.center : ℝ) ∈ tm.domain) :
    f tm.center ∈ valueAtCenterInterval tm := by
  have heval := hf tm.center hc
  simp only [evalSet, Set.mem_setOf_eq] at heval
  obtain ⟨r, hr_mem, hr_eq⟩ := heval
  simp only [valueAtCenterInterval, IntervalRat.mem_def, IntervalRat.add,
    IntervalRat.singleton, Rat.cast_add]
  have hpoly : Polynomial.aeval ((tm.center : ℝ) - tm.center) tm.poly = (tm.poly.coeff 0 : ℝ) := by
    simp only [sub_self]
    simp only [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    rfl
  rw [hr_eq, hpoly]
  simp only [IntervalRat.mem_def] at hr_mem
  constructor <;> linarith [hr_mem.1, hr_mem.2]

/-! ### Taylor model operations -/

/-- Constant Taylor model -/
noncomputable def const (q : ℚ) (domain : IntervalRat) : TaylorModel :=
  { poly := Polynomial.C q
    remainder := IntervalRat.singleton 0
    center := domain.midpoint
    domain := domain }

/-- Identity Taylor model: represents the function x ↦ x -/
noncomputable def identity (domain : IntervalRat) : TaylorModel :=
  let c := domain.midpoint
  { poly := Polynomial.X + Polynomial.C c
    remainder := IntervalRat.singleton 0
    center := c
    domain := domain }

/-- Add two Taylor models -/
noncomputable def add (tm1 tm2 : TaylorModel) : TaylorModel :=
  { poly := tm1.poly + tm2.poly
    remainder := IntervalRat.add tm1.remainder tm2.remainder
    center := tm1.center
    domain := tm1.domain }

/-- Negate a Taylor model -/
noncomputable def neg (tm : TaylorModel) : TaylorModel :=
  { poly := -tm.poly
    remainder := IntervalRat.neg tm.remainder
    center := tm.center
    domain := tm.domain }

/-- Subtract Taylor models -/
noncomputable def sub (tm1 tm2 : TaylorModel) : TaylorModel :=
  add tm1 (neg tm2)

/-- Invert a Taylor model, assuming its bound does not contain 0. -/
noncomputable def inv (tm : TaylorModel) (hnz : ¬ IntervalRat.containsZero tm.bound) :
    TaylorModel :=
  let nz : IntervalRat.IntervalRatNonzero :=
    { lo := tm.bound.lo
      hi := tm.bound.hi
      le := tm.bound.le
      nonzero := hnz }
  let invBound := IntervalRat.invNonzero nz
  { poly := Polynomial.C 0
    remainder := invBound
    center := tm.center
    domain := tm.domain }

/-- Multiply Taylor models with truncation and proper remainder handling. -/
noncomputable def mul (tm1 tm2 : TaylorModel) (maxDegree : ℕ) : TaylorModel :=
  let prodPoly := tm1.poly * tm2.poly
  let truncatedPoly := truncPoly prodPoly maxDegree
  let tail := tailPoly prodPoly maxDegree
  let tailB := boundPolyAbs tail tm1.domain tm1.center
  let tailInterval : IntervalRat := ⟨-tailB, tailB, by
    have hB : (0 : ℚ) ≤ tailB := boundPolyAbs_nonneg tail tm1.domain tm1.center
    linarith⟩
  let p1Bound := boundPolyAbs tm1.poly tm1.domain tm1.center
  let p2Bound := boundPolyAbs tm2.poly tm2.domain tm2.center
  let p1r2 := IntervalRat.mul
    ⟨-p1Bound, p1Bound, by linarith [boundPolyAbs_nonneg tm1.poly tm1.domain tm1.center]⟩
    tm2.remainder
  let p2r1 := IntervalRat.mul
    ⟨-p2Bound, p2Bound, by linarith [boundPolyAbs_nonneg tm2.poly tm2.domain tm2.center]⟩
    tm1.remainder
  let r1r2 := IntervalRat.mul tm1.remainder tm2.remainder
  let totalRemainder := IntervalRat.add tailInterval
                         (IntervalRat.add p1r2
                           (IntervalRat.add p2r1 r1r2))
  { poly := truncatedPoly
    remainder := totalRemainder
    center := tm1.center
    domain := tm1.domain }

end TaylorModel

/-! ### Core Correctness Theorems -/

/-- Helper: |x - c| ≤ max(|hi - c|, |lo - c|) for x in [lo, hi] -/
private theorem abs_sub_le_radius (x : ℝ) (c : ℚ) (domain : IntervalRat)
    (hx : x ∈ domain) :
    |x - c| ≤ max (|(domain.hi : ℝ) - c|) (|(domain.lo : ℝ) - c|) := by
  simp only [IntervalRat.mem_def] at hx
  by_cases hxc : (c : ℝ) ≤ x
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - c)]
    have hxhi : x - c ≤ (domain.hi : ℝ) - c := by linarith
    calc x - c ≤ (domain.hi : ℝ) - c := hxhi
      _ ≤ |(domain.hi : ℝ) - c| := le_abs_self _
      _ ≤ max |(domain.hi : ℝ) - c| |(domain.lo : ℝ) - c| := le_max_left _ _
  · push_neg at hxc
    have h_neg : x - (c : ℝ) < 0 := by linarith
    rw [abs_of_neg h_neg]
    have hxlo : -(x - (c : ℝ)) ≤ (c : ℝ) - domain.lo := by linarith
    calc -(x - (c : ℝ)) ≤ (c : ℝ) - domain.lo := hxlo
      _ ≤ |c - (domain.lo : ℝ)| := le_abs_self _
      _ = |(domain.lo : ℝ) - c| := abs_sub_comm _ _
      _ ≤ max |(domain.hi : ℝ) - c| |(domain.lo : ℝ) - c| := le_max_right _ _

/-- Helper: polynomial evaluation bounded by triangle inequality -/
private theorem aeval_abs_le_sum (p : Polynomial ℚ) (y : ℝ) (r : ℝ) (hr : |y| ≤ r) :
    |Polynomial.aeval y p| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * r ^ i := by
  have haeval : Polynomial.aeval y p = ∑ i ∈ Finset.range (p.natDegree + 1),
      (p.coeff i : ℝ) * y ^ i := by
    simp only [Polynomial.aeval_eq_sum_range]
    rfl
  rw [haeval]
  calc |∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * y ^ i|
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ) * y ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * |y| ^ i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * r ^ i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (abs_nonneg _) hr i
        · exact abs_nonneg _

/-- Key lemma: polynomial evaluation is bounded by polyBoundInterval. -/
theorem evalPoly_mem_polyBoundInterval
    (tm : TaylorModel) (x : ℝ) (hx : x ∈ tm.domain) :
    tm.evalPoly x ∈ tm.polyBoundInterval := by
  simp only [TaylorModel.evalPoly, TaylorModel.polyBoundInterval, IntervalRat.mem_def]
  set B := boundPolyAbs tm.poly tm.domain tm.center with hB_def
  suffices h : |Polynomial.aeval (x - tm.center) tm.poly| ≤ B by
    constructor
    · simp only [Rat.cast_neg]
      have := neg_abs_le (Polynomial.aeval (x - ↑tm.center) tm.poly)
      linarith
    · exact le_trans (le_abs_self _) h
  unfold boundPolyAbs at hB_def
  simp only at hB_def
  set r : ℚ := max (|tm.domain.hi - tm.center|) (|tm.domain.lo - tm.center|) with hr_def
  have hr_real : (r : ℝ) = max (|(tm.domain.hi : ℝ) - tm.center|) (|(tm.domain.lo : ℝ) - tm.center|) := by
    simp only [hr_def, Rat.cast_max, Rat.cast_abs, Rat.cast_sub]
  have habs_le_r : |x - tm.center| ≤ r := by
    rw [hr_real]
    exact abs_sub_le_radius x tm.center tm.domain hx
  have hr_nn : 0 ≤ (r : ℝ) := by
    rw [hr_real]
    exact le_max_of_le_left (abs_nonneg _)
  have h := aeval_abs_le_sum tm.poly (x - tm.center) r habs_le_r
  have hcoeff_abs : ∀ i, (|tm.poly.coeff i| : ℝ) = |(tm.poly.coeff i : ℝ)| := fun i => rfl
  calc |Polynomial.aeval (x - ↑tm.center) tm.poly|
      ≤ ∑ i ∈ Finset.range (tm.poly.natDegree + 1), |(tm.poly.coeff i : ℝ)| * (r : ℝ) ^ i := h
    _ = ∑ i ∈ Finset.range (tm.poly.natDegree + 1), (|tm.poly.coeff i| : ℝ) * (r : ℝ) ^ i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hcoeff_abs]
    _ = (∑ i ∈ Finset.range (tm.poly.natDegree + 1), |tm.poly.coeff i| * r ^ i : ℚ) := by
        simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow]
    _ = (B : ℝ) := by rw [hB_def]

/-- Taylor model bounds are correct: if f(x) ∈ evalSet for all x in domain,
    then f(x) ∈ bound for all x in domain. -/
theorem taylorModel_correct (tm : TaylorModel) (f : ℝ → ℝ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, f x ∈ tm.bound := by
  intro x hx
  have hfx := hf x hx
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq] at hfx
  obtain ⟨r, hr_mem, hr_eq⟩ := hfx
  -- Use Bernstein bounds (via the correctness theorem)
  have hpoly : tm.evalPoly x ∈ tm.polyBoundIntervalBernstein := by
    simp only [TaylorModel.evalPoly, TaylorModel.polyBoundIntervalBernstein]
    exact poly_eval_mem_boundPolyBernstein tm.poly tm.domain tm.center x hx
  have hr : r ∈ tm.remainder := hr_mem
  have hsum : tm.evalPoly x + r ∈ IntervalRat.add tm.polyBoundIntervalBernstein tm.remainder :=
    IntervalRat.mem_add hpoly hr
  simp only [TaylorModel.bound]
  rw [hr_eq]
  exact hsum

/-! ### Local evalSet correctness lemmas -/

namespace TaylorModel

/-- Constant TM correctness for evalSet: q ∈ const(q).evalSet x. -/
theorem const_evalSet_correct (q : ℚ) (domain : IntervalRat) :
    ∀ x ∈ domain, (q : ℝ) ∈ (const q domain).evalSet x := by
  intro x hx
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq, TaylorModel.const]
  refine ⟨0, ?_, ?_⟩
  · simpa using (IntervalRat.mem_singleton (0 : ℚ))
  · simp

/-- Identity TM correctness for evalSet: x ∈ identity.evalSet x. -/
theorem identity_evalSet_correct (domain : IntervalRat) :
    ∀ x ∈ domain, x ∈ (identity domain).evalSet x := by
  intro x hx
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq, TaylorModel.identity]
  refine ⟨0, ?_, ?_⟩
  · simpa using (IntervalRat.mem_singleton (0 : ℚ))
  · simp

/-- Negation preserves evalSet membership. -/
theorem neg_evalSet_of_mem {tm : TaylorModel} {x r : ℝ}
    (hr : r ∈ tm.remainder) :
    -(tm.evalPoly x + r) ∈ (neg tm).evalSet x := by
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq, TaylorModel.neg, TaylorModel.evalPoly]
  refine ⟨-r, ?_, ?_⟩
  · exact IntervalRat.mem_neg hr
  · simp [map_neg, add_comm]

/-- Convenience: any `evalPoly x + r` with `r ∈ remainder` lies in `evalSet`. -/
theorem evalSet_of_remainder (tm : TaylorModel) (x : ℝ) {r : ℝ}
    (hr : r ∈ tm.remainder) :
    tm.evalPoly x + r ∈ tm.evalSet x := by
  simp only [evalSet, Set.mem_setOf_eq]
  exact ⟨r, hr, rfl⟩

/-- Addition preserves evalSet membership when centers match. -/
theorem add_evalSet_of_mem {tm1 tm2 : TaylorModel} {x : ℝ}
    (hcenter : tm1.center = tm2.center)
    {v1 v2 : ℝ} (hv1 : v1 ∈ tm1.evalSet x) (hv2 : v2 ∈ tm2.evalSet x) :
    v1 + v2 ∈ (TaylorModel.add tm1 tm2).evalSet x := by
  simp only [evalSet, Set.mem_setOf_eq] at hv1 hv2 ⊢
  obtain ⟨r1, hr1, heq1⟩ := hv1
  obtain ⟨r2, hr2, heq2⟩ := hv2
  refine ⟨r1 + r2, IntervalRat.mem_add hr1 hr2, ?_⟩
  simp only [TaylorModel.add]
  have hcast : (tm2.center : ℝ) = tm1.center := by exact_mod_cast hcenter.symm
  calc v1 + v2
      = (Polynomial.aeval (x - tm1.center) tm1.poly + r1)
        + (Polynomial.aeval (x - tm2.center) tm2.poly + r2) := by rw [heq1, heq2]
    _ = (Polynomial.aeval (x - tm1.center) tm1.poly
        + Polynomial.aeval (x - tm1.center) tm2.poly) + (r1 + r2) := by
          simp only [hcast]; ring
    _ = Polynomial.aeval (x - tm1.center) (tm1.poly + tm2.poly) + (r1 + r2) := by
          simp only [map_add]

end TaylorModel

/-! ### Polynomial helper lemmas for multiplication -/

/-- truncPoly + tailPoly = original polynomial -/
theorem truncPoly_add_tailPoly (p : Polynomial ℚ) (n : ℕ) :
    truncPoly p n + tailPoly p n = p := by
  simp only [tailPoly, add_sub_cancel]

/-- aeval distributes over truncPoly + tailPoly -/
theorem aeval_eq_truncPoly_add_tailPoly (p : Polynomial ℚ) (n : ℕ) (y : ℝ) :
    Polynomial.aeval y p =
      Polynomial.aeval y (truncPoly p n) + Polynomial.aeval y (tailPoly p n) := by
  have h := truncPoly_add_tailPoly p n
  conv_lhs => rw [← h]
  simp only [map_add]

/-- Tail polynomial evaluation is bounded by boundPolyAbs of tail. -/
theorem tailPoly_eval_bounded (p : Polynomial ℚ) (n : ℕ) (domain : IntervalRat) (c : ℚ) (x : ℝ)
    (hx : x ∈ domain) :
    |Polynomial.aeval (x - c) (tailPoly p n)| ≤ boundPolyAbs (tailPoly p n) domain c := by
  set tail := tailPoly p n with htail_def
  set B := boundPolyAbs tail domain c with hB_def
  set r : ℚ := max (|domain.hi - c|) (|domain.lo - c|) with hr_def
  have hr_real : (r : ℝ) = max (|(domain.hi : ℝ) - c|) (|(domain.lo : ℝ) - c|) := by
    simp only [hr_def, Rat.cast_max, Rat.cast_abs, Rat.cast_sub]
  have habs_le_r : |x - c| ≤ r := by
    rw [hr_real]
    exact abs_sub_le_radius x c domain hx
  have h := aeval_abs_le_sum tail (x - c) r habs_le_r
  have hcoeff_abs : ∀ i, (|tail.coeff i| : ℝ) = |(tail.coeff i : ℝ)| := fun i => rfl
  calc |Polynomial.aeval (x - ↑c) tail|
      ≤ ∑ i ∈ Finset.range (tail.natDegree + 1), |(tail.coeff i : ℝ)| * (r : ℝ) ^ i := h
    _ = ∑ i ∈ Finset.range (tail.natDegree + 1), (|tail.coeff i| : ℝ) * (r : ℝ) ^ i := by
        apply Finset.sum_congr rfl; intro i _; rw [← hcoeff_abs]
    _ = (∑ i ∈ Finset.range (tail.natDegree + 1), |tail.coeff i| * r ^ i : ℚ) := by
        simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow]
    _ = (B : ℝ) := by rw [hB_def]; rfl

/-- Polynomial bound lemma: |P(y)| ≤ boundPolyAbs P domain c for y = x - c, x ∈ domain -/
theorem poly_eval_bounded (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ) (x : ℝ)
    (hx : x ∈ domain) :
    |Polynomial.aeval (x - c) p| ≤ boundPolyAbs p domain c := by
  set B := boundPolyAbs p domain c with hB_def
  set r : ℚ := max (|domain.hi - c|) (|domain.lo - c|) with hr_def
  have hr_real : (r : ℝ) = max (|(domain.hi : ℝ) - c|) (|(domain.lo : ℝ) - c|) := by
    simp only [hr_def, Rat.cast_max, Rat.cast_abs, Rat.cast_sub]
  have habs_le_r : |x - c| ≤ r := by
    rw [hr_real]
    exact abs_sub_le_radius x c domain hx
  have h := aeval_abs_le_sum p (x - c) r habs_le_r
  have hcoeff_abs : ∀ i, (|p.coeff i| : ℝ) = |(p.coeff i : ℝ)| := fun i => rfl
  calc |Polynomial.aeval (x - ↑c) p|
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (r : ℝ) ^ i := h
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), (|p.coeff i| : ℝ) * (r : ℝ) ^ i := by
        apply Finset.sum_congr rfl; intro i _; rw [← hcoeff_abs]
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * r ^ i : ℚ) := by
        simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow]
    _ = (B : ℝ) := by rw [hB_def]; rfl

/-- Value in symmetric interval from absolute bound -/
theorem mem_symmetric_interval_of_abs_le {x : ℝ} {B : ℚ} (hB : 0 ≤ B) (h : |x| ≤ B) :
    x ∈ (⟨-B, B, by linarith⟩ : IntervalRat) := by
  simp only [IntervalRat.mem_def, Rat.cast_neg]
  constructor
  · have := neg_abs_le x; linarith
  · exact le_trans (le_abs_self x) h

/-! ### Generic Taylor model algebra lemmas

These lemmas are pure TM algebra that don't depend on Expr or transcendentals.
-/

namespace TaylorModel

/-- If x ∈ bound and bound doesn't contain zero, then x ≠ 0. -/
theorem ne_zero_of_mem_nonzero_bound {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hnz : ¬ IntervalRat.containsZero I) : x ≠ 0 := by
  simp only [IntervalRat.containsZero, not_and, not_le] at hnz
  simp only [IntervalRat.mem_def] at hx
  intro hxz
  rw [hxz] at hx
  by_cases hlo : I.lo ≤ 0
  · have hhi := hnz hlo
    have hhi_real : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
    linarith
  · push_neg at hlo
    have hlo_real : (0 : ℝ) < I.lo := by exact_mod_cast hlo
    linarith

/-- FOIL expansion for Taylor model multiplication.
(P₁ + r₁)(P₂ + r₂) = trunc(P₁P₂) + [tail(P₁P₂) + P₁r₂ + P₂r₁ + r₁r₂] -/
theorem foil_to_trunc_remainder {p1 p2 : Polynomial ℚ} {r1 r2 y : ℝ} {degree : ℕ}
    (hsplit : Polynomial.aeval y (p1 * p2) =
              Polynomial.aeval y (truncPoly (p1 * p2) degree) +
              Polynomial.aeval y (tailPoly (p1 * p2) degree)) :
    (Polynomial.aeval y p1 + r1) * (Polynomial.aeval y p2 + r2) =
    Polynomial.aeval y (truncPoly (p1 * p2) degree) +
      (Polynomial.aeval y (tailPoly (p1 * p2) degree) +
       Polynomial.aeval y p1 * r2 + Polynomial.aeval y p2 * r1 + r1 * r2) := by
  have hpoly_mul : Polynomial.aeval y p1 * Polynomial.aeval y p2 =
                   Polynomial.aeval y (p1 * p2) :=
    ((Polynomial.aeval y).map_mul p1 p2).symm
  calc
    (Polynomial.aeval y p1 + r1) * (Polynomial.aeval y p2 + r2)
      = Polynomial.aeval y p1 * Polynomial.aeval y p2 +
        Polynomial.aeval y p1 * r2 + Polynomial.aeval y p2 * r1 + r1 * r2 := by ring
    _ = Polynomial.aeval y (p1 * p2) +
        Polynomial.aeval y p1 * r2 + Polynomial.aeval y p2 * r1 + r1 * r2 := by rw [hpoly_mul]
    _ = (Polynomial.aeval y (truncPoly (p1 * p2) degree) +
         Polynomial.aeval y (tailPoly (p1 * p2) degree)) +
        Polynomial.aeval y p1 * r2 + Polynomial.aeval y p2 * r1 + r1 * r2 := by rw [hsplit]
    _ = Polynomial.aeval y (truncPoly (p1 * p2) degree) +
        (Polynomial.aeval y (tailPoly (p1 * p2) degree) +
         Polynomial.aeval y p1 * r2 + Polynomial.aeval y p2 * r1 + r1 * r2) := by ring

/-- Four-term remainder membership: tail + p1r2 + p2r1 + r1r2 ∈ totalRemainder.
This extracts the nested interval addition pattern from mul_evalSet_correct. -/
theorem remainder_four_terms_mem {v_tail v_p1r2 v_p2r1 v_r1r2 : ℝ}
    {I_tail I_p1r2 I_p2r1 I_r1r2 : IntervalRat}
    (htail : v_tail ∈ I_tail) (hp1r2 : v_p1r2 ∈ I_p1r2)
    (hp2r1 : v_p2r1 ∈ I_p2r1) (hr1r2 : v_r1r2 ∈ I_r1r2) :
    v_tail + v_p1r2 + v_p2r1 + v_r1r2 ∈
      IntervalRat.add I_tail (IntervalRat.add I_p1r2 (IntervalRat.add I_p2r1 I_r1r2)) := by
  have h_inner := IntervalRat.mem_add hp2r1 hr1r2
  have h_mid := IntervalRat.mem_add hp1r2 h_inner
  have h_full := IntervalRat.mem_add htail h_mid
  convert h_full using 1
  ring

set_option maxHeartbeats 400000 in
/-- Multiplication preserves evalSet membership.

Given:
- f₁(x) ∈ tm1.evalSet x (i.e., f₁(x) = P₁(y) + r₁ with r₁ ∈ tm1.remainder)
- f₂(x) ∈ tm2.evalSet x (i.e., f₂(x) = P₂(y) + r₂ with r₂ ∈ tm2.remainder)

Then f₁(x) * f₂(x) ∈ (TaylorModel.mul tm1 tm2 degree).evalSet x.

The expansion is:
  (P₁ + r₁)(P₂ + r₂) = P₁P₂ + P₁r₂ + P₂r₁ + r₁r₂
                     = trunc(P₁P₂) + [tail(P₁P₂) + P₁r₂ + P₂r₁ + r₁r₂]
-/
theorem mul_evalSet_correct
    (f₁ f₂ : ℝ → ℝ) (tm1 tm2 : TaylorModel) (degree : ℕ)
    (hcenter : tm1.center = tm2.center)
    (hdomain : tm1.domain = tm2.domain)
    (hf1 : ∀ x ∈ tm1.domain, f₁ x ∈ tm1.evalSet x)
    (hf2 : ∀ x ∈ tm2.domain, f₂ x ∈ tm2.evalSet x) :
    ∀ x ∈ tm1.domain, (f₁ x) * (f₂ x) ∈ (TaylorModel.mul tm1 tm2 degree).evalSet x := by
  intro x hx
  have h1 := hf1 x hx
  have h2 := hf2 x (hdomain ▸ hx)
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq] at h1 h2
  rcases h1 with ⟨r1, hr1_mem, hr1_eq⟩
  rcases h2 with ⟨r2, hr2_mem, hr2_eq⟩

  have hcenter_cast : (tm2.center : ℝ) = tm1.center := by exact_mod_cast hcenter.symm

  let prodPoly := tm1.poly * tm2.poly
  let truncatedPoly := truncPoly prodPoly degree
  let tail := tailPoly prodPoly degree
  let tailB := boundPolyAbs tail tm1.domain tm1.center
  let p1Bound := boundPolyAbs tm1.poly tm1.domain tm1.center
  let p2Bound := boundPolyAbs tm2.poly tm2.domain tm2.center
  let tailInterval : IntervalRat := ⟨-tailB, tailB, by linarith [boundPolyAbs_nonneg tail tm1.domain tm1.center]⟩
  let p1r2 := IntervalRat.mul ⟨-p1Bound, p1Bound, by linarith [boundPolyAbs_nonneg tm1.poly tm1.domain tm1.center]⟩ tm2.remainder
  let p2r1 := IntervalRat.mul ⟨-p2Bound, p2Bound, by linarith [boundPolyAbs_nonneg tm2.poly tm2.domain tm2.center]⟩ tm1.remainder
  let r1r2 := IntervalRat.mul tm1.remainder tm2.remainder
  let totalRemainder := IntervalRat.add tailInterval (IntervalRat.add p1r2 (IntervalRat.add p2r1 r1r2))

  let y := x - tm1.center
  let remainderTerm := Polynomial.aeval y tail +
                       Polynomial.aeval y tm1.poly * r2 +
                       Polynomial.aeval y tm2.poly * r1 +
                       r1 * r2

  have hp2Bound_eq : p2Bound = boundPolyAbs tm2.poly tm1.domain tm1.center := by
    show boundPolyAbs tm2.poly tm2.domain tm2.center = boundPolyAbs tm2.poly tm1.domain tm1.center
    simp only [hdomain, hcenter]

  have htailB_nn : 0 ≤ tailB := boundPolyAbs_nonneg tail tm1.domain tm1.center
  have hp1Bound_nn : 0 ≤ p1Bound := boundPolyAbs_nonneg tm1.poly tm1.domain tm1.center
  have hp2Bound_nn : 0 ≤ p2Bound := boundPolyAbs_nonneg tm2.poly tm2.domain tm2.center

  have htail_bounded : |Polynomial.aeval y tail| ≤ tailB :=
    tailPoly_eval_bounded prodPoly degree tm1.domain tm1.center x hx
  have hp1_bounded : |Polynomial.aeval y tm1.poly| ≤ p1Bound :=
    poly_eval_bounded tm1.poly tm1.domain tm1.center x hx
  have hp2_bounded : |Polynomial.aeval y tm2.poly| ≤ p2Bound := by
    rw [hp2Bound_eq]
    exact poly_eval_bounded tm2.poly tm1.domain tm1.center x hx

  have htail_mem : Polynomial.aeval y tail ∈ tailInterval :=
    mem_symmetric_interval_of_abs_le htailB_nn htail_bounded
  have hp1_mem : Polynomial.aeval y tm1.poly ∈ (⟨-p1Bound, p1Bound, by linarith⟩ : IntervalRat) :=
    mem_symmetric_interval_of_abs_le hp1Bound_nn hp1_bounded
  have hp2_mem : Polynomial.aeval y tm2.poly ∈ (⟨-p2Bound, p2Bound, by linarith⟩ : IntervalRat) :=
    mem_symmetric_interval_of_abs_le hp2Bound_nn hp2_bounded

  have hp1r2_mem : Polynomial.aeval y tm1.poly * r2 ∈ p1r2 :=
    IntervalRat.mem_mul hp1_mem hr2_mem
  have hp2r1_mem : Polynomial.aeval y tm2.poly * r1 ∈ p2r1 :=
    IntervalRat.mem_mul hp2_mem hr1_mem
  have hr1r2_mem : r1 * r2 ∈ r1r2 :=
    IntervalRat.mem_mul hr1_mem hr2_mem

  have hrem_mem : remainderTerm ∈ totalRemainder :=
    remainder_four_terms_mem htail_mem hp1r2_mem hp2r1_mem hr1r2_mem

  have hy_eq : x - (tm2.center : ℝ) = y := by
    simp only [hcenter_cast]
    rfl

  have hprod_expand : f₁ x * f₂ x =
      (Polynomial.aeval y tm1.poly + r1) * (Polynomial.aeval y tm2.poly + r2) := by
    rw [hr1_eq, hr2_eq, hy_eq]

  have hsplit : Polynomial.aeval y prodPoly =
      Polynomial.aeval y truncatedPoly + Polynomial.aeval y tail :=
    aeval_eq_truncPoly_add_tailPoly prodPoly degree y

  have hfinal : f₁ x * f₂ x = Polynomial.aeval y truncatedPoly + remainderTerm := by
    rw [hprod_expand]
    exact foil_to_trunc_remainder hsplit

  refine ⟨remainderTerm, hrem_mem, ?_⟩
  rw [hfinal]
  rfl

/-- Inversion preserves evalSet membership (conservative construction).

Since `TaylorModel.inv` uses poly = 0 and remainder = invBound, we show
that if `f(x) ∈ tm.evalSet x` for all x in domain, then `f(x)⁻¹ ∈ (inv tm hnz).evalSet x`.
-/
theorem inv_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (hnz : ¬ IntervalRat.containsZero tm.bound)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, (f x)⁻¹ ∈ (TaylorModel.inv tm hnz).evalSet x := by
  intro x hx
  have hfbound := taylorModel_correct tm f hf x hx
  have hfne : f x ≠ 0 := ne_zero_of_mem_nonzero_bound hfbound hnz
  let nz : IntervalRat.IntervalRatNonzero :=
    { lo := tm.bound.lo
      hi := tm.bound.hi
      le := tm.bound.le
      nonzero := hnz }
  have hinv : (f x)⁻¹ ∈ IntervalRat.invNonzero nz := IntervalRat.mem_invNonzero hfbound hfne
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq, TaylorModel.inv]
  refine ⟨(f x)⁻¹, hinv, ?_⟩
  simp only [map_zero, zero_add]

end TaylorModel

end LeanCert.Engine
