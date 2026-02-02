/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.GetD

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

/-! ### Bernstein proof infrastructure -/

/-- For the zero polynomial, all transformed coefficients are zero. -/
private theorem transformPolyCoeffs_zero (α β : ℚ) :
    transformPolyCoeffs 0 α β = [0] := by
  unfold transformPolyCoeffs
  simp only [Polynomial.natDegree_zero, Polynomial.coeff_zero, zero_mul,
    Finset.sum_const_zero]
  rfl

/-- For the zero polynomial, Bernstein bounds contain zero. -/
theorem boundPolyBernstein_zero_poly (domain : IntervalRat) (c : ℚ) :
    (boundPolyBernstein 0 domain c).lo ≤ 0 ∧ 0 ≤ (boundPolyBernstein 0 domain c).hi := by
  have hcoeffs : bernsteinCoeffsForDomain 0 domain.lo domain.hi c = [0] := by
    simp only [bernsteinCoeffsForDomain, transformPolyCoeffs_zero]
    -- Now need: monomialToBernstein [0] = [0]
    simp only [monomialToBernstein, List.length_cons, List.length_nil,
      Nat.add_one_sub_one, Nat.not_lt_zero, ite_false]
    simp only [binomialRat]
    norm_num
  simp only [boundPolyBernstein, hcoeffs]
  simp only [listMinMax, List.foldl_cons, List.foldl_nil, min_self, max_self]
  exact ⟨le_refl 0, le_refl 0⟩

/-! ### listMinMax bounds -/

/-- The foldl accumulator lo is monotonically decreasing. -/
private theorem listMinMax_foldl_lo_le_init (l : List ℚ) (p : ℚ × ℚ) :
    (l.foldl (fun (lo, hi) x => (min lo x, max hi x)) p).1 ≤ p.1 := by
  induction l generalizing p with
  | nil => exact le_refl _
  | cons a as ih =>
    simp only [List.foldl_cons]
    calc (as.foldl _ (min p.1 a, max p.2 a)).1 ≤ min p.1 a := ih _
      _ ≤ p.1 := min_le_left _ _

/-- The foldl accumulator hi is monotonically increasing. -/
private theorem init_le_listMinMax_foldl_hi (l : List ℚ) (p : ℚ × ℚ) :
    p.2 ≤ (l.foldl (fun (lo, hi) x => (min lo x, max hi x)) p).2 := by
  induction l generalizing p with
  | nil => exact le_refl _
  | cons a as ih =>
    simp only [List.foldl_cons]
    calc p.2 ≤ max p.2 a := le_max_left _ _
      _ ≤ (as.foldl _ (min p.1 a, max p.2 a)).2 := ih _

/-- Helper: foldl result lo ≤ every element of the list -/
private theorem listMinMax_foldl_lo_le_elem (l : List ℚ) (p : ℚ × ℚ) (x : ℚ) (hx : x ∈ l) :
    (l.foldl (fun (lo, hi) y => (min lo y, max hi y)) p).1 ≤ x := by
  induction l generalizing p with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with heq | hmem
    · rw [heq]
      exact le_trans (listMinMax_foldl_lo_le_init as _) (min_le_right p.1 a)
    · exact ih _ hmem

/-- Helper: every element of the list ≤ foldl result hi -/
private theorem listMinMax_foldl_elem_le_hi (l : List ℚ) (p : ℚ × ℚ) (x : ℚ) (hx : x ∈ l) :
    x ≤ (l.foldl (fun (lo, hi) y => (min lo y, max hi y)) p).2 := by
  induction l generalizing p with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with heq | hmem
    · rw [heq]
      exact le_trans (le_max_right p.2 a) (init_le_listMinMax_foldl_hi as _)
    · exact ih _ hmem

/-- Elements of a list lie between the listMinMax bounds -/
theorem listMinMax_bounds_elem (l : List ℚ) (d : ℚ) (x : ℚ) (hx : x ∈ l) :
    (listMinMax l d).1 ≤ x ∧ x ≤ (listMinMax l d).2 := by
  unfold listMinMax
  exact ⟨listMinMax_foldl_lo_le_elem l (d, d) x hx,
         listMinMax_foldl_elem_le_hi l (d, d) x hx⟩

/-- The default value lies between the listMinMax bounds -/
theorem listMinMax_bounds_default (l : List ℚ) (d : ℚ) :
    (listMinMax l d).1 ≤ d ∧ d ≤ (listMinMax l d).2 := by
  unfold listMinMax
  constructor
  · exact le_trans (listMinMax_foldl_lo_le_init l _) (le_refl d)
  · exact le_trans (le_refl d) (init_le_listMinMax_foldl_hi l _)

/-! ### Convex combination bounds -/

/-- A weighted sum with non-negative weights summing to 1 is bounded above by the max. -/
theorem weighted_sum_le_sup {n : ℕ} (a w : Fin (n + 1) → ℝ) (M : ℝ)
    (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : Finset.univ.sum w = 1)
    (ha_le : ∀ k, a k ≤ M) :
    Finset.univ.sum (fun k => a k * w k) ≤ M := by
  calc Finset.univ.sum (fun k => a k * w k)
      ≤ Finset.univ.sum (fun k => M * w k) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (ha_le k) (hw_nn k)
    _ = M * Finset.univ.sum w := by rw [← Finset.mul_sum]
    _ = M := by rw [hw_sum, mul_one]

/-- A weighted sum with non-negative weights summing to 1 is bounded below by the min. -/
theorem inf_le_weighted_sum {n : ℕ} (a w : Fin (n + 1) → ℝ) (m : ℝ)
    (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : Finset.univ.sum w = 1)
    (hm_le : ∀ k, m ≤ a k) :
    m ≤ Finset.univ.sum (fun k => a k * w k) := by
  calc m = m * 1 := (mul_one m).symm
    _ = m * Finset.univ.sum w := by rw [hw_sum]
    _ = Finset.univ.sum (fun k => m * w k) := by rw [Finset.mul_sum]
    _ ≤ Finset.univ.sum (fun k => a k * w k) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hm_le k) (hw_nn k)

/-! ### Combinatorial identity -/

/-- Key identity: C(k,j) * C(n,k) = C(n,j) * C(n-j, k-j) for j ≤ k ≤ n -/
theorem choose_mul_choose_eq {n k j : ℕ} (hj : j ≤ k) (hk : k ≤ n) :
    Nat.choose k j * Nat.choose n k = Nat.choose n j * Nat.choose (n - j) (k - j) := by
  have hjn : j ≤ n := le_trans hj hk
  have hkj : k - j ≤ n - j := Nat.sub_le_sub_right hk j
  have hnk : n - j - (k - j) = n - k := by omega
  have lhs1 := Nat.choose_mul_factorial_mul_factorial hj
  have lhs2 := Nat.choose_mul_factorial_mul_factorial hk
  have rhs1 := Nat.choose_mul_factorial_mul_factorial hjn
  have rhs2 := Nat.choose_mul_factorial_mul_factorial hkj
  rw [hnk] at rhs2
  -- Both sides * (j! * (k-j)! * k! * (n-k)!) = k! * n!
  have hfact_pos : 0 < Nat.factorial j * Nat.factorial (k - j) *
      Nat.factorial k * Nat.factorial (n - k) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hfact_pos
  -- LHS * factor = (choose k j * j! * (k-j)!) * (choose n k * k! * (n-k)!) = k! * n!
  have hlhs : Nat.choose k j * Nat.choose n k *
      (Nat.factorial j * Nat.factorial (k - j) * Nat.factorial k * Nat.factorial (n - k)) =
      Nat.factorial k * Nat.factorial n := by
    calc Nat.choose k j * Nat.choose n k *
        (Nat.factorial j * Nat.factorial (k - j) * Nat.factorial k * Nat.factorial (n - k))
        = (Nat.choose k j * Nat.factorial j * Nat.factorial (k - j)) *
          (Nat.choose n k * Nat.factorial k * Nat.factorial (n - k)) := by ring
      _ = Nat.factorial k * Nat.factorial n := by rw [lhs1, lhs2]
  -- RHS * factor = (choose (n-j) (k-j) * (k-j)! * (n-k)!) * (choose n j * j!) * k!
  --             = (n-j)! * (choose n j * j!) * k! = n! * k!
  have hrhs : Nat.choose n j * Nat.choose (n - j) (k - j) *
      (Nat.factorial j * Nat.factorial (k - j) * Nat.factorial k * Nat.factorial (n - k)) =
      Nat.factorial k * Nat.factorial n := by
    calc Nat.choose n j * Nat.choose (n - j) (k - j) *
        (Nat.factorial j * Nat.factorial (k - j) * Nat.factorial k * Nat.factorial (n - k))
        = (Nat.choose (n - j) (k - j) * Nat.factorial (k - j) * Nat.factorial (n - k)) *
          (Nat.choose n j * Nat.factorial j) * Nat.factorial k := by ring
      _ = Nat.factorial (n - j) * (Nat.choose n j * Nat.factorial j) * Nat.factorial k := by
          rw [rhs2]
      _ = (Nat.choose n j * Nat.factorial j * Nat.factorial (n - j)) * Nat.factorial k := by ring
      _ = Nat.factorial n * Nat.factorial k := by rw [rhs1]
      _ = Nat.factorial k * Nat.factorial n := by ring
  linarith

/-! ### Partition of unity for Bernstein basis -/

/-- Bernstein basis functions sum to 1 (follows from binomial theorem). -/
theorem bernstein_partition_of_unity (n : ℕ) (t : ℝ) :
    (Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : ℝ) * t ^ k * (1 - t) ^ (n - k)) = 1 := by
  have h := add_pow t (1 - t) n
  have h1 : t + (1 - t) = (1 : ℝ) := by ring
  rw [h1, one_pow] at h
  -- h : 1 = ∑ m ∈ range (n+1), t^m * (1-t)^(n-m) * ↑(n.choose m)
  conv_lhs =>
    arg 2; ext k
    rw [show (Nat.choose n k : ℝ) * t ^ k * (1 - t) ^ (n - k) =
        t ^ k * (1 - t) ^ (n - k) * (Nat.choose n k : ℝ) from by ring]
  linarith

/-- Bernstein basis functions are non-negative on [0, 1]. -/
theorem bernstein_nonneg (n k : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (Nat.choose n k : ℝ) * t ^ k * (1 - t) ^ (n - k) := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact_mod_cast Nat.zero_le (Nat.choose n k)
    · exact pow_nonneg ht0 k
  · exact pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (n - k)

/-! ### Bernstein representation identity

The key identity: for a polynomial Q(t) = Σⱼ qⱼ tʲ of degree n,
with Bernstein coefficients bₖ = Σⱼ≤k C(k,j)/C(n,j) · qⱼ, we have:
  Q(t) = Σₖ bₖ · C(n,k) · tᵏ · (1-t)^(n-k)

The proof uses: tʲ = Σₖ≥ⱼ C(n-j,k-j) · tᵏ · (1-t)^(n-k)
which follows from tʲ · (t + (1-t))^(n-j) = tʲ (binomial theorem).
-/

/-- The monomial tʲ expanded in Bernstein basis.
    tʲ · 1 = tʲ · (t + (1-t))^(n-j)
           = Σₘ C(n-j,m) · t^(m+j) · (1-t)^(n-j-m)
           = Σₖ≥ⱼ C(n-j,k-j) · tᵏ · (1-t)^(n-k)

    The proof follows from the binomial theorem: tʲ · (t + (1-t))^(n-j) = tʲ.
    Expanding the binomial and reindexing m ↦ k=m+j gives the result. -/
theorem monomial_bernstein_expansion (n j : ℕ) (hjn : j ≤ n) (t : ℝ) :
    t ^ j = (Finset.range (n + 1)).sum (fun k =>
      if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
      else 0) := by
  -- Step 1: t^j = t^j * (t + (1-t))^(n-j)
  have h1 : t + (1 - t) = (1 : ℝ) := by ring
  have hstart : t ^ j = t ^ j * (t + (1 - t)) ^ (n - j) := by
    rw [h1, one_pow, mul_one]
  rw [hstart]
  -- Step 2: expand (t + (1-t))^(n-j) via binomial theorem
  rw [add_pow t (1 - t) (n - j)]
  -- Goal: t^j * Σ_m C(n-j,m) * t^m * (1-t)^(n-j-m) = Σ_k if j≤k then ...
  rw [Finset.mul_sum]
  -- Step 3: reindex the sum. LHS sums over m ∈ range(n-j+1), RHS over k ∈ range(n+1)
  -- Let k = m + j, so m = k - j
  -- We split the RHS: terms with k < j are 0, terms with j ≤ k contribute
  -- First simplify: the RHS sum over k < j gives 0
  have hsplit : (Finset.range (n + 1)).sum (fun k =>
      if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
      else 0) =
    (Finset.range (n - j + 1)).sum (fun m =>
      (Nat.choose (n - j) m : ℝ) * t ^ (m + j) * (1 - t) ^ (n - j - m)) := by
    -- Reindex: k = m + j
    rw [show n + 1 = j + (n + 1 - j) from by omega]
    rw [Finset.sum_range_add]
    -- The first part (k < j) sums to 0
    have hfirst : (Finset.range j).sum (fun k =>
        if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      simp only [show ¬(j ≤ k) from by omega, ite_false]
    rw [hfirst, zero_add]
    -- Second part: ∑ m in range(n+1-j), f(m+j)
    -- f(m+j) = if j ≤ m+j then C(n-j, m+j-j) * t^(m+j) * (1-t)^(n-(m+j)) else 0
    --        = C(n-j, m) * t^(m+j) * (1-t)^(n-j-m)
    rw [show n + 1 - j = n - j + 1 from by omega]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_range] at hm
    have hjle : j ≤ j + m := Nat.le_add_right j m
    rw [if_pos hjle]
    have h1 : j + m - j = m := by omega
    have h2 : n - (j + m) = n - j - m := by omega
    rw [h1, h2]
    ring
  rw [hsplit]
  -- Now both sides sum over m ∈ range(n-j+1)
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  -- LHS: t^j * (t^m * (1-t)^(n-j-m) * C(n-j,m))
  -- RHS: C(n-j,m) * t^(m+j) * (1-t)^(n-j-m)
  rw [pow_add t m j]
  ring

/-! ### Main Bernstein enclosure theorem -/

/-- Bernstein bounds are always at least as tight as naive bounds (symmetric [-B, B]).
    This follows from the property that Bernstein coefficients bound the polynomial range. -/
theorem boundPolyBernstein_le_boundPolyAbs (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ) :
    -(boundPolyAbs p domain c) ≤ (boundPolyBernstein p domain c).lo ∧
    (boundPolyBernstein p domain c).hi ≤ boundPolyAbs p domain c := by
  -- UNUSED: secondary property showing Bernstein ⊆ naive [-B, B].
  -- Requires showing ∀ k, |bₖ| ≤ Σᵢ |aᵢ| rⁱ via double-sum triangle inequality:
  --   bₖ = Σⱼ Σᵢ C(k,j)/C(n,j) · aᵢ · C(i,j) · α^(i-j) · w^j
  -- Need: Σ_{j≤min(k,i)} C(k,j)·C(i,j)/C(n,j)·|α|^(i-j)·|w|^j ≤ r^i
  -- where r = max(|α|,|β|). Note: weights C(k,j)/C(n,j) do NOT sum to 1
  -- (for k=n they sum to n+1), so a simple convex combination argument fails.
  sorry

/- Key theorem: polynomial evaluation lies within Bernstein bounds.
    This is the fundamental theorem of Bernstein polynomials:
    For P(x) = Σₖ bₖ Bₖₙ(x), we have min(bₖ) ≤ P(x) ≤ max(bₖ) on [0,1].

    This follows because Bernstein basis functions are non-negative and sum to 1. -/
/-- Bridge lemma: evaluation of a polynomial equals a Finset sum of its coefficients times monomials. -/
private theorem poly_aeval_eq_sum (p : Polynomial ℚ) (x : ℝ) :
    Polynomial.aeval x p =
    (Finset.range (p.natDegree + 1)).sum (fun j => (p.coeff j : ℝ) * x ^ j) := by
  rw [Polynomial.aeval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [Algebra.smul_def]

/- Bridge lemma: the Bernstein representation holds for real polynomials.
    Q(t) = Σⱼ qⱼ tʲ = Σₖ bₖ B_{n,k}(t) where bₖ = Σⱼ≤k C(k,j)/C(n,j) qⱼ.

    This connects the mathematical expansion (via monomial_bernstein_expansion)
    to the concrete Bernstein coefficients. The proof requires showing that
    the double sum can be reindexed to match the Bernstein coefficient formula. -/
/-- Auxiliary: length of monomialToBernstein output -/
private theorem monomialToBernstein_length (qs : List ℚ) (hn : 0 < qs.length) :
    (monomialToBernstein qs).length = qs.length := by
  simp only [monomialToBernstein]
  have : ¬ (qs.length - 1 < 0) := by omega
  simp only [this, ite_false, List.length_ofFn]
  omega

/-- Auxiliary: getElem of monomialToBernstein output -/
private theorem monomialToBernstein_getElem (qs : List ℚ) (k : ℕ) (hk : k < qs.length)
    (hn : 0 < qs.length) :
    (monomialToBernstein qs)[k]'(by rw [monomialToBernstein_length qs hn]; exact hk) =
    (Finset.range (k + 1)).sum (fun j =>
      if hj : j < qs.length then
        if (Nat.choose (qs.length - 1) j) = 0 then 0
        else binomialRat k j / binomialRat (qs.length - 1) j * qs[j]
      else 0) := by
  simp only [monomialToBernstein]
  have : ¬ (qs.length - 1 < 0) := by omega
  simp only [this, ite_false]
  rw [List.getElem_ofFn]
  rfl

private theorem bernstein_representation (qs : List ℚ) (n : ℕ) (hn : qs.length = n + 1)
    (t : ℝ) (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    let bs := monomialToBernstein qs
    (Finset.range (n + 1)).sum (fun j => (qs.getD j 0 : ℝ) * t ^ j) =
    (Finset.range (n + 1)).sum (fun k =>
      (bs.getD k 0 : ℝ) *
      ((Nat.choose n k : ℝ) * t ^ k * (1 - t) ^ (n - k))) := by
  intro bs
  -- Step 1: expand t^j using monomial_bernstein_expansion
  have hexpand : ∀ j ∈ Finset.range (n + 1),
      (qs.getD j 0 : ℝ) * t ^ j =
      (qs.getD j 0 : ℝ) *
      (Finset.range (n + 1)).sum (fun k =>
        if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
        else 0) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    congr 1
    exact monomial_bernstein_expansion n j (by omega) t
  rw [Finset.sum_congr rfl hexpand]
  simp_rw [Finset.mul_sum]
  -- Step 2: exchange sums
  rw [Finset.sum_comm]
  -- After sum_comm: Σ_k Σ_j q_j * (if j ≤ k then C(n-j,k-j) * t^k * (1-t)^(n-k) else 0)
  -- Goal: show this = Σ_k b_k * (C(n,k) * t^k * (1-t)^(n-k))
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  -- Factor out t^k * (1-t)^(n-k) from the inner sum on LHS
  have factor_lhs : (Finset.range (n + 1)).sum (fun j =>
      (qs.getD j 0 : ℝ) *
      (if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
       else 0)) =
    ((Finset.range (k + 1)).sum (fun j =>
      (qs.getD j 0 : ℝ) * (Nat.choose (n - j) (k - j) : ℝ))) *
    (t ^ k * (1 - t) ^ (n - k)) := by
    conv_rhs => rw [Finset.sum_mul]
    rw [show n + 1 = (k + 1) + (n - k) from by omega]
    rw [Finset.sum_range_add]
    have hzero : (Finset.range (n - k)).sum (fun j =>
        (qs.getD (j + (k + 1)) 0 : ℝ) *
        (if j + (k + 1) ≤ k then (Nat.choose (n - (j + (k + 1))) (k - (j + (k + 1))) : ℝ) *
          t ^ k * (1 - t) ^ (n - k)
        else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      simp only [show ¬(j + (k + 1) ≤ k) from by omega, ite_false, mul_zero]
    have hzero2 : ∀ j ∈ Finset.range (n - k),
        (qs.getD (k + 1 + j) 0 : ℝ) *
        (if k + 1 + j ≤ k then (Nat.choose (n - (k + 1 + j)) (k - (k + 1 + j)) : ℝ) *
          t ^ k * (1 - t) ^ (n - k)
        else 0) = 0 := by
      intro j _; simp only [show ¬(k + 1 + j ≤ k) from by omega, ite_false, mul_zero]
    rw [Finset.sum_eq_zero hzero2, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [if_pos (show j ≤ k from by omega)]
    ring
  rw [factor_lhs]
  -- Need: (Σ_{j≤k} q_j * C(n-j,k-j)) * (t^k * (1-t)^(n-k)) = b_k * (C(n,k) * t^k * (1-t)^(n-k))
  -- Suffices to show: Σ_{j≤k} q_j * C(n-j,k-j) = b_k * C(n,k)
  -- This is a combinatorial identity relating monomial and Bernstein coefficients.
  have hbs_len : bs.length = qs.length := monomialToBernstein_length qs (by omega)
  have hk_lt : k < bs.length := by rw [hbs_len]; omega
  suffices h : (∑ j ∈ Finset.range (k + 1), (qs.getD j 0 : ℝ) * (Nat.choose (n - j) (k - j) : ℝ)) =
    (bs.getD k 0 : ℝ) * (Nat.choose n k : ℝ) by
    calc (∑ j ∈ Finset.range (k + 1), (qs.getD j 0 : ℝ) * ↑((n - j).choose (k - j))) *
          (t ^ k * (1 - t) ^ (n - k))
        = ((bs.getD k 0 : ℝ) * ↑(n.choose k)) * (t ^ k * (1 - t) ^ (n - k)) := by rw [h]
      _ = (bs.getD k 0 : ℝ) * (↑(n.choose k) * t ^ k * (1 - t) ^ (n - k)) := by ring
  rw [List.getD_eq_getElem bs 0 hk_lt]
  rw [monomialToBernstein_getElem qs k (by omega) (by omega)]
  push_cast [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hj_lt : j < qs.length := by omega
  rw [List.getD_eq_getElem qs 0 hj_lt]
  simp only [dite_true, hn, show n + 1 - 1 = n from by omega,
    show j < n + 1 from by omega]
  by_cases hcnj : Nat.choose n j = 0
  · exfalso
    have := Nat.choose_eq_zero_iff.mp hcnj
    omega
  · simp only [hcnj, ite_false, binomialRat]
    have hident := choose_mul_choose_eq (show j ≤ k from by omega) (show k ≤ n from by omega)
    have hcnj_ne : (Nat.choose n j : ℚ) ≠ 0 := by exact_mod_cast hcnj
    have hid : (Nat.choose k j : ℚ) * (Nat.choose n k : ℚ) =
           (Nat.choose n j : ℚ) * (Nat.choose (n - j) (k - j) : ℚ) := by
      exact_mod_cast hident
    -- Goal is in ℝ: ↑qs[j] * ↑C(n-j,k-j) = ↑(C(k,j)/C(n,j) * qs[j]) * ↑C(n,k)
    -- where outer ↑ is ℚ→ℝ, inner ↑(C) is ℕ→ℚ
    -- Goal is in ℝ: ↑qs[j] * ↑C(n-j,k-j) = ↑(C(k,j)/C(n,j) * qs[j]) * ↑C(n,k)
    -- Prove the equality in ℚ first
    have hq : qs[j] * (Nat.choose (n - j) (k - j) : ℚ) =
        ((Nat.choose k j : ℚ) / (Nat.choose n j : ℚ) * qs[j]) * (Nat.choose n k : ℚ) := by
      -- Clear fractions: multiply both sides by C(n,j)
      have lhs_eq : qs[j] * (Nat.choose (n - j) (k - j) : ℚ) * (Nat.choose n j : ℚ) =
          qs[j] * ((Nat.choose n j : ℚ) * (Nat.choose (n - j) (k - j) : ℚ)) := by ring
      have rhs_eq : ((Nat.choose k j : ℚ) / (Nat.choose n j : ℚ) * qs[j]) * (Nat.choose n k : ℚ) *
          (Nat.choose n j : ℚ) =
          qs[j] * ((Nat.choose k j : ℚ) * (Nat.choose n k : ℚ)) := by
        field_simp
      have hmul : qs[j] * ((Nat.choose n j : ℚ) * (Nat.choose (n - j) (k - j) : ℚ)) =
          qs[j] * ((Nat.choose k j : ℚ) * (Nat.choose n k : ℚ)) := by
        congr 1; linarith
      exact mul_right_cancel₀ hcnj_ne (by linarith [lhs_eq, rhs_eq, hmul])
    exact_mod_cast hq

/- Bridge lemma: transformPolyCoeffs correctly represents the polynomial on [0,1].
    If Q = transformPolyCoeffs P α β, then P(α + t*(β-α)) = Σⱼ qⱼ tʲ for t ∈ [0,1]. -/
/-- Length of transformPolyCoeffs output -/
private theorem transformPolyCoeffs_length (p : Polynomial ℚ) (α β : ℚ) :
    (transformPolyCoeffs p α β).length = p.natDegree + 1 := by
  simp [transformPolyCoeffs, List.length_ofFn]

/-- getElem of transformPolyCoeffs output -/
private theorem transformPolyCoeffs_getElem (p : Polynomial ℚ) (α β : ℚ) (j : ℕ)
    (hj : j < p.natDegree + 1) :
    (transformPolyCoeffs p α β)[j]'(by rw [transformPolyCoeffs_length]; exact hj) =
    (Finset.range (p.natDegree + 1 - j)).sum (fun k =>
      let i := j + k
      p.coeff i * binomialRat i j * α ^ (i - j) * (β - α) ^ j) := by
  simp only [transformPolyCoeffs]
  rw [List.getElem_ofFn]

private theorem transformPolyCoeffs_correct (p : Polynomial ℚ) (α β : ℚ) (t : ℝ) :
    let qs := transformPolyCoeffs p α β
    Polynomial.aeval ((α : ℝ) + t * ((β : ℝ) - (α : ℝ))) p =
    (Finset.range qs.length).sum (fun j => (qs.getD j 0 : ℝ) * t ^ j) := by
  intro qs
  let n := p.natDegree
  let w := (β : ℝ) - (α : ℝ)
  -- LHS = Σ_i a_i * (α + tw)^i = Σ_i a_i * (tw + α)^i
  rw [poly_aeval_eq_sum]
  -- Use add_pow with tw as first arg so j-th term has (tw)^j
  -- Step 1: expand (α + tw)^i via add_pow and pad inner sums
  have hexpand : ∀ i ∈ Finset.range (n + 1),
      (p.coeff i : ℝ) * ((α : ℝ) + t * ((β : ℝ) - (α : ℝ))) ^ i =
      (Finset.range (n + 1)).sum (fun j =>
        (p.coeff i : ℝ) * ((t * w) ^ j * (α : ℝ) ^ (i - j) * (Nat.choose i j : ℝ))) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [show (α : ℝ) + t * ((β : ℝ) - (α : ℝ)) = t * ((β : ℝ) - (α : ℝ)) + (α : ℝ) from by ring]
    rw [add_pow (t * ((β : ℝ) - (α : ℝ))) (α : ℝ) i]
    rw [Finset.mul_sum]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj1 hj2
    simp only [Finset.mem_range] at hj1 hj2
    push_neg at hj2
    have : Nat.choose i j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]
  rw [Finset.sum_congr rfl hexpand]
  -- Now both sums over range(n+1), can exchange
  rw [Finset.sum_comm]
  -- Outer index is now j (power of tw), inner is i
  -- Σ_j Σ_i a_i * (tw)^j * α^(i-j) * C(i,j)
  -- = Σ_j (Σ_i a_i * C(i,j) * α^(i-j)) * (tw)^j
  -- = Σ_j (Σ_i a_i * C(i,j) * α^(i-j)) * w^j * t^j
  -- = Σ_j q_j * t^j  where q_j = (Σ_{i≥j} a_i * C(i,j) * α^(i-j) * w^j)
  rw [transformPolyCoeffs_length]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  -- Show inner sum matches q_j * t^j
  -- Convert getD to getElem
  have hqs_len : qs.length = n + 1 := transformPolyCoeffs_length p α β
  have hj_lt : j < qs.length := by omega
  rw [List.getD_eq_getElem qs 0 hj_lt, transformPolyCoeffs_getElem p α β j (by omega)]
  -- RHS: (Σ_{k=0}^{n-j} a_{j+k} * C(j+k, j) * α^k * w^j) * t^j
  -- LHS: Σ_{i=0}^{n} a_i * ((tw)^j * α^(i-j) * C(i,j))
  -- Reindex LHS: set k = i - j, so i = j + k, k ranges 0..n-j
  -- Terms with i < j: C(i,j) = 0
  -- After reindex: Σ_{k=0}^{n-j} a_{j+k} * (tw)^j * α^k * C(j+k, j)
  --             = (Σ_{k=0}^{n-j} a_{j+k} * C(j+k, j) * α^k) * (tw)^j
  --             = (Σ_{k=0}^{n-j} a_{j+k} * C(j+k, j) * α^k) * w^j * t^j
  -- This matches RHS!

  -- Split sum: terms with i < j give 0 (C(i,j) = 0)
  rw [show n + 1 = j + (n + 1 - j) from by omega]
  rw [Finset.sum_range_add]
  have hzero : (Finset.range j).sum (fun i =>
      (p.coeff i : ℝ) * ((t * w) ^ j * (α : ℝ) ^ (i - j) * (Nat.choose i j : ℝ))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_range] at hi
    have : Nat.choose i j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]
  rw [hzero, zero_add]
  -- Now: Σ_{k=0}^{n-j} a_{j+k} * (tw)^j * α^((j+k)-j) * C(j+k, j) = qⱼ * t^j
  -- Simplify (j+k) - j = k
  -- Each term: a_{j+k} * (tw)^j * α^k * C(j+k,j) = cast(a_{j+k} * C(j+k,j) * α^k * w^j) * t^j
  push_cast [Finset.sum_mul]
  rw [show j + (n + 1 - j) - j = n + 1 - j from by omega]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  simp only [show (j + k) - j = k from by omega, binomialRat, mul_pow,
    show w = (β : ℝ) - (α : ℝ) from rfl]
  push_cast
  ring

/-- The core Bernstein enclosure: for coefficients of length n+1 on [0,1],
    Σⱼ qⱼ tʲ lies in the Bernstein bounds interval. -/
private theorem bernstein_enclosure_01 (qs : List ℚ) (n : ℕ) (hn : qs.length = n + 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let bs := monomialToBernstein qs
    let bounds := listMinMax bs (bs[0]'(by rw [monomialToBernstein_length qs (by omega)]; omega))
    (bounds.1 : ℝ) ≤
    (Finset.range (n + 1)).sum (fun j => (qs.getD j 0 : ℝ) * t ^ j) ∧
    (Finset.range (n + 1)).sum (fun j => (qs.getD j 0 : ℝ) * t ^ j) ≤
    (bounds.2 : ℝ) := by
  -- Rewrite using bernstein_representation
  rw [bernstein_representation qs n hn t ht0 ht1]
  -- Now the sum is Σ_k b_k * B_{n,k}(t) which is a convex combination
  -- First convert getD to getElem for bs terms
  have hbs_len := monomialToBernstein_length qs (by omega)
  -- Convert from Finset.range to Finset.univ (Fin) for weighted_sum lemmas
  -- First, rewrite the sum using Fin.sum_univ_eq_sum_range
  have hbs := monomialToBernstein qs
  set bs := monomialToBernstein qs with hbs_def
  constructor
  · -- Lower bound
    -- Direct proof: bounds.1 ≤ each summand's coefficient, weights ≥ 0, sum weights = 1
    -- Transform the range sum to a Fin-based sum
    rw [← Fin.sum_univ_eq_sum_range]
    apply inf_le_weighted_sum
    · intro ⟨k, hk⟩
      exact bernstein_nonneg n k t ht0 ht1
    · have := bernstein_partition_of_unity n t
      rwa [← Fin.sum_univ_eq_sum_range] at this
    · intro ⟨k, hk⟩
      have hk_lt : k < bs.length := by rw [hbs_def, hbs_len]; omega
      have hgetD : bs.getD k 0 = bs[k]'hk_lt := List.getD_eq_getElem bs 0 hk_lt
      rw [hgetD]
      exact_mod_cast (listMinMax_bounds_elem bs
        (bs[0]'(by rw [hbs_def, hbs_len]; omega))
        (bs[k]'hk_lt)
        (List.getElem_mem hk_lt)).1
  · -- Upper bound
    rw [← Fin.sum_univ_eq_sum_range]
    apply weighted_sum_le_sup
    · intro ⟨k, hk⟩
      exact bernstein_nonneg n k t ht0 ht1
    · have := bernstein_partition_of_unity n t
      rwa [← Fin.sum_univ_eq_sum_range] at this
    · intro ⟨k, hk⟩
      have hk_lt : k < bs.length := by rw [hbs_def, hbs_len]; omega
      have hgetD : bs.getD k 0 = bs[k]'hk_lt := List.getD_eq_getElem bs 0 hk_lt
      rw [hgetD]
      exact_mod_cast (listMinMax_bounds_elem bs
        (bs[0]'(by rw [hbs_def, hbs_len]; omega))
        (bs[k]'hk_lt)
        (List.getElem_mem hk_lt)).2

/-- Helper: bernsteinCoeffsForDomain is always nonempty -/
private theorem bernsteinCoeffsForDomain_ne_nil (p : Polynomial ℚ) (lo hi c : ℚ) :
    bernsteinCoeffsForDomain p lo hi c ≠ [] := by
  simp only [bernsteinCoeffsForDomain]
  have htlen : (transformPolyCoeffs p (lo - c) (hi - c)).length = p.natDegree + 1 :=
    transformPolyCoeffs_length p (lo - c) (hi - c)
  have hpos : 0 < (transformPolyCoeffs p (lo - c) (hi - c)).length := by omega
  have hlen : (monomialToBernstein (transformPolyCoeffs p (lo - c) (hi - c))).length =
    (transformPolyCoeffs p (lo - c) (hi - c)).length :=
    monomialToBernstein_length _ hpos
  intro h
  rw [h] at hlen
  simp at hlen
  omega

/-- Helper: bernsteinCoeffsForDomain has the expected length -/
private theorem bernsteinCoeffsForDomain_length (p : Polynomial ℚ) (lo hi c : ℚ) :
    (bernsteinCoeffsForDomain p lo hi c).length = p.natDegree + 1 := by
  simp only [bernsteinCoeffsForDomain]
  rw [monomialToBernstein_length _ (by rw [transformPolyCoeffs_length]; omega)]
  exact transformPolyCoeffs_length p (lo - c) (hi - c)

theorem poly_eval_mem_boundPolyBernstein (p : Polynomial ℚ) (domain : IntervalRat) (c : ℚ)
    (x : ℝ) (hx : x ∈ domain) :
    Polynomial.aeval (x - c) p ∈ boundPolyBernstein p domain c := by
  simp only [IntervalRat.mem_def] at hx
  -- Unfold boundPolyBernstein and handle the match
  unfold boundPolyBernstein
  set coeffs := bernsteinCoeffsForDomain p domain.lo domain.hi c with hcoeffs_def
  -- coeffs is nonempty
  have hne := bernsteinCoeffsForDomain_ne_nil p domain.lo domain.hi c
  obtain ⟨c0, cs, hcoeffs_eq⟩ : ∃ c0 cs, coeffs = c0 :: cs := by
    match h : coeffs with
    | [] => exact absurd h hne
    | c0 :: cs => exact ⟨c0, cs, rfl⟩
  simp only [hcoeffs_eq]
  simp only [IntervalRat.mem_def]
  -- Need: (listMinMax (c0::cs) c0).1 ≤ aeval (x-c) p ∧ aeval (x-c) p ≤ (listMinMax (c0::cs) c0).2
  -- The key connection: coeffs = monomialToBernstein (transformPolyCoeffs p α β)
  -- and bernstein_enclosure_01 gives us bounds on Σ qⱼ tʲ
  -- transformPolyCoeffs_correct gives us P(x-c) = Σ qⱼ tʲ
  -- So we need to connect these.
  set α := domain.lo - c
  set β := domain.hi - c
  set qs := transformPolyCoeffs p α β
  -- coeffs = monomialToBernstein qs
  have hcoeffs_mb : coeffs = monomialToBernstein qs := by
    simp only [hcoeffs_def, bernsteinCoeffsForDomain]; rfl
  have hqs_len : qs.length = p.natDegree + 1 := transformPolyCoeffs_length p α β
  -- Choose t ∈ [0,1] such that x - c = α + t*(β - α) = (lo-c) + t*(hi-lo)
  -- If hi = lo, then x = lo = hi, so x - c = lo - c, and t can be anything (use 0)
  -- If hi > lo, t = (x - lo) / (hi - lo)
  by_cases hdom : domain.lo = domain.hi
  · -- Degenerate case: lo = hi, so x = lo, x - c = lo - c = α
    have hxeq : x = ↑domain.lo := by
      have h1 := hx.1; have h2 := hx.2
      have : (domain.lo : ℝ) = (domain.hi : ℝ) := by exact_mod_cast hdom
      linarith
    -- Use t = 0: P(α) = Σ qⱼ 0^j, and α = x - c
    -- Bernstein enclosure bounds the sum, so bounds hold.
    have htrans := transformPolyCoeffs_correct p α β 0
    have halpha : (α : ℝ) = x - (c : ℝ) := by
      simp only [α, hxeq]; push_cast; rfl
    have henc := bernstein_enclosure_01 qs p.natDegree hqs_len 0 le_rfl zero_le_one
    rw [hcoeffs_mb] at hcoeffs_eq
    simp only [hcoeffs_eq, List.getElem_cons_zero] at henc
    simp only [zero_mul, add_zero] at htrans
    rw [halpha] at htrans
    rw [htrans]
    rw [show (transformPolyCoeffs p α β).length = p.natDegree + 1 from
      transformPolyCoeffs_length p α β]
    exact henc
  · -- Non-degenerate: hi > lo (since lo ≤ hi and lo ≠ hi)
    have hlt : domain.lo < domain.hi := lt_of_le_of_ne domain.le (fun h => hdom h)
    set t := (x - ↑domain.lo) / (↑domain.hi - ↑domain.lo)
    have ht0 : (0 : ℝ) ≤ t := by
      apply div_nonneg; linarith [hx.1]; linarith [show (domain.lo : ℝ) < domain.hi from by exact_mod_cast hlt]
    have ht1 : t ≤ 1 := by
      apply div_le_one_of_le₀; linarith [hx.2]
      linarith [show (domain.lo : ℝ) < domain.hi from by exact_mod_cast hlt]
    -- x - c = α + t * (β - α)
    have hxt : (x : ℝ) - (c : ℝ) = (α : ℝ) + t * ((β : ℝ) - (α : ℝ)) := by
      simp only [α, β, t]
      push_cast
      have hne : (domain.hi : ℝ) - domain.lo ≠ 0 := by
        linarith [show (domain.lo : ℝ) < domain.hi from by exact_mod_cast hlt]
      field_simp
      ring
    -- Apply transformPolyCoeffs_correct
    have htrans := transformPolyCoeffs_correct p α β t
    rw [← hxt] at htrans
    -- Apply bernstein_enclosure_01
    have henc := bernstein_enclosure_01 qs p.natDegree hqs_len t ht0 ht1
    -- henc gives bounds on the sum in terms of listMinMax of monomialToBernstein qs
    -- which is listMinMax of coeffs (by hcoeffs_mb)
    -- We need to connect listMinMax of (monomialToBernstein qs) to listMinMax of (c0 :: cs)
    rw [htrans]
    rw [hcoeffs_mb] at hcoeffs_eq
    -- hcoeffs_eq : monomialToBernstein qs = c0 :: cs
    simp only [hcoeffs_eq, List.getElem_cons_zero] at henc
    have hqs_eq : qs = transformPolyCoeffs p α β := rfl
    simp only [← hqs_eq, hqs_len]
    exact_mod_cast henc

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
