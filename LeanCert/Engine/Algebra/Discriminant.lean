/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Real-root counts from low-degree discriminants

This file supplies the mathematical layer behind executable discriminant
certificates.  Cubics are reduced at one real root to a quadratic by synthetic
division.  The identity `Δ(P) = Δ(Q) * P'(r)^2` then transfers the sign of the
cubic discriminant to the quadratic discriminant.
-/

namespace LeanCert.Engine.Algebra

/-- The real zero set of `a*x^2 + b*x + c`. -/
def quadraticZeroSet (a b c : ℝ) : Set ℝ :=
  {x | a * (x * x) + b * x + c = 0}

theorem quadraticZeroSet_ncard_eq_zero_of_discrim_neg {a b c : ℝ}
    (hΔ : discrim a b c < 0) : (quadraticZeroSet a b c).ncard = 0 := by
  have hempty : quadraticZeroSet a b c = ∅ := by
    ext x
    simp only [quadraticZeroSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    apply quadratic_ne_zero_of_discrim_ne_sq
    intro s hs
    nlinarith [sq_nonneg s]
  simp [hempty]

theorem quadraticZeroSet_ncard_eq_one_of_discrim_eq_zero {a b c : ℝ}
    (ha : a ≠ 0) (hΔ : discrim a b c = 0) :
    (quadraticZeroSet a b c).ncard = 1 := by
  have hset : quadraticZeroSet a b c = {-b / (2 * a)} := by
    ext x
    simp only [quadraticZeroSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact quadratic_eq_zero_iff_of_discrim_eq_zero ha hΔ x
  simp [hset]

theorem quadraticZeroSet_ncard_eq_two_of_discrim_pos {a b c : ℝ}
    (ha : a ≠ 0) (hΔ : 0 < discrim a b c) :
    (quadraticZeroSet a b c).ncard = 2 := by
  let s := Real.sqrt (discrim a b c)
  let x₁ := (-b + s) / (2 * a)
  let x₂ := (-b - s) / (2 * a)
  have hs0 : 0 ≤ discrim a b c := hΔ.le
  have hs : discrim a b c = s * s := by
    dsimp [s]
    nlinarith [Real.sq_sqrt hs0]
  have hset : quadraticZeroSet a b c = {x₁, x₂} := by
    ext x
    simp only [quadraticZeroSet, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact quadratic_eq_zero_iff ha hs x
  have hsne : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hΔ)
  have hxne : x₁ ≠ x₂ := by
    intro h
    have h2a : (2 : ℝ) * a ≠ 0 := mul_ne_zero (by norm_num) ha
    apply hsne
    have hnum := congrArg (fun z : ℝ => z * (2 * a)) h
    simp [x₁, x₂, h2a] at hnum
    linarith
  rw [hset, Set.ncard_pair hxne]

theorem quadraticZeroSet_finite (a b c : ℝ) (ha : a ≠ 0) :
    (quadraticZeroSet a b c).Finite := by
  let p : Polynomial ℝ :=
    Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c
  have hp : p ≠ 0 := by
    intro hp
    have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff 2) hp
    simp [p, ha] at hcoeff
  have hfinite : {x : ℝ | p.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hp
  simpa [quadraticZeroSet, p, Polynomial.IsRoot, pow_two] using hfinite

/-- The real zero set of a cubic. -/
def cubicZeroSet (P : Cubic ℝ) : Set ℝ :=
  {x | P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0}

private def quotientB (P : Cubic ℝ) (r : ℝ) : ℝ := P.b + P.a * r
private def quotientC (P : Cubic ℝ) (r : ℝ) : ℝ :=
  P.c + P.b * r + P.a * r ^ 2

private def cubicDerivativeAt (P : Cubic ℝ) (r : ℝ) : ℝ :=
  3 * P.a * r ^ 2 + 2 * P.b * r + P.c

private theorem cubic_factor_at_root (P : Cubic ℝ) {r : ℝ}
    (hr : r ∈ cubicZeroSet P) (x : ℝ) :
    P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d =
      (x - r) * (P.a * (x * x) + quotientB P r * x + quotientC P r) := by
  simp only [cubicZeroSet, Set.mem_setOf_eq] at hr
  dsimp [quotientB, quotientC]
  linear_combination hr

private theorem cubic_discr_factor_at_root (P : Cubic ℝ) {r : ℝ}
    (hr : r ∈ cubicZeroSet P) :
    P.discr = discrim P.a (quotientB P r) (quotientC P r) *
      cubicDerivativeAt P r ^ 2 := by
  simp only [cubicZeroSet, Set.mem_setOf_eq] at hr
  have hd : P.d = -(P.a * r ^ 3 + P.b * r ^ 2 + P.c * r) := by
    linarith
  rw [Cubic.discr]
  rw [hd]
  dsimp [discrim, quotientB, quotientC, cubicDerivativeAt]
  ring

private theorem exists_cubic_root (P : Cubic ℝ) (ha : P.a ≠ 0) :
    ∃ r, r ∈ cubicZeroSet P := by
  let p := P.toPoly
  have hpdeg : 0 < p.degree := by simp [p, Cubic.degree_of_a_ne_zero ha]
  have hplead : p.leadingCoeff = P.a := Cubic.leadingCoeff_of_a_ne_zero ha
  have hcont : Continuous p.eval := p.continuous
  have hroot : (0 : ℝ) ∈ Set.range p.eval := by
    rcases lt_or_gt_of_ne ha with haNeg | haPos
    · have htop : Filter.Tendsto p.eval Filter.atTop Filter.atBot :=
        p.tendsto_atBot_of_leadingCoeff_nonpos hpdeg (hplead.trans_le haNeg.le)
      let q := p.comp (-Polynomial.X)
      have hqdeg : 0 < q.degree := by simp [q, p, Cubic.degree_of_a_ne_zero ha]
      have hqlead : 0 ≤ q.leadingCoeff := by
        norm_num [q, p, Cubic.natDegree_of_a_ne_zero ha, hplead]
        exact haNeg.le
      have hqtop : Filter.Tendsto q.eval Filter.atTop Filter.atTop :=
        q.tendsto_atTop_of_leadingCoeff_nonneg hqdeg hqlead
      apply mem_range_of_exists_le_of_exists_ge hcont
      · exact (htop.eventually (Filter.eventually_le_atBot 0)).exists
      · obtain ⟨x, hx⟩ := (hqtop.eventually (Filter.eventually_ge_atTop 0)).exists
        refine ⟨-x, ?_⟩
        simpa [q] using hx
    · have htop : Filter.Tendsto p.eval Filter.atTop Filter.atTop :=
        p.tendsto_atTop_of_leadingCoeff_nonneg hpdeg (hplead.trans_ge haPos.le)
      let q := p.comp (-Polynomial.X)
      have hqdeg : 0 < q.degree := by simp [q, p, Cubic.degree_of_a_ne_zero ha]
      have hqlead : q.leadingCoeff ≤ 0 := by
        norm_num [q, p, Cubic.natDegree_of_a_ne_zero ha, hplead]
        exact haPos.le
      have hqtop : Filter.Tendsto q.eval Filter.atTop Filter.atBot :=
        q.tendsto_atBot_of_leadingCoeff_nonpos hqdeg hqlead
      apply mem_range_of_exists_le_of_exists_ge hcont
      · obtain ⟨x, hx⟩ := (hqtop.eventually (Filter.eventually_le_atBot 0)).exists
        refine ⟨-x, ?_⟩
        simpa [q] using hx
      · exact (htop.eventually (Filter.eventually_ge_atTop 0)).exists
  obtain ⟨r, hr⟩ := hroot
  refine ⟨r, ?_⟩
  simpa [p, cubicZeroSet, Cubic.toPoly] using hr

private theorem cubicZeroSet_eq_insert_quotientZeroSet (P : Cubic ℝ) {r : ℝ}
    (hr : r ∈ cubicZeroSet P) :
    cubicZeroSet P = insert r (quadraticZeroSet P.a (quotientB P r) (quotientC P r)) := by
  ext x
  rw [Set.mem_insert_iff]
  simp only [cubicZeroSet, quadraticZeroSet, Set.mem_setOf_eq]
  rw [cubic_factor_at_root P hr]
  constructor
  · intro hx
    rcases mul_eq_zero.mp hx with hx | hx
    · exact .inl (sub_eq_zero.mp hx)
    · exact .inr hx
  · rintro (rfl | hx)
    · simp
    · exact mul_eq_zero_of_right _ hx

theorem cubicZeroSet_ncard_eq_one_of_discr_neg (P : Cubic ℝ)
    (ha : P.a ≠ 0) (hΔ : P.discr < 0) : (cubicZeroSet P).ncard = 1 := by
  obtain ⟨r, hr⟩ := exists_cubic_root P ha
  have hfactor := cubic_discr_factor_at_root P hr
  have hderiv : cubicDerivativeAt P r ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num), mul_zero] at hfactor
    linarith
  have hqΔ : discrim P.a (quotientB P r) (quotientC P r) < 0 := by
    have hsquare : 0 < cubicDerivativeAt P r ^ 2 := sq_pos_of_ne_zero hderiv
    nlinarith
  rw [cubicZeroSet_eq_insert_quotientZeroSet P hr]
  have hempty : quadraticZeroSet P.a (quotientB P r) (quotientC P r) = ∅ := by
    ext x
    simp only [quadraticZeroSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    apply quadratic_ne_zero_of_discrim_ne_sq
    intro s hs
    nlinarith [sq_nonneg s]
  simp [hempty]

theorem cubicZeroSet_ncard_eq_three_of_discr_pos (P : Cubic ℝ)
    (ha : P.a ≠ 0) (hΔ : 0 < P.discr) : (cubicZeroSet P).ncard = 3 := by
  obtain ⟨r, hr⟩ := exists_cubic_root P ha
  have hfactor := cubic_discr_factor_at_root P hr
  have hderiv : cubicDerivativeAt P r ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num), mul_zero] at hfactor
    linarith
  have hsquare : 0 < cubicDerivativeAt P r ^ 2 := sq_pos_of_ne_zero hderiv
  have hqΔ : 0 < discrim P.a (quotientB P r) (quotientC P r) := by nlinarith
  let Q := quadraticZeroSet P.a (quotientB P r) (quotientC P r)
  have hQcard : Q.ncard = 2 := quadraticZeroSet_ncard_eq_two_of_discrim_pos ha hqΔ
  have hrQ : r ∉ Q := by
    intro hrq
    have hqzero : P.a * (r * r) + quotientB P r * r + quotientC P r = 0 := hrq
    apply hderiv
    dsimp [quotientB, quotientC, cubicDerivativeAt] at hqzero ⊢
    nlinarith
  rw [cubicZeroSet_eq_insert_quotientZeroSet P hr]
  rw [Set.ncard_insert_of_notMem hrQ (quadraticZeroSet_finite _ _ _ ha)]
  omega

/-! ### Quantitative separation from a discriminant lower bound -/

/-- A scale-aware root-separation theorem. If `x`, `y`, and `z` are all the
roots of a real cubic, `d` is a lower bound for `|discr|`, `A` bounds the
leading coefficient, and `M` bounds the two other gaps, then any `eps` whose
corresponding discriminant product is below `d` is a strict lower bound for
`|x-y|`.

The bounds `A` and `M` are essential: the discriminant alone has no
scale-independent quantitative separation consequence. -/
theorem cubic_root_gap_gt_of_discr_bound (P : Cubic ℝ) {x y z d A M eps : ℝ}
    (ha : P.a ≠ 0) (hroots : P.roots = {x, y, z})
    (hd : d ≤ |P.discr|) (hA : |P.a| ≤ A)
    (hxz : |x - z| ≤ M) (hyz : |y - z| ≤ M)
    (hthreshold : A ^ 4 * M ^ 4 * eps ^ 2 < d) :
    eps < |x - y| := by
  have hroots' : (Cubic.map (RingHom.id ℝ) P).roots = {x, y, z} := by
    have hmap : Cubic.map (RingHom.id ℝ) P = P := by
      ext <;> simp [Cubic.map]
    rw [hmap]
    exact hroots
  have hdisc := Cubic.discr_eq_prod_three_roots
    (P := P) (φ := RingHom.id ℝ) ha hroots'
  have hdisc' : P.discr = (P.a * P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
    simpa using hdisc
  have hprod :
      |P.discr| = |P.a| ^ 4 * |x - y| ^ 2 * |x - z| ^ 2 * |y - z| ^ 2 := by
    rw [hdisc']
    simp only [abs_pow, abs_mul]
    ring
  have hbound : |P.discr| ≤ A ^ 4 * M ^ 4 * |x - y| ^ 2 := by
    rw [hprod]
    calc
      |P.a| ^ 4 * |x - y| ^ 2 * |x - z| ^ 2 * |y - z| ^ 2
          ≤ A ^ 4 * |x - y| ^ 2 * |x - z| ^ 2 * |y - z| ^ 2 := by gcongr
      _ ≤ A ^ 4 * |x - y| ^ 2 * M ^ 2 * M ^ 2 := by gcongr
      _ = A ^ 4 * M ^ 4 * |x - y| ^ 2 := by ring
  by_contra hgap
  have hgap' : |x - y| ≤ eps := not_lt.mp hgap
  have hgapSq : |x - y| ^ 2 ≤ eps ^ 2 := by gcongr
  have : d ≤ A ^ 4 * M ^ 4 * eps ^ 2 := by
    calc
      d ≤ |P.discr| := hd
      _ ≤ A ^ 4 * M ^ 4 * |x - y| ^ 2 := hbound
      _ ≤ A ^ 4 * M ^ 4 * eps ^ 2 := by gcongr
  linarith

/-- A convenient pairwise-separation corollary using a common root-radius
bound. Once all three roots lie in `[-R, R]`, every auxiliary gap is at most
`2*R`, so one discriminant threshold separates all three pairs. -/
theorem cubic_roots_pairwise_gap_gt_of_discr_bound_and_radius
    (P : Cubic ℝ) {x y z d A R eps : ℝ}
    (ha : P.a ≠ 0) (hroots : P.roots = {x, y, z})
    (hd : d ≤ |P.discr|) (hA : |P.a| ≤ A)
    (hx : |x| ≤ R) (hy : |y| ≤ R) (hz : |z| ≤ R)
    (hthreshold : A ^ 4 * (2 * R) ^ 4 * eps ^ 2 < d) :
    eps < |x - y| ∧ eps < |x - z| ∧ eps < |y - z| := by
  have hxy : |x - y| ≤ 2 * R := by
    calc
      |x - y| ≤ |x| + |y| := abs_sub x y
      _ ≤ R + R := add_le_add hx hy
      _ = 2 * R := by ring
  have hxz : |x - z| ≤ 2 * R := by
    calc
      |x - z| ≤ |x| + |z| := abs_sub x z
      _ ≤ R + R := add_le_add hx hz
      _ = 2 * R := by ring
  have hyz : |y - z| ≤ 2 * R := by
    calc
      |y - z| ≤ |y| + |z| := abs_sub y z
      _ ≤ R + R := add_le_add hy hz
      _ = 2 * R := by ring
  have hrootsXZY : P.roots = {x, z, y} := by
    rw [hroots]
    exact congrArg (fun m : Multiset ℝ => x ::ₘ m) (Multiset.cons_swap y z 0)
  have hrootsYZX : P.roots = {y, z, x} := by
    rw [hroots]
    calc
      {x, y, z} = {y, x, z} := Multiset.cons_swap x y {z}
      _ = {y, z, x} :=
        congrArg (fun m : Multiset ℝ => y ::ₘ m) (Multiset.cons_swap x z 0)
  exact ⟨
    cubic_root_gap_gt_of_discr_bound P ha hroots hd hA hxz hyz hthreshold,
    cubic_root_gap_gt_of_discr_bound P ha hrootsXZY hd hA hxy (by simpa [abs_sub_comm] using hyz)
      hthreshold,
    cubic_root_gap_gt_of_discr_bound P ha hrootsYZX hd hA (by simpa [abs_sub_comm] using hxy)
      (by simpa [abs_sub_comm] using hxz) hthreshold⟩

end LeanCert.Engine.Algebra
