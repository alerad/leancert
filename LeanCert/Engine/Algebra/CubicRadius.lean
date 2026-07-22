/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.QCubic

/-!
# Executable radius and separation bounds for exact rational cubics

This module turns the discriminant separation theorem into an executable
mesh-width certificate.  A rational Cauchy bound supplies a common radius for
all roots; the checker then verifies the remaining exact rational inequality.
-/

namespace LeanCert.Engine

open LeanCert.Engine.Algebra

/-- An executable (slightly relaxed) Cauchy radius.  The sum in the numerator
is at least the usual maximum-coefficient numerator and is especially simple
to check over exact rationals. -/
def QCubic.cauchyRadius (P : QCubic) : ℚ :=
  1 + (|P.b| + |P.c| + |P.d|) / |P.a|

theorem QCubic.one_le_cauchyRadius (P : QCubic) : 1 ≤ P.cauchyRadius := by
  simp only [QCubic.cauchyRadius]
  exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))

/-- Every real root lies in the executable Cauchy radius. -/
theorem QCubic.root_abs_le_cauchyRadius (P : QCubic) (ha : P.a ≠ 0) {x : ℝ}
    (hx : x ∈ cubicZeroSet P.toReal) : |x| ≤ P.cauchyRadius := by
  simp only [cubicZeroSet, Set.mem_setOf_eq, QCubic.toReal] at hx
  let A : ℝ := |(P.a : ℝ)|
  let S : ℝ := |(P.b : ℝ)| + |(P.c : ℝ)| + |(P.d : ℝ)|
  have hA : 0 < A := by
    dsimp [A]
    exact abs_pos.mpr (by exact_mod_cast ha)
  have hS : 0 ≤ S := by positivity
  have hradius : (P.cauchyRadius : ℝ) = 1 + S / A := by
    simp [QCubic.cauchyRadius, A, S]
  rw [hradius]
  by_cases hx1 : |x| ≤ 1
  · exact hx1.trans (le_add_of_nonneg_right (div_nonneg hS hA.le))
  have hx1' : 1 < |x| := lt_of_not_ge hx1
  have hx0 : 0 < |x| := by linarith
  have heq : A * |x| ^ 3 =
      |(P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d| := by
    calc
      A * |x| ^ 3 = |(P.a : ℝ) * x ^ 3| := by simp [A, abs_mul, abs_pow]
      _ = |-((P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d)| := by
        congr 1
        linarith
      _ = |(P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d| := abs_neg _
  have htri :
      |(P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d| ≤
        |(P.b : ℝ)| * |x| ^ 2 + |(P.c : ℝ)| * |x| + |(P.d : ℝ)| := by
    calc
      |(P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x + P.d|
          ≤ |(P.b : ℝ) * x ^ 2 + (P.c : ℝ) * x| + |(P.d : ℝ)| := abs_add_le _ _
      _ ≤ |(P.b : ℝ) * x ^ 2| + |(P.c : ℝ) * x| + |(P.d : ℝ)| := by
        gcongr
        exact abs_add_le _ _
      _ = |(P.b : ℝ)| * |x| ^ 2 + |(P.c : ℝ)| * |x| + |(P.d : ℝ)| := by
        simp only [abs_mul, abs_pow]
  have hscale :
      |(P.b : ℝ)| * |x| ^ 2 + |(P.c : ℝ)| * |x| + |(P.d : ℝ)| ≤
        S * |x| ^ 2 := by
    dsimp [S]
    have hxx : |x| ≤ |x| ^ 2 := by nlinarith
    have hone : 1 ≤ |x| ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hxx (abs_nonneg (P.c : ℝ)),
      mul_le_mul_of_nonneg_left hone (abs_nonneg (P.d : ℝ))]
  have hmain : A * |x| ^ 3 ≤ S * |x| ^ 2 := heq.trans_le (htri.trans hscale)
  have hcancel : A * |x| ≤ S := by
    nlinarith [sq_pos_of_pos hx0]
  have hxdiv : |x| ≤ S / A := (le_div_iff₀ hA).2 (by simpa [mul_comm] using hcancel)
  linarith

/-- Check that `eps` is a strict pairwise root-separation bound.  The checker
uses exact rational arithmetic only. -/
def QCubic.separationMeshCheck (P : QCubic) (eps : ℚ) : Bool :=
  decide (P.a ≠ 0) && decide (0 < eps) &&
    decide (|P.a| ^ 4 * (2 * P.cauchyRadius) ^ 4 * eps ^ 2 < |P.discr|)

/-- A deterministic rational mesh candidate.  The checker remains the source
of truth; callers may use this value directly or provide a coarser candidate. -/
def QCubic.automaticSeparationMesh (P : QCubic) : ℚ :=
  let D := |P.discr|
  let C := |P.a| ^ 4 * (2 * P.cauchyRadius) ^ 4
  D / (1 + C + D)

/-- The deterministic mesh constructor passes the exact checker for every
genuine cubic with nonzero discriminant. -/
theorem QCubic.automaticSeparationMesh_check (P : QCubic)
    (ha : P.a ≠ 0) (hdiscr : P.discr ≠ 0) :
    P.separationMeshCheck P.automaticSeparationMesh = true := by
  let D : ℚ := |P.discr|
  let C : ℚ := |P.a| ^ 4 * (2 * P.cauchyRadius) ^ 4
  let T : ℚ := 1 + C + D
  have hD : 0 < D := by exact abs_pos.mpr hdiscr
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have hCD : C * D < T ^ 2 := by
    dsimp [T]
    nlinarith [sq_nonneg C, sq_nonneg D, mul_nonneg hC hD.le]
  have hthreshold : C * (D / T) ^ 2 < D := by
    rw [div_pow]
    rw [show C * (D ^ 2 / T ^ 2) = (C * D ^ 2) / T ^ 2 by ring]
    apply (div_lt_iff₀ (sq_pos_of_pos hT)).2
    nlinarith [mul_lt_mul_of_pos_right hCD hD]
  simp only [QCubic.separationMeshCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨ha, ?_⟩, ?_⟩
  · simpa [QCubic.automaticSeparationMesh, D, C, T] using div_pos hD hT
  · simpa [QCubic.automaticSeparationMesh, D, C, T] using hthreshold

theorem QCubic.mem_roots_iff_mem_zeroSet (P : QCubic) (ha : P.a ≠ 0) (x : ℝ) :
    x ∈ P.toReal.roots ↔ x ∈ cubicZeroSet P.toReal := by
  have haR : P.toReal.a ≠ 0 := by
    simp only [QCubic.toReal]
    exact_mod_cast ha
  have hp : P.toReal.toPoly ≠ 0 := by
    intro hp
    apply haR
    have := congrArg (fun q : Polynomial ℝ => q.coeff 3) hp
    simpa using this
  rw [Cubic.mem_roots_iff hp]
  simp [cubicZeroSet]

/-- Three distinct real zeros enumerate the root multiset of a genuine cubic. -/
theorem QCubic.roots_eq_three_of_mem (P : QCubic) (ha : P.a ≠ 0) {x y z : ℝ}
    (hx : x ∈ cubicZeroSet P.toReal) (hy : y ∈ cubicZeroSet P.toReal)
    (hz : z ∈ cubicZeroSet P.toReal)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    P.toReal.roots = {x, y, z} := by
  classical
  have hxroot := (P.mem_roots_iff_mem_zeroSet ha x).2 hx
  have hyroot := (P.mem_roots_iff_mem_zeroSet ha y).2 hy
  have hzroot := (P.mem_roots_iff_mem_zeroSet ha z).2 hz
  have hsub : ({x, y, z} : Multiset ℝ) ≤ P.toReal.roots := by
    change (x ::ₘ y ::ₘ {z}) ≤ P.toReal.roots
    rw [Multiset.cons_le_of_notMem (by simp [hxy, hxz])]
    refine ⟨hxroot, ?_⟩
    rw [Multiset.cons_le_of_notMem (by simp [hyz])]
    exact ⟨hyroot, Multiset.singleton_le.mpr hzroot⟩
  symm
  apply Multiset.eq_of_le_of_card_le hsub
  have haR : P.toReal.a ≠ 0 := by
    simp only [QCubic.toReal]
    exact_mod_cast ha
  calc
    P.toReal.roots.card = P.toReal.toPoly.roots.card := rfl
    _ ≤ P.toReal.toPoly.natDegree := Polynomial.card_roots' _
    _ = 3 := Cubic.natDegree_of_a_ne_zero haR

/-- Soundness of the exact separation-mesh checker. -/
theorem QCubic.separationMeshCheck_sound (P : QCubic) {eps : ℚ} {x y z : ℝ}
    (hcheck : P.separationMeshCheck eps = true)
    (hroots : P.toReal.roots = {x, y, z}) :
    (eps : ℝ) < |x - y| ∧ (eps : ℝ) < |x - z| ∧ (eps : ℝ) < |y - z| := by
  simp only [QCubic.separationMeshCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨ha, heps⟩, hthreshold⟩ := hcheck
  have haR : P.toReal.a ≠ 0 := by
    simp only [QCubic.toReal]
    exact_mod_cast ha
  have hp : P.toReal.toPoly ≠ 0 := by
    intro hp
    apply haR
    have := congrArg (fun q : Polynomial ℝ => q.coeff 3) hp
    simpa using this
  have root_mem_zeroSet {r : ℝ} (hr : r ∈ P.toReal.roots) :
      r ∈ cubicZeroSet P.toReal := by
    rw [Cubic.mem_roots_iff hp] at hr
    simpa [cubicZeroSet, Polynomial.IsRoot, Cubic.toPoly] using hr
  have hx : x ∈ cubicZeroSet P.toReal := root_mem_zeroSet (by rw [hroots]; simp)
  have hy : y ∈ cubicZeroSet P.toReal := root_mem_zeroSet (by rw [hroots]; simp)
  have hz : z ∈ cubicZeroSet P.toReal := root_mem_zeroSet (by rw [hroots]; simp)
  apply cubic_roots_pairwise_gap_gt_of_discr_bound_and_radius P.toReal haR hroots
  · exact le_rfl
  · exact le_rfl
  · exact P.root_abs_le_cauchyRadius ha hx
  · exact P.root_abs_le_cauchyRadius ha hy
  · exact P.root_abs_le_cauchyRadius ha hz
  · rw [QCubic.toReal_discr]
    simp only [QCubic.toReal]
    norm_cast

/-- User-facing separation: any two distinct real roots of a certified
three-root cubic are farther apart than the checked mesh width. -/
theorem QCubic.separationMeshCheck_sound_of_distinct_roots
    (P : QCubic) {eps : ℚ}
    (hcount : P.threeRootCountCheck = true)
    (hmesh : P.separationMeshCheck eps = true) {x y : ℝ}
    (hx : x ∈ cubicZeroSet P.toReal) (hy : y ∈ cubicZeroSet P.toReal)
    (hxy : x ≠ y) : (eps : ℝ) < |x - y| := by
  have hcard := P.threeRootCountCheck_sound hcount
  have ha : P.a ≠ 0 := by
    simp only [QCubic.threeRootCountCheck, Bool.and_eq_true, decide_eq_true_eq] at hcount
    exact hcount.1
  have hz : ∃ z ∈ cubicZeroSet P.toReal, z ≠ x ∧ z ≠ y := by
    by_contra hnone
    push Not at hnone
    have hsub : cubicZeroSet P.toReal ⊆ ({x, y} : Set ℝ) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hpair
      have hzx : z ≠ x := fun h => hpair (Or.inl h)
      exact hpair (Or.inr (hnone z hz hzx))
    have hle := Set.ncard_le_ncard hsub (by simp : ({x, y} : Set ℝ).Finite)
    rw [hcard] at hle
    simp [hxy] at hle
  obtain ⟨z, hz, hzx, hzy⟩ := hz
  have hroots := P.roots_eq_three_of_mem ha hx hy hz hxy hzx.symm hzy.symm
  exact (P.separationMeshCheck_sound hmesh hroots).1

end LeanCert.Engine
