import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Tactic

/-!
# The finite imaginary-shift strip contraction

The operator averages f(z+ia) and f(z-ia). A conjugate-pair norm comparison
proves strict separation outside the contracted strip. Multiplicities are
retained in the root multiset; no simple-root or root-motion hypothesis is used.
This file does not assert the corresponding theorem for the DBN heat integral.
-/
namespace LeanCert.Analysis.DBN
open Complex Polynomial ComplexConjugate

noncomputable def shiftAverage (f : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (f (z + (a : ℂ)*I) + f (z - (a : ℂ)*I)) / 2

/-- The exact algebra behind contraction of a conjugate pair. -/
theorem conjugate_pair_shift_difference (z r : ℂ) (a : ℝ) :
    normSq ((z+(a : ℂ)*I-r)*(z+(a : ℂ)*I-conj r)) -
      normSq ((z-(a : ℂ)*I-r)*(z-(a : ℂ)*I-conj r)) =
      8*a*z.im*((z.re-r.re)^2 + z.im^2 + a^2 - r.im^2) := by
  simp only [normSq_apply, add_re, sub_re, mul_re, ofReal_re,
    ofReal_im, I_re, I_im, conj_re, add_im, sub_im, mul_im, conj_im]
  ring

theorem conjugate_pair_shift_lt {z r : ℂ} {a : ℝ}
    (ha : 0 < a) (hy : 0 < z.im) (hr : r.im^2 < z.im^2+a^2) :
    normSq ((z-(a : ℂ)*I-r)*(z-(a : ℂ)*I-conj r)) <
      normSq ((z+(a : ℂ)*I-r)*(z+(a : ℂ)*I-conj r)) := by
  have h := conjugate_pair_shift_difference z r a
  have hb : 0 < (z.re-r.re)^2 + z.im^2+a^2-r.im^2 := by nlinarith [sq_nonneg (z.re-r.re)]
  have hp : 0 < 8*a*z.im*((z.re-r.re)^2 + z.im^2+a^2-r.im^2) := by positivity
  linarith

private theorem pair_product (roots : Multiset ℂ) (hc : roots.map conj = roots) (w : ℂ) :
    (roots.map (fun r => normSq ((w-r)*(w-conj r)))).prod =
      ((roots.map (fun r => normSq (w-r))).prod)^2 := by
  simp only [normSq_mul, Multiset.prod_map_mul]
  have he : (roots.map (fun r => normSq (w-conj r))).prod =
      (roots.map (fun r => normSq (w-r))).prod := by
    have h := congrArg (fun s : Multiset ℂ => (s.map (fun r => normSq (w-r))).prod) hc
    simpa only [Multiset.map_map, Function.comp_def] using h
  rw [he]
  ring

private theorem prod_strict {ι : Type*} (s : Multiset ι) (hs : s ≠ 0)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | @cons i s ih =>
    have hi := hf i (Multiset.mem_cons_self i s)
    have hgi := hfg i (Multiset.mem_cons_self i s)
    have hf' : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Multiset.mem_cons_of_mem hj)
    have hg' : ∀ j ∈ s, f j < g j := fun j hj => hfg j (Multiset.mem_cons_of_mem hj)
    by_cases he : s = 0
    · subst s
      simpa using hgi
    · have ht := ih he hf' hg'
      have ht0 : 0 ≤ (s.map f).prod := Multiset.prod_nonneg (by simpa using hf')
      simp only [Multiset.map_cons, Multiset.prod_cons]
      nlinarith

/-- Finite conjugation-invariant root multisets obey a strict shifted norm inequality. -/
theorem rootProduct_shift_lt (roots : Multiset ℂ) (hne : roots ≠ 0)
    (hc : roots.map conj = roots) {z : ℂ} {a : ℝ} (ha : 0 < a) (hy : 0 < z.im)
    (hr : ∀ r ∈ roots, r.im^2 < z.im^2+a^2) :
    normSq ((roots.map (fun r => z-(a : ℂ)*I-r)).prod) <
      normSq ((roots.map (fun r => z+(a : ℂ)*I-r)).prod) := by
  have h := prod_strict roots hne
    (fun r => normSq ((z-(a : ℂ)*I-r)*(z-(a : ℂ)*I-conj r)))
    (fun r => normSq ((z+(a : ℂ)*I-r)*(z+(a : ℂ)*I-conj r)))
    (fun r _ => normSq_nonneg _) (fun r hr' => conjugate_pair_shift_lt ha hy (hr r hr'))
  rw [pair_product roots hc, pair_product roots hc] at h
  have hm : 0 ≤ (roots.map (fun r => normSq (z-(a : ℂ)*I-r))).prod :=
    Multiset.prod_nonneg (by simpa using fun r (_ : r ∈ roots) => normSq_nonneg (z-(a : ℂ)*I-r))
  have hp : 0 ≤ (roots.map (fun r => normSq (z+(a : ℂ)*I-r))).prod :=
    Multiset.prod_nonneg (by simpa using fun r (_ : r ∈ roots) => normSq_nonneg (z+(a : ℂ)*I-r))
  have he (w : ℂ) : normSq ((roots.map (fun r => w-r)).prod) =
      (roots.map (fun r => normSq (w-r))).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  rw [he, he]
  nlinarith

private theorem polynomial_roots_conj (p : ℂ[X]) (hc : p.map (starRingEnd ℂ) = p) :
    p.roots.map conj = p.roots := by
  have h := (IsAlgClosed.splits p).roots_map (starRingEnd ℂ)
  rw [hc] at h
  exact h.symm

/-- One imaginary-shift average contracts a real polynomial's strip.
The squared formulation includes the case when the entire strip collapses. -/
theorem polynomial_shiftAverage_strip (p : ℂ[X]) (hp : p ≠ 0)
    (hc : p.map (starRingEnd ℂ) = p) {b a : ℝ} (ha : 0 < a)
    (hstrip : ∀ r : ℂ, p.eval r = 0 → r.im^2 ≤ b^2)
    {z : ℂ} (hz : shiftAverage p.eval a z = 0) :
    z.im^2 ≤ max (b^2-a^2) 0 := by
  have hup {w : ℂ} (hw : 0 < w.im) (hb : b^2 < w.im^2+a^2) :
      shiftAverage p.eval a w ≠ 0 := by
    by_cases he : p.roots = 0
    · simp [shiftAverage, (IsAlgClosed.splits p).eval_eq_prod_roots, he,
        leadingCoeff_ne_zero.mpr hp]
    · have hr : ∀ r ∈ p.roots, r.im^2 < w.im^2+a^2 := by
        intro r hr
        exact (hstrip r ((mem_roots hp).mp hr)).trans_lt hb
      have h := rootProduct_shift_lt p.roots he (polynomial_roots_conj p hc) ha hw hr
      have hl : 0 < normSq p.leadingCoeff := by
        exact normSq_pos.mpr (leadingCoeff_ne_zero.mpr hp)
      have hn : normSq (p.eval (w-(a : ℂ)*I)) < normSq (p.eval (w+(a : ℂ)*I)) := by
        rw [(IsAlgClosed.splits p).eval_eq_prod_roots, (IsAlgClosed.splits p).eval_eq_prod_roots,
          normSq_mul, normSq_mul]
        exact mul_lt_mul_of_pos_left h hl
      intro hzero
      have heq : p.eval (w+(a : ℂ)*I) = -p.eval (w-(a : ℂ)*I) := by
        apply eq_neg_of_add_eq_zero_left
        simpa [shiftAverage, div_eq_zero_iff] using hzero
      rw [heq, normSq_neg] at hn
      exact (lt_irrefl _ hn)
  by_contra hb
  have hsq : max (b^2-a^2) 0 < z.im^2 := lt_of_not_ge hb
  have hne : z.im ≠ 0 := by intro h; simp [h] at hsq
  have hb' : b^2 < z.im^2+a^2 := by have := le_max_left (b^2-a^2) 0; linarith
  rcases lt_or_gt_of_ne hne with hy | hy
  · have hz' : shiftAverage p.eval a (conj z) = 0 := by
      have he (w : ℂ) : p.eval (conj w) = conj (p.eval w) := by
        have h := Polynomial.eval₂_at_apply (p := p) (starRingEnd ℂ) w
        simpa [← Polynomial.eval_map, hc] using h
      simp only [shiftAverage] at hz ⊢
      rw [show conj z+(a : ℂ)*I = conj (z-(a : ℂ)*I) by simp,
        show conj z-(a : ℂ)*I = conj (z+(a : ℂ)*I) by simp [sub_eq_add_neg], he, he]
      simpa [map_div₀, map_add, add_comm] using congrArg conj hz
    exact hup (by simpa using neg_pos.mpr hy) (by simpa using hb') hz'
  · exact hup hy hb' hz

/-- A shift at least as wide as the original strip leaves only real zeros. -/
theorem polynomial_shiftAverage_real (p : ℂ[X]) (hp : p ≠ 0)
    (hc : p.map (starRingEnd ℂ) = p) {b a : ℝ} (ha : 0 < a)
    (hba : b^2 ≤ a^2) (hstrip : ∀ r : ℂ, p.eval r = 0 → r.im^2 ≤ b^2)
    {z : ℂ} (hz : shiftAverage p.eval a z = 0) : z.im = 0 := by
  have h := polynomial_shiftAverage_strip p hp hc ha hstrip hz
  rw [max_eq_right (sub_nonpos.mpr hba)] at h
  nlinarith [sq_nonneg z.im]

/-- The real-coefficient specialization of the finite contraction theorem. -/
theorem realPolynomial_shiftAverage_strip (p : ℝ[X]) (hp : p ≠ 0)
    {b a : ℝ} (ha : 0 < a)
    (hstrip : ∀ r : ℂ, (p.map (algebraMap ℝ ℂ)).eval r = 0 → r.im^2 ≤ b^2)
    {z : ℂ} (hz : shiftAverage (p.map (algebraMap ℝ ℂ)).eval a z = 0) :
    z.im^2 ≤ max (b^2-a^2) 0 := by
  apply polynomial_shiftAverage_strip (p.map (algebraMap ℝ ℂ))
    (by simpa using hp) ?_ ha hstrip hz
  ext n
  simp

end LeanCert.Analysis.DBN
