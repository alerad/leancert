/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.QPoly
import LeanCert.Engine.TaylorModel.Core
import LeanCert.Engine.Integrate

/-!
# Computable Bernstein certificates for rational polynomials

`Engine/TaylorModel/Core.lean` proves that a polynomial on a closed interval lies
between the minimum and maximum of its Bernstein coefficients, but states the
result over Mathlib's noncomputable `Polynomial ℚ`. This file evaluates the same
enclosure on the executable `QPoly` representation so it can serve as a Boolean
certificate:

* `bernsteinCoeffs p I` — exact Bernstein coefficients of `p` on `[I.lo, I.hi]`,
  obtained by composing `p` with the affine reparametrisation of `[0,1]` onto
  `I` and converting monomial to Bernstein coefficients;
* `bernsteinEnclosure p I` — the interval `[min bₖ, max bₖ]`;
* `bernsteinCheck cmp p c I depth` — a recursive certificate that either proves
  the comparison from the enclosure on the current box or bisects, up to `depth`.

Bisection recomputes the coefficients on each child from `p` (exact, `O(n²)`
per box) so the soundness proof reduces to the one-box enclosure every time.
Unlike Horner interval evaluation, the Bernstein enclosure is exact at the
endpoints and converges quadratically under bisection, so polynomial bounds
that are tight near an endpoint need no subdivision at all.
-/

namespace LeanCert.Engine.QPoly

open LeanCert.Core

/-! ### Affine reparametrisation -/

/-- The affine map `t ↦ I.lo + (I.hi - I.lo) · t` sending `[0,1]` onto `I`. -/
def affineMap (I : IntervalRat) : QPoly :=
  (constant I.lo).add ((constant (I.hi - I.lo)).mul X)

theorem aeval_affineMap (I : IntervalRat) (t : ℝ) :
    Polynomial.aeval t (affineMap I).toPoly = (I.lo : ℝ) + ((I.hi : ℝ) - I.lo) * t := by
  simp [affineMap, toPoly_add, toPoly_mul, toPoly_constant, toPoly_X]

/-- Coefficients of `t ↦ p(I.lo + (I.hi - I.lo) t)`, padded to be nonempty. -/
def shiftedCoeffs (p : QPoly) (I : IntervalRat) : List ℚ :=
  match (p.compose (affineMap I)).coeffs.toList with
  | [] => [0]
  | c :: cs => c :: cs

theorem shiftedCoeffs_length_pos (p : QPoly) (I : IntervalRat) :
    0 < (shiftedCoeffs p I).length := by
  unfold shiftedCoeffs
  split <;> simp

theorem aeval_shiftedCoeffs (p : QPoly) (I : IntervalRat) (t : ℝ) :
    Polynomial.aeval ((I.lo : ℝ) + ((I.hi : ℝ) - I.lo) * t) p.toPoly =
      ∑ j ∈ Finset.range (shiftedCoeffs p I).length,
        ((shiftedCoeffs p I).getD j 0 : ℝ) * t ^ j := by
  rw [← aeval_affineMap, ← aeval_compose, aeval_toPoly_eq_sum]
  unfold shiftedCoeffs
  split
  · next h => simp [h]
  · next c cs h => rw [h]

/-! ### Bernstein coefficients and enclosure -/

/-- Exact Bernstein coefficients of `p` on `I` (degree `p.coeffs.size - 1`). -/
def bernsteinCoeffs (p : QPoly) (I : IntervalRat) : List ℚ :=
  monomialToBernstein (shiftedCoeffs p I)

theorem bernsteinCoeffs_length (p : QPoly) (I : IntervalRat) :
    (bernsteinCoeffs p I).length = (shiftedCoeffs p I).length :=
  monomialToBernstein_length _ (shiftedCoeffs_length_pos p I)

/-- `[min bₖ, max bₖ]` over the Bernstein coefficients of `p` on `I`. -/
def bernsteinEnclosure (p : QPoly) (I : IntervalRat) : IntervalRat :=
  let bs := bernsteinCoeffs p I
  ⟨(listMinMax bs (bs.headD 0)).1, (listMinMax bs (bs.headD 0)).2, listMinMax_le _ _⟩

private theorem getElem_zero_eq_headD (bs : List ℚ) (h : 0 < bs.length) :
    bs[0]'h = bs.headD 0 := by
  cases bs with
  | nil => simp at h
  | cons b bs => rfl

/-- Parametrise `x ∈ I` as `I.lo + (I.hi - I.lo) t` with `t ∈ [0,1]`. -/
private theorem exists_param {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (I.lo : ℝ) + ((I.hi : ℝ) - I.lo) * t := by
  rw [IntervalRat.mem_def] at hx
  obtain ⟨hlo, hhi⟩ := hx
  by_cases hdeg : (I.lo : ℝ) = I.hi
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    have : x = I.lo := le_antisymm (hdeg ▸ hhi) hlo
    simp [this]
  · have hlt : (I.lo : ℝ) < I.hi := lt_of_le_of_ne (by exact_mod_cast I.le) hdeg
    have hw : (0 : ℝ) < (I.hi : ℝ) - I.lo := by linarith
    refine ⟨(x - I.lo) / ((I.hi : ℝ) - I.lo), ?_, ?_, ?_⟩
    · exact div_nonneg (by linarith) hw.le
    · rw [div_le_one hw]; linarith
    · field_simp
      ring

/-- **Bernstein enclosure.** Every value of `p` on `I` lies in
`bernsteinEnclosure p I`. -/
theorem aeval_mem_bernsteinEnclosure (p : QPoly) (I : IntervalRat) {x : ℝ}
    (hx : x ∈ I) : Polynomial.aeval x p.toPoly ∈ bernsteinEnclosure p I := by
  obtain ⟨t, ht0, ht1, rfl⟩ := exists_param hx
  rw [aeval_shiftedCoeffs]
  set qs := shiftedCoeffs p I with hqs
  have hlen : qs.length = (qs.length - 1) + 1 :=
    (Nat.sub_add_cancel (shiftedCoeffs_length_pos p I)).symm
  have key := bernstein_enclosure_01 qs (qs.length - 1) hlen t ht0 ht1
  simp only at key
  rw [getElem_zero_eq_headD] at key
  rw [← hlen] at key
  simp only [bernsteinEnclosure, bernsteinCoeffs, IntervalRat.mem_def]
  exact key

/-! ### Recursive certificates -/

/-- The four comparisons certified against an enclosure. -/
inductive Cmp where
  | lower
  | upper
  | strictLower
  | strictUpper
  deriving DecidableEq, Repr, Inhabited

/-- Semantic comparison `c ?? y` for each `Cmp`. -/
def Cmp.holds : Cmp → ℝ → ℝ → Prop
  | .lower, c, y => c ≤ y
  | .upper, c, y => y ≤ c
  | .strictLower, c, y => c < y
  | .strictUpper, c, y => y < c

/-- Does the enclosure `J` prove `c ?? y` for every `y ∈ J`? -/
def Cmp.check : Cmp → IntervalRat → ℚ → Bool
  | .lower, J, c => decide (c ≤ J.lo)
  | .upper, J, c => decide (J.hi ≤ c)
  | .strictLower, J, c => decide (c < J.lo)
  | .strictUpper, J, c => decide (J.hi < c)

theorem Cmp.holds_of_check {cmp : Cmp} {J : IntervalRat} {c : ℚ}
    (h : cmp.check J c = true) {y : ℝ} (hy : y ∈ J) : cmp.holds c y := by
  rw [IntervalRat.mem_def] at hy
  obtain ⟨hlo, hhi⟩ := hy
  cases cmp <;> simp only [Cmp.check, decide_eq_true_eq] at h <;> simp only [Cmp.holds]
  · exact le_trans (by exact_mod_cast h) hlo
  · exact le_trans hhi (by exact_mod_cast h)
  · exact lt_of_lt_of_le (by exact_mod_cast h) hlo
  · exact lt_of_le_of_lt hhi (by exact_mod_cast h)

/-- Recursive Bernstein certificate: prove `cmp` from the enclosure on `I`, or
bisect and certify both halves, up to `depth` levels. -/
def bernsteinCheck (cmp : Cmp) (p : QPoly) (c : ℚ) (I : IntervalRat) : Nat → Bool
  | 0 => cmp.check (bernsteinEnclosure p I) c
  | depth + 1 =>
      cmp.check (bernsteinEnclosure p I) c ||
        (bernsteinCheck cmp p c (splitMid I).1 depth &&
          bernsteinCheck cmp p c (splitMid I).2 depth)

/-- Least depth at which `bernsteinCheck` succeeds, if any up to `maxDepth`.
Untrusted search helper used for reporting; certificates re-run the checker. -/
def bernsteinDepth? (cmp : Cmp) (p : QPoly) (c : ℚ) (I : IntervalRat)
    (maxDepth : Nat) : Option Nat :=
  (List.range (maxDepth + 1)).find? fun depth => bernsteinCheck cmp p c I depth

/-- Number of boxes examined by `bernsteinCheck` (reporting only). -/
def bernsteinBoxes (cmp : Cmp) (p : QPoly) (c : ℚ) (I : IntervalRat) : Nat → Nat
  | 0 => 1
  | depth + 1 =>
      if cmp.check (bernsteinEnclosure p I) c then 1
      else 1 + bernsteinBoxes cmp p c (splitMid I).1 depth +
        bernsteinBoxes cmp p c (splitMid I).2 depth

/-- **Soundness of the recursive Bernstein certificate.** -/
theorem bernsteinCheck_sound {cmp : Cmp} {p : QPoly} {c : ℚ} {I : IntervalRat}
    {depth : Nat} (h : bernsteinCheck cmp p c I depth = true) :
    ∀ x ∈ I, cmp.holds c (Polynomial.aeval x p.toPoly) := by
  induction depth generalizing I with
  | zero =>
      intro x hx
      exact Cmp.holds_of_check h (aeval_mem_bernsteinEnclosure p I hx)
  | succ depth ih =>
      intro x hx
      simp only [bernsteinCheck, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hl, hr⟩
      · exact Cmp.holds_of_check h (aeval_mem_bernsteinEnclosure p I hx)
      · rcases mem_splitMid hx with hx' | hx'
        · exact ih hl x hx'
        · exact ih hr x hx'

/-- Lower bounds from a Bernstein certificate. -/
theorem le_aeval_of_bernsteinCheck {p : QPoly} {c : ℚ} {I : IntervalRat} {depth : Nat}
    (h : bernsteinCheck .lower p c I depth = true) :
    ∀ x ∈ I, (c : ℝ) ≤ Polynomial.aeval x p.toPoly :=
  bernsteinCheck_sound h

theorem aeval_le_of_bernsteinCheck {p : QPoly} {c : ℚ} {I : IntervalRat} {depth : Nat}
    (h : bernsteinCheck .upper p c I depth = true) :
    ∀ x ∈ I, Polynomial.aeval x p.toPoly ≤ (c : ℝ) :=
  bernsteinCheck_sound h

theorem lt_aeval_of_bernsteinCheck {p : QPoly} {c : ℚ} {I : IntervalRat} {depth : Nat}
    (h : bernsteinCheck .strictLower p c I depth = true) :
    ∀ x ∈ I, (c : ℝ) < Polynomial.aeval x p.toPoly :=
  bernsteinCheck_sound h

theorem aeval_lt_of_bernsteinCheck {p : QPoly} {c : ℚ} {I : IntervalRat} {depth : Nat}
    (h : bernsteinCheck .strictUpper p c I depth = true) :
    ∀ x ∈ I, Polynomial.aeval x p.toPoly < (c : ℝ) :=
  bernsteinCheck_sound h

end LeanCert.Engine.QPoly
