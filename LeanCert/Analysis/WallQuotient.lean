/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.IntervalCases

/-!
# Wall quotients: enclosures at removable singularities

Interval evaluation degenerates at a point `w` where an expression has the
form `num/den` with `num w = den w = 0`: the order-0 data is `0/0`, and a
naive enclosure is vacuous. The information lives one jet order up. This
module provides the order-1 enclosure: by the Cauchy mean value theorem,
on an interval to the right of the wall the quotient is trapped by any
uniform bounds on the derivative ratio,

  `lo · den′ ≤ num′ ≤ hi · den′  on (w, b)   ⟹   num t / den t ∈ [lo, hi]`.

The derivative bounds are ordinary (wall-free) interval-evaluation targets,
so this theorem converts a singular enclosure problem into a regular one.

`expm1_div_self_mem` is the model instance: `(eˣ − 1)/x ∈ [1, e]` on `(0,1)`.

## Roadmap

* Order-`k` walls (`num`, `den` vanishing to higher order) via iterated
  Cauchy MVT or Taylor remainders, for quotients like the symmetric
  log integrand of the Li2 development, whose wall data currently uses
  bespoke tail lemmas.
* A left-of-wall variant and a two-sided wrapper.
* Engine hookup: a wall-aware partition step for `interval_integrate`
  that evaluates jets at singular endpoints and the standard interval
  engine elsewhere.
-/

namespace LeanCert.Analysis.WallQuotient

open Set

/-- Order-1 wall enclosure. If `num` and `den` both vanish at `w`, `den`
has positive derivative on `(w, b)`, and the derivative ratio is trapped in
`[lo, hi]` there, then the quotient is trapped in `[lo, hi]` on `(w, b)`. -/
theorem quotient_mem_of_deriv_ratio_bounds
    {num den num' den' : ℝ → ℝ} {w b lo hi : ℝ}
    (hnum0 : num w = 0) (hden0 : den w = 0)
    (hnumc : ContinuousOn num (Icc w b))
    (hdenc : ContinuousOn den (Icc w b))
    (hnumd : ∀ x ∈ Ioo w b, HasDerivAt num (num' x) x)
    (hdend : ∀ x ∈ Ioo w b, HasDerivAt den (den' x) x)
    (hden'pos : ∀ x ∈ Ioo w b, 0 < den' x)
    (hlo : ∀ x ∈ Ioo w b, lo * den' x ≤ num' x)
    (hhi : ∀ x ∈ Ioo w b, num' x ≤ hi * den' x)
    {t : ℝ} (ht : t ∈ Ioo w b) :
    num t / den t ∈ Icc lo hi := by
  obtain ⟨hwt, htb⟩ := ht
  have hIccSub : Icc w t ⊆ Icc w b := Icc_subset_Icc_right htb.le
  have hIooSub : Ioo w t ⊆ Ioo w b := Ioo_subset_Ioo_right htb.le
  -- `den t > 0` by the mean value theorem and `den′ > 0`.
  obtain ⟨c₀, hc₀mem, hc₀⟩ := exists_hasDerivAt_eq_slope den den' hwt
    (hdenc.mono hIccSub) (fun x hx => hdend x (hIooSub hx))
  have hdent_pos : 0 < den t := by
    have hd'c₀ := hden'pos c₀ (hIooSub hc₀mem)
    have htw : (0 : ℝ) < t - w := by linarith
    have hEq : den t - den w = den' c₀ * (t - w) := by
      rw [hc₀]
      field_simp
    have hpos : 0 < den' c₀ * (t - w) := mul_pos hd'c₀ htw
    rw [← hEq, hden0] at hpos
    linarith
  -- Cauchy MVT: the quotient is a derivative ratio at an interior point.
  obtain ⟨c, hcmem, hc⟩ := exists_ratio_hasDerivAt_eq_ratio_slope num num' hwt
    (hnumc.mono hIccSub) (fun x hx => hnumd x (hIooSub hx))
    den den' (hdenc.mono hIccSub) (fun x hx => hdend x (hIooSub hx))
  rw [hnum0, hden0, sub_zero, sub_zero] at hc
  -- `hc : den t * num' c = num t * den' c`
  have hcb := hIooSub hcmem
  have hd'c := hden'pos c hcb
  constructor
  · rw [le_div_iff₀ hdent_pos]
    have h1 : lo * den' c ≤ num' c := hlo c hcb
    have h2 : lo * den' c * den t ≤ num' c * den t :=
      mul_le_mul_of_nonneg_right h1 hdent_pos.le
    have h3 : (lo * den t) * den' c ≤ num t * den' c := by nlinarith [hc]
    exact le_of_mul_le_mul_right h3 hd'c
  · rw [div_le_iff₀ hdent_pos]
    have h1 : num' c ≤ hi * den' c := hhi c hcb
    have h2 : num' c * den t ≤ hi * den' c * den t :=
      mul_le_mul_of_nonneg_right h1 hdent_pos.le
    have h3 : num t * den' c ≤ (hi * den t) * den' c := by nlinarith [hc]
    exact le_of_mul_le_mul_right h3 hd'c

/-- Model instance: `(eˣ − 1)/x ∈ [1, e]` on `(0, 1)`, with the wall at
`x = 0` handled by `quotient_mem_of_deriv_ratio_bounds` and the derivative
bounds `1 ≤ eˣ ≤ e` as the regular interval data. -/
theorem expm1_div_self_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (Real.exp t - 1) / t ∈ Icc (1 : ℝ) (Real.exp 1) := by
  have h := quotient_mem_of_deriv_ratio_bounds
    (num := fun x => Real.exp x - 1) (den := fun x => x)
    (num' := fun x => Real.exp x) (den' := fun _ => (1 : ℝ))
    (w := 0) (b := 1) (lo := 1) (hi := Real.exp 1)
    (by simp) rfl
    ((Real.continuous_exp.sub continuous_const).continuousOn)
    (continuous_id.continuousOn)
    (fun x _ => (Real.hasDerivAt_exp x).sub_const 1)
    (fun x _ => hasDerivAt_id x)
    (fun _ _ => one_pos)
    (fun x hx => by simpa using Real.one_le_exp hx.1.le)
    (fun x hx => by simpa using Real.exp_le_exp.mpr hx.2.le)
    ht
  simpa using h

/-! ### Order-`k` walls via derivative ladders

When numerator and denominator both vanish to order `k` at the wall, the
quotient is controlled by ratio bounds on the `k`-th derivatives. The
derivative data is packaged as a ladder: explicit functions `f 0, …, f k`
with each `f (i+1)` the derivative of `f i`, avoiding the `iteratedDeriv`
API entirely. -/

/-- A derivative ladder of order `k` on `[w, b]`: functions `f 0, …, f k`
with `f (i+1)` the derivative of `f i` on `(w, b)` for `i < k`, each level
below the top continuous on `[w, b]` and vanishing at the wall `w`. -/
structure DerivLadder (k : ℕ) (w b : ℝ) where
  /-- The ladder of functions; only levels `0, …, k` are meaningful. -/
  f : ℕ → ℝ → ℝ
  cont : ∀ i < k, ContinuousOn (f i) (Icc w b)
  deriv : ∀ i < k, ∀ x ∈ Ioo w b, HasDerivAt (f i) (f (i + 1) x) x
  zero : ∀ i < k, f i w = 0

namespace DerivLadder

/-- Drop the bottom level of a ladder. -/
def tail {k : ℕ} {w b : ℝ} (L : DerivLadder (k + 1) w b) : DerivLadder k w b where
  f i := L.f (i + 1)
  cont i hi := L.cont (i + 1) (by omega)
  deriv i hi := L.deriv (i + 1) (by omega)
  zero i hi := L.zero (i + 1) (by omega)

/-- Positivity propagates down a ladder: if the top level is positive on
`(w, b)`, every level is, by the mean value theorem and the wall zeros. -/
theorem pos_of_top (k : ℕ) : ∀ (w b : ℝ) (L : DerivLadder k w b),
    (∀ x ∈ Ioo w b, 0 < L.f k x) →
    ∀ i ≤ k, ∀ x ∈ Ioo w b, 0 < L.f i x := by
  induction k with
  | zero =>
    intro w b L htop i hi x hx
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact htop x hx
  | succ k ih =>
    intro w b L htop i hi x hx
    cases i with
    | succ j => exact ih w b L.tail htop j (by omega) x hx
    | zero =>
      obtain ⟨hwx, hxb⟩ := hx
      have hcont : ContinuousOn (L.f 0) (Icc w x) :=
        (L.cont 0 (by omega)).mono (Icc_subset_Icc_right hxb.le)
      have hderiv : ∀ y ∈ Ioo w x, HasDerivAt (L.f 0) (L.f 1 y) y :=
        fun y hy => L.deriv 0 (by omega) y (Ioo_subset_Ioo_right hxb.le hy)
      obtain ⟨c, hcmem, hc⟩ :=
        exists_hasDerivAt_eq_slope (L.f 0) (L.f 1) hwx hcont hderiv
      have hpos1 : 0 < L.f 1 c :=
        ih w b L.tail htop 0 (Nat.zero_le k) c (Ioo_subset_Ioo_right hxb.le hcmem)
      have htw : (0 : ℝ) < x - w := by linarith
      have hEq : L.f 0 x - L.f 0 w = L.f 1 c * (x - w) := by
        rw [hc]
        field_simp
      have hpos := mul_pos hpos1 htw
      rw [← hEq, L.zero 0 (by omega)] at hpos
      linarith

end DerivLadder

/-- **Order-`k` wall enclosure.** If numerator and denominator ladders vanish
to order `k` at the wall and the top-level derivative ratio is trapped in
`[lo, hi]` on `(w, b)` (with positive top denominator derivative), then the
quotient of the bottom levels is trapped in `[lo, hi]` on `(w, b)`. -/
theorem quotient_mem_of_derivLadder {w b lo hi : ℝ} :
    ∀ (k : ℕ), 0 < k → ∀ (N D : DerivLadder k w b),
    (∀ x ∈ Ioo w b, 0 < D.f k x) →
    (∀ x ∈ Ioo w b, lo * D.f k x ≤ N.f k x) →
    (∀ x ∈ Ioo w b, N.f k x ≤ hi * D.f k x) →
    ∀ t ∈ Ioo w b, N.f 0 t / D.f 0 t ∈ Icc lo hi := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro _ N D hpos hlo hhi t ht
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- order 1: the Cauchy MVT core.
      exact quotient_mem_of_deriv_ratio_bounds
        (N.zero 0 (by omega)) (D.zero 0 (by omega))
        (N.cont 0 (by omega)) (D.cont 0 (by omega))
        (N.deriv 0 (by omega)) (D.deriv 0 (by omega))
        hpos hlo hhi ht
    · -- order k+1, k ≥ 1: the tails give level-1 quotient bounds everywhere,
      -- which convert to level-1 ratio bounds for the order-1 core.
      have hDpos1 : ∀ x ∈ Ioo w b, 0 < D.f 1 x := fun x hx =>
        DerivLadder.pos_of_top (k + 1) w b D hpos 1 (by omega) x hx
      have hq : ∀ x ∈ Ioo w b, N.tail.f 0 x / D.tail.f 0 x ∈ Icc lo hi :=
        fun x hx => ih hk N.tail D.tail hpos hlo hhi x hx
      have hlo1 : ∀ x ∈ Ioo w b, lo * D.f 1 x ≤ N.f 1 x := by
        intro x hx
        have h : lo ≤ N.f 1 x / D.f 1 x := (hq x hx).1
        have hp := hDpos1 x hx
        rw [le_div_iff₀ hp] at h
        exact h
      have hhi1 : ∀ x ∈ Ioo w b, N.f 1 x ≤ hi * D.f 1 x := by
        intro x hx
        have h : N.f 1 x / D.f 1 x ≤ hi := (hq x hx).2
        have hp := hDpos1 x hx
        rw [div_le_iff₀ hp] at h
        exact h
      exact quotient_mem_of_deriv_ratio_bounds
        (N.zero 0 (by omega)) (D.zero 0 (by omega))
        (N.cont 0 (by omega)) (D.cont 0 (by omega))
        (N.deriv 0 (by omega)) (D.deriv 0 (by omega))
        hDpos1 hlo1 hhi1 ht

/-- Numerator ladder for the order-2 model instance:
`eˣ − x − 1`, `eˣ − 1`, `eˣ`. -/
private noncomputable def expm1SubLadder : DerivLadder 2 0 1 where
  f
    | 0 => fun x => Real.exp x - x - 1
    | 1 => fun x => Real.exp x - 1
    | _ + 2 => fun x => Real.exp x
  cont := by
    intro i hi
    interval_cases i
    · exact ((Real.continuous_exp.sub continuous_id).sub
        continuous_const).continuousOn
    · exact (Real.continuous_exp.sub continuous_const).continuousOn
  deriv := by
    intro i hi x hx
    interval_cases i
    · show HasDerivAt (fun y => Real.exp y - y - 1) (Real.exp x - 1) x
      simpa using ((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).sub_const 1
    · show HasDerivAt (fun y => Real.exp y - 1) (Real.exp x) x
      exact (Real.hasDerivAt_exp x).sub_const 1
  zero := by
    intro i hi
    interval_cases i
    · show Real.exp 0 - 0 - 1 = 0
      simp
    · show Real.exp 0 - 1 = 0
      simp

/-- Denominator ladder for the order-2 model instance: `x²`, `2x`, `2`. -/
private noncomputable def sqLadder : DerivLadder 2 0 1 where
  f
    | 0 => fun x => x ^ 2
    | 1 => fun x => 2 * x
    | _ + 2 => fun _ => 2
  cont := by
    intro i hi
    interval_cases i
    · exact (continuous_pow 2).continuousOn
    · exact (continuous_const.mul continuous_id).continuousOn
  deriv := by
    intro i hi x hx
    interval_cases i
    · show HasDerivAt (fun y => y ^ 2) (2 * x) x
      simpa using hasDerivAt_pow 2 x
    · show HasDerivAt (fun y => 2 * y) (2 : ℝ) x
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  zero := by
    intro i hi
    interval_cases i
    · show (0 : ℝ) ^ 2 = 0
      simp
    · show 2 * (0 : ℝ) = 0
      simp

/-- Order-2 model instance: `(eᵗ − t − 1)/t² ∈ [1/2, e/2]` on `(0, 1)`.
Numerator and denominator vanish to order 2 at the wall `t = 0`; the
second-derivative ratio bounds `1 ≤ eˣ ≤ e` are the regular interval data. -/
theorem expm1_sub_self_div_sq_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (Real.exp t - t - 1) / t ^ 2 ∈ Icc (1 / 2 : ℝ) (Real.exp 1 / 2) := by
  have h := quotient_mem_of_derivLadder 2 (by omega) expm1SubLadder sqLadder
    (fun x _ => by
      show (0 : ℝ) < 2
      norm_num)
    (fun x hx => by
      show 1 / 2 * (2 : ℝ) ≤ Real.exp x
      have := Real.one_le_exp hx.1.le
      linarith)
    (fun x hx => by
      show Real.exp x ≤ Real.exp 1 / 2 * 2
      have := Real.exp_le_exp.mpr hx.2.le
      linarith)
    t ht
  exact h

end LeanCert.Analysis.WallQuotient
