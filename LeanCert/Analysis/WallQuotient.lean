/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

end LeanCert.Analysis.WallQuotient
