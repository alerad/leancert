/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Pentagon Lucas Sequence

We define a Lucas-like sequence arising from the regular pentagon:

  `T n = (2 cos(π/10))ⁿ + (2 sin(π/10))ⁿ`

where the roots α = 2 cos(π/10) and β = 2 sin(π/10) satisfy the characteristic
quadratic x² - (α + β)x + αβ = 0, with:

  αβ = 2 sin(π/5)   (by the double-angle identity)

## Main results

* `pentagonSeq` — the sequence definition
* `pentagonSeq_zero` — T₀ = 2
* `pentagonSeq_two` — T₂ = 4  (Pythagorean identity)
* `pentagonSeq_recurrence` — T_{n+2} = (α + β) T_{n+1} - αβ · T_n
* `cos_pi_div_five_eq_goldenRatio_div_two` — cos(π/5) = φ/2
* `two_sin_pi_div_ten_eq_inv_goldenRatio` — 2 sin(π/10) = φ⁻¹ = -ψ
* `pentagonSeq_product` — αβ = 2 sin(π/5)

## References

The sequence bridges the golden ratio φ and pentagon trigonometry through
the exact identity cos(π/5) = φ/2, equivalently sin(π/10) = φ⁻¹/2 = -ψ/2.
-/

noncomputable section

open Real

namespace LeanCert.Engine.PentagonLucas

/-! ### Pentagon trig constants -/

/-- The larger root: α = 2 cos(π/10). -/
def α : ℝ := 2 * cos (π / 10)

/-- The smaller root: β = 2 sin(π/10). -/
def β : ℝ := 2 * sin (π / 10)

/-! ### Sequence definition -/

/-- The pentagon Lucas sequence: `T n = αⁿ + βⁿ`. -/
def pentagonSeq (n : ℕ) : ℝ := α ^ n + β ^ n

/-! ### Base cases -/

@[simp]
theorem pentagonSeq_zero : pentagonSeq 0 = 2 := by
  unfold pentagonSeq; norm_num

@[simp]
theorem pentagonSeq_one : pentagonSeq 1 = α + β := by
  unfold pentagonSeq; ring

/-- T₂ = 4: this is the Pythagorean identity in disguise, since
    (2 cos θ)² + (2 sin θ)² = 4(cos² θ + sin² θ) = 4. -/
theorem pentagonSeq_two : pentagonSeq 2 = 4 := by
  unfold pentagonSeq α β
  have h : (2 * cos (π / 10)) ^ 2 + (2 * sin (π / 10)) ^ 2
      = 4 * (cos (π / 10) ^ 2 + sin (π / 10) ^ 2) := by ring
  rw [h, cos_sq_add_sin_sq]
  norm_num

/-! ### Product of roots: αβ = 2 sin(π/5) -/

/-- The product of the roots equals 2 sin(π/5), by the double-angle identity
    2 sin θ cos θ = sin(2θ). -/
theorem pentagonSeq_product : α * β = 2 * sin (π / 5) := by
  unfold α β
  have h : 2 * cos (π / 10) * (2 * sin (π / 10))
      = 2 * (2 * sin (π / 10) * cos (π / 10)) := by ring
  rw [h, ← sin_two_mul]
  ring_nf

/-! ### Recurrence relation -/

/-- The fundamental recurrence: T_{n+2} = (α + β) · T_{n+1} - αβ · T_n.

This follows from α and β being roots of x² - (α+β)x + αβ = 0,
i.e., α² = (α+β)α - αβ and β² = (α+β)β - αβ. -/
theorem pentagonSeq_recurrence (n : ℕ) :
    pentagonSeq (n + 2) = (α + β) * pentagonSeq (n + 1) - α * β * pentagonSeq n := by
  simp only [pentagonSeq]
  ring

/-! ### Golden ratio bridge -/

/-- cos(π/5) = φ/2, linking the golden ratio to pentagon geometry.
    This follows directly from Mathlib's `cos_pi_div_five`. -/
theorem cos_pi_div_five_eq_goldenRatio_div_two :
    cos (π / 5) = goldenRatio / 2 := by
  rw [cos_pi_div_five]
  unfold goldenRatio
  ring

/-- sin(π/10) = (√5 - 1) / 4.
    We derive this from cos(π/5) = (1 + √5)/4 via cos(2θ) = 1 - 2sin²(θ). -/
theorem sin_pi_div_ten :
    sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
  -- Use cos(π/5) = 1 - 2sin²(π/10)
  have hcos : cos (π / 5) = 1 - 2 * sin (π / 10) ^ 2 := by
    have h : π / 5 = 2 * (π / 10) := by ring
    rw [h, cos_two_mul]
    have := sin_sq (π / 10)
    linarith
  rw [cos_pi_div_five] at hcos
  -- sin(π/10) ≥ 0
  have hsin_nn : 0 ≤ sin (π / 10) := by
    apply sin_nonneg_of_nonneg_of_le_pi
    · linarith [pi_pos]
    · linarith [pi_pos]
  -- sin²(π/10) = (3 - √5)/8
  have hsq : sin (π / 10) ^ 2 = (3 - Real.sqrt 5) / 8 := by linarith
  -- target² = (3 - √5)/8
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have htarget_sq : ((Real.sqrt 5 - 1) / 4) ^ 2 = (3 - Real.sqrt 5) / 8 := by nlinarith
  -- target ≥ 0
  have htarget_nn : 0 ≤ (Real.sqrt 5 - 1) / 4 := by
    apply div_nonneg _ (by norm_num)
    have : 1 ≤ Real.sqrt 5 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  -- Both nonneg with same square → equal
  nlinarith [sq_nonneg (sin (π / 10) - (Real.sqrt 5 - 1) / 4)]

/-- The golden ratio bridge: 2 sin(π/10) = φ⁻¹ = -ψ.
    This means β = 1/φ, connecting the pentagon sequence root to the golden ratio. -/
theorem two_sin_pi_div_ten_eq_inv_goldenRatio :
    2 * sin (π / 10) = goldenRatio⁻¹ := by
  rw [sin_pi_div_ten, inv_goldenRatio]
  unfold goldenConj
  ring

/-- β = φ⁻¹: the smaller root of the pentagon sequence is the reciprocal
    of the golden ratio. -/
theorem β_eq_inv_goldenRatio : β = goldenRatio⁻¹ := by
  exact two_sin_pi_div_ten_eq_inv_goldenRatio

/-- α expressed in terms of the golden ratio. -/
theorem α_eq : α = 2 * cos (π / 10) := rfl

/-! ### Recurrence with golden ratio -/

/-- The recurrence in terms of concrete constants:
    T_{n+2} = (α + β) · T_{n+1} - 2sin(π/5) · T_n -/
theorem pentagonSeq_recurrence' (n : ℕ) :
    pentagonSeq (n + 2) =
      (α + β) * pentagonSeq (n + 1) - 2 * sin (π / 5) * pentagonSeq n := by
  rw [← pentagonSeq_product]
  exact pentagonSeq_recurrence n

/-! ### Asymptotic dominance -/

/-- β < 1, so βⁿ → 0. The sequence is asymptotically dominated by αⁿ. -/
theorem β_lt_one : β < 1 := by
  rw [β_eq_inv_goldenRatio]
  exact (inv_lt_one₀ goldenRatio_pos).mpr one_lt_goldenRatio

theorem β_pos : 0 < β := by
  rw [β_eq_inv_goldenRatio]
  exact inv_pos.mpr goldenRatio_pos

/-! ### The characteristic quadratic -/

/-- α and β are the two roots of x² - (α+β)x + αβ = 0. -/
theorem α_is_root_char_poly :
    α ^ 2 - (α + β) * α + α * β = 0 := by ring

theorem β_is_root_char_poly :
    β ^ 2 - (α + β) * β + α * β = 0 := by ring

/-! ### Separation: Binet-like formula -/

/-- The anti-symmetric companion: U_n = αⁿ - βⁿ. -/
def pentagonSeqU (n : ℕ) : ℝ := α ^ n - β ^ n

theorem pentagonSeqU_zero : pentagonSeqU 0 = 0 := by
  unfold pentagonSeqU; norm_num

theorem pentagonSeqU_one : pentagonSeqU 1 = α - β := by
  unfold pentagonSeqU; ring

theorem pentagonSeqU_recurrence (n : ℕ) :
    pentagonSeqU (n + 2) = (α + β) * pentagonSeqU (n + 1) - α * β * pentagonSeqU n := by
  simp only [pentagonSeqU]
  ring

/-- Recovery: αⁿ = (T_n + U_n) / 2 -/
theorem alpha_pow_eq (n : ℕ) :
    α ^ n = (pentagonSeq n + pentagonSeqU n) / 2 := by
  unfold pentagonSeq pentagonSeqU; ring

/-- Recovery: βⁿ = (T_n - U_n) / 2 -/
theorem beta_pow_eq (n : ℕ) :
    β ^ n = (pentagonSeq n - pentagonSeqU n) / 2 := by
  unfold pentagonSeq pentagonSeqU; ring

end LeanCert.Engine.PentagonLucas
