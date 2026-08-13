/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicLimit
import LeanCert.Validity.RelativeCompleteness

namespace LeanCert.Test.DyadicLimit

open Filter LeanCert.Core LeanCert.Validity

private def unit : IntervalDyadic :=
  ⟨LeanCert.Core.Dyadic.ofInt 0, LeanCert.Core.Dyadic.ofInt 1,
    by norm_num [LeanCert.Core.Dyadic.toRat_ofInt]⟩

private def alternating : InfiniteDyadicPath := fun n => n % 2 == 0

example : alternating.finitePrefix 4 = [true, false, true, false] := by native_decide

example : (alternating.cell unit 4).lo.toRat = 5 / 8 := by native_decide
example : (alternating.cell unit 4).hi.toRat = 11 / 16 := by native_decide

example (bits : InfiniteDyadicPath) (depth : Nat) :
    (bits.cell unit depth).width.toRat = (1 / 2 : ℚ) ^ depth := by
  rw [bits.cell_width_toRat]
  have hwidth : unit.width.toRat = 1 := by native_decide
  rw [hwidth, one_mul]

example (bits : InfiniteDyadicPath) :
    ∃! x : ℝ, ∀ depth, x ∈ bits.cell unit depth :=
  bits.exists_unique_limit unit

example (bits : InfiniteDyadicPath) (points : Nat → ℝ)
    (hpoints : ∀ depth, points depth ∈ bits.cell unit depth) :
    Tendsto points atTop (nhds (bits.decode unit)) :=
  bits.tendsto_decode_of_mem_cell unit points hpoints

private noncomputable def geometricSchedule : NumericalRefinementSchedule where
  spatial n := (1 / 2 : ℝ) ^ n
  rounding n := (1 / 4 : ℝ) ^ n
  analytic n := (1 / 8 : ℝ) ^ n
  spatial_nonneg := fun n => pow_nonneg (by norm_num) n
  rounding_nonneg := fun n => pow_nonneg (by norm_num) n
  analytic_nonneg := fun n => pow_nonneg (by norm_num) n
  spatial_tendsto_zero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rounding_tendsto_zero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  analytic_tendsto_zero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

example : ∀ᶠ n in atTop, geometricSchedule.totalError n < (1 / 100 : ℝ) :=
  geometricSchedule.eventually_totalError_lt (by norm_num)

example (upper : Nat → ℝ)
    (hupper : ∀ n, upper n ≤ 0 + geometricSchedule.totalError n) :
    ∃ n, upper n < 1 / 100 := by
  apply geometricSchedule.exists_certifying_upper upper (margin := 1 / 100)
    (trueBound := 0) (target := 1 / 100)
  · norm_num
  · norm_num
  · exact hupper

example (lower : Nat → ℝ)
    (hlower : ∀ n, 1 - geometricSchedule.totalError n ≤ lower n) :
    ∃ n, 99 / 100 < lower n := by
  apply geometricSchedule.exists_certifying_lower lower (margin := 1 / 100)
    (trueBound := 1) (target := 99 / 100)
  · norm_num
  · norm_num
  · exact hlower

end LeanCert.Test.DyadicLimit
