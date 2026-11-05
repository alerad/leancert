/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Rational Endpoint Intervals - Computable arctan

Tight, computable enclosures of `Real.arctan`.

The Maclaurin series `arctan x = Σ (-1)^k x^(2k+1)/(2k+1)` is evaluated exactly
over `ℚ`, and its tail is bounded by the geometric series
`|x|^(2m+1) / (1 - x²)`. Arguments are first reduced to `|r| ≤ 3/7`:

* `0 ≤ q ≤ 2/5`: the series at `q`;
* `2/5 < q ≤ 5/2`: `arctan q = π/4 + arctan ((q - 1)/(q + 1))`, with `|r| ≤ 3/7`;
* `5/2 < q`: `arctan q = π/2 - arctan q⁻¹`, with `q⁻¹ < 2/5`;
* `q < 0`: `arctan q = -arctan (-q)`.

`π/4` is itself enclosed through Machin's formula
`π/4 = 4 arctan (1/5) - arctan (1/239)`, so its precision follows the same
series depth and no rational bound on `π` is hard-coded.

Since `arctan` is monotone, an interval enclosure is the hull of the
lower endpoint enclosure at `I.lo` and the upper endpoint enclosure at `I.hi`.

## Main definitions

* `arctanSeries` - point enclosure for `|q| < 1`, sound for every `q`
* `piQuarterComputable` - `π/4` via Machin's formula
* `arctanPoint` - point enclosure with argument reduction
* `arctanComputable` - interval enclosure

## Main theorems

* `abs_arctan_sub_partial_le` - geometric tail bound for the series
* `mem_arctanPoint`, `mem_arctanComputable` - correctness
-/

namespace LeanCert.Core

namespace IntervalRat

/-! ### Series and tail bound -/

/-- Exact partial sum `Σ_{k<m} (-1)^k q^(2k+1)/(2k+1)` over `ℚ`. -/
def arctanPartial (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => arctanPartial q k + (-1) ^ k * q ^ (2 * k + 1) / (2 * k + 1)

theorem arctanPartial_cast (q : ℚ) (m : ℕ) :
    ((arctanPartial q m : ℚ) : ℝ) =
      ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * (q : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
  induction m with
  | zero => simp [arctanPartial]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, arctanPartial]
    push_cast
    ring

/-- Tail bound for the arctan series:
    `|arctan x - Σ_{k<m} (-1)^k x^(2k+1)/(2k+1)| ≤ |x|^(2m+1) / (1 - x²)` for `|x| < 1`. -/
theorem abs_arctan_sub_partial_le {x : ℝ} (hx : |x| < 1) (m : ℕ) :
    |Real.arctan x -
        ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)| ≤
      |x| ^ (2 * m + 1) / (1 - x ^ 2) := by
  set term : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
    with hterm
  have hseries : HasSum term (Real.arctan x) :=
    Real.hasSum_arctan (by simpa [Real.norm_eq_abs] using hx)
  have h_summable := hseries.summable
  have h_tail_summable : Summable fun k => term (k + m) :=
    (summable_nat_add_iff m).mpr h_summable
  have h_tail_eq : Real.arctan x - ∑ k ∈ Finset.range m, term k = ∑' k, term (k + m) := by
    have h_split := h_summable.sum_add_tsum_nat_add m
    have h_tsum_eq : ∑' i, term i = Real.arctan x := hseries.tsum_eq
    linarith
  rw [h_tail_eq]
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hx2 : x ^ 2 < 1 := by
    rw [← hsq]
    have h0 : 0 ≤ |x| := abs_nonneg x
    nlinarith
  let geo : ℕ → ℝ := fun k => |x| ^ (2 * m + 1) * (x ^ 2) ^ k
  have h_geo_summable : Summable geo :=
    (summable_geometric_of_lt_one (sq_nonneg x) hx2).mul_left _
  have h_term_bound : ∀ k, |term (k + m)| ≤ geo k := by
    intro k
    simp only [term, geo]
    rw [abs_div, abs_mul, abs_pow, abs_pow]
    simp only [abs_neg, abs_one, one_pow, one_mul]
    have h_pow_eq : |x| ^ (2 * (k + m) + 1) = |x| ^ (2 * m + 1) * (x ^ 2) ^ k := by
      rw [← hsq, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [h_pow_eq]
    have hd : (1 : ℝ) ≤ |((2 * (k + m) + 1 : ℕ) : ℝ)| := by
      rw [abs_of_nonneg (by positivity)]
      push_cast
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact div_le_self (by positivity) hd
  calc |∑' k, term (k + m)| ≤ ∑' k, |term (k + m)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm h_tail_summable.norm
    _ ≤ ∑' k, geo k := h_tail_summable.abs.tsum_le_tsum h_term_bound h_geo_summable
    _ = |x| ^ (2 * m + 1) / (1 - x ^ 2) := by
        simp only [geo]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg x) hx2]
        ring

/-! ### Point enclosures -/

/-- `arctan` is always in `[-2, 2]`, since `|arctan x| < π/2 < 2`. -/
theorem arctan_mem_Icc_neg_two_two (x : ℝ) : Real.arctan x ∈ Set.Icc (-2 : ℝ) 2 := by
  have h_lo := Real.neg_pi_div_two_lt_arctan x
  have h_hi := Real.arctan_lt_pi_div_two x
  have hpi := Real.pi_le_four
  constructor <;> linarith

/-- Point enclosure of `arctan q` by `m` series terms. Accurate for `|q| ≤ 3/7`;
    falls back to `[-2, 2]` when `q² ≥ 1`. Sound for every `q`. -/
def arctanSeries (q : ℚ) (m : ℕ) : IntervalRat :=
  if h : q * q < 1 then
    let S := arctanPartial q m
    let R := |q| ^ (2 * m + 1) / (1 - q * q)
    ⟨S - R, S + R, by
      have hR : 0 ≤ R := div_nonneg (pow_nonneg (abs_nonneg q) _) (by linarith)
      linarith⟩
  else
    ⟨-2, 2, by norm_num⟩

theorem mem_arctanSeries (q : ℚ) (m : ℕ) : Real.arctan q ∈ arctanSeries q m := by
  unfold arctanSeries
  split_ifs with h
  · have hqR : ((q : ℝ)) ^ 2 < 1 := by
      have : ((q * q : ℚ) : ℝ) < 1 := by exact_mod_cast h
      push_cast at this
      nlinarith
    have habs : |(q : ℝ)| < 1 := (sq_lt_one_iff_abs_lt_one _).mp hqR
    have hb := abs_le.mp (abs_arctan_sub_partial_le habs m)
    rw [← arctanPartial_cast] at hb
    simp only [mem_def]
    push_cast
    rw [show ((q : ℝ)) * q = (q : ℝ) ^ 2 by ring]
    constructor <;> linarith [hb.1, hb.2]
  · simp only [mem_def]
    push_cast
    exact arctan_mem_Icc_neg_two_two _

/-- Enclosure of `π/4` via Machin's formula `π/4 = 4 arctan (1/5) - arctan (1/239)`. -/
def piQuarterComputable (m : ℕ) : IntervalRat :=
  sub (scale 4 (arctanSeries (1 / 5) m)) (arctanSeries (1 / 239) m)

theorem mem_piQuarterComputable (m : ℕ) : Real.pi / 4 ∈ piQuarterComputable m := by
  rw [← Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  have h := mem_sub (mem_scale 4 (mem_arctanSeries (1 / 5) m)) (mem_arctanSeries (1 / 239) m)
  unfold piQuarterComputable
  convert h using 3 <;> norm_num

/-- Point enclosure of `arctan q` for `0 ≤ q`, with argument reduction to `|r| ≤ 3/7`. -/
def arctanNonneg (q : ℚ) (m : ℕ) : IntervalRat :=
  if q ≤ 2 / 5 then
    arctanSeries q m
  else if q ≤ 5 / 2 then
    add (piQuarterComputable m) (arctanSeries ((q - 1) / (q + 1)) m)
  else
    sub (scale 2 (piQuarterComputable m)) (arctanSeries q⁻¹ m)

/-- `arctan q = π/4 + arctan ((q - 1)/(q + 1))` for `q > -1`. -/
theorem arctan_eq_pi_div_four_add {q : ℝ} (hq : -1 < q) :
    Real.arctan q = Real.pi / 4 + Real.arctan ((q - 1) / (q + 1)) := by
  have hq1 : 0 < q + 1 := by linarith
  have hlt : 1 * ((q - 1) / (q + 1)) < 1 := by
    rw [one_mul, div_lt_one hq1]
    linarith
  rw [← Real.arctan_one, Real.arctan_add hlt]
  congr 1
  field_simp
  ring

theorem mem_arctanNonneg {q : ℚ} (hq : 0 ≤ q) (m : ℕ) :
    Real.arctan q ∈ arctanNonneg q m := by
  unfold arctanNonneg
  split_ifs with h1 h2
  · exact mem_arctanSeries q m
  · have hqR : (-1 : ℝ) < q := by
      have : (0 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    rw [arctan_eq_pi_div_four_add hqR]
    have hr := mem_arctanSeries ((q - 1) / (q + 1)) m
    push_cast at hr
    exact mem_add (mem_piQuarterComputable m) hr
  · have hpos : (0 : ℝ) < q := by
      have : (5 / 2 : ℚ) < q := lt_of_not_ge h2
      have : ((5 / 2 : ℚ) : ℝ) < q := by exact_mod_cast this
      push_cast at this
      linarith
    have hinv := Real.arctan_inv_of_pos hpos
    have heq : Real.arctan q = (2 : ℚ) * (Real.pi / 4) - Real.arctan ((q : ℝ)⁻¹) := by
      rw [hinv]
      push_cast
      ring
    rw [heq]
    have hr := mem_arctanSeries q⁻¹ m
    push_cast at hr
    exact mem_sub (mem_scale 2 (mem_piQuarterComputable m)) hr

/-- Point enclosure of `arctan q` for any rational `q`. -/
def arctanPoint (q : ℚ) (m : ℕ) : IntervalRat :=
  if 0 ≤ q then arctanNonneg q m else neg (arctanNonneg (-q) m)

theorem mem_arctanPoint (q : ℚ) (m : ℕ) : Real.arctan q ∈ arctanPoint q m := by
  unfold arctanPoint
  split_ifs with h
  · exact mem_arctanNonneg h m
  · have hneg : 0 ≤ -q := by linarith [lt_of_not_ge h]
    have hm := mem_neg (mem_arctanNonneg hneg m)
    push_cast at hm
    rwa [Real.arctan_neg, neg_neg] at hm

/-! ### Interval enclosure -/

/-- Interval enclosure of `arctan` on `I`, using monotonicity:
    `[lower(arctan I.lo), upper(arctan I.hi)]` with `m` series terms. -/
def arctanComputable (I : IntervalRat) (m : ℕ := 15) : IntervalRat :=
  ⟨(arctanPoint I.lo m).lo, (arctanPoint I.hi m).hi, by
    have h1 := ((mem_def _ _).mp (mem_arctanPoint I.lo m)).1
    have h2 := ((mem_def _ _).mp (mem_arctanPoint I.hi m)).2
    have h3 : Real.arctan (I.lo : ℝ) ≤ Real.arctan (I.hi : ℝ) :=
      Real.arctan_mono (by exact_mod_cast I.le)
    have : ((arctanPoint I.lo m).lo : ℝ) ≤ (arctanPoint I.hi m).hi := by linarith
    exact_mod_cast this⟩

theorem mem_arctanComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (m : ℕ) :
    Real.arctan x ∈ arctanComputable I m := by
  rw [mem_def] at hx
  have h1 := ((mem_def _ _).mp (mem_arctanPoint I.lo m)).1
  have h2 := ((mem_def _ _).mp (mem_arctanPoint I.hi m)).2
  have hlo := Real.arctan_mono hx.1
  have hhi := Real.arctan_mono hx.2
  simp only [mem_def, arctanComputable]
  constructor <;> linarith

end IntervalRat

end LeanCert.Core
