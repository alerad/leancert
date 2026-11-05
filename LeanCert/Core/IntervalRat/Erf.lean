/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Arctan
import LeanCert.Core.IntervalRat.Derived
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rational Endpoint Intervals - Computable erf

Tight, computable enclosures of `Real.erf x = (2/√π) ∫₀ˣ exp(-t²) dt`.

For `u ≥ 0` the partial sums `Sₘ(u) = Σ_{k<m} (-u)^k/k!` of `exp(-u)` alternate
around it: `(-1)^m (exp(-u) - Sₘ(u)) ≥ 0`. (The derivative of this quantity is
the same quantity at `m - 1`, so it follows by induction and monotonicity.)
Substituting `u = t²` and integrating over `[0, x]` brackets `∫₀ˣ exp(-t²) dt`
between two exact rational polynomials in `x`. The factor `2/√π` is enclosed
from Machin's `π` and the verified square root, so every digit follows the
requested depth.

Enclosures on intervals use monotonicity and oddness. Endpoints are rounded
outward to a `2⁻⁶⁰` grid and clamped to `|x| ≤ 5` (where `1 - erf 5 < 2·10⁻¹²`),
which bounds the size of the rationals involved.
-/

namespace LeanCert.Core

namespace IntervalRat

open Finset

/-! ### Alternating bounds for `exp(-u)` -/

/-- Partial sum `Σ_{k<m} (-u)^k/k!` of `exp(-u)`. -/
noncomputable def expNegPartial (m : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range m, (-u) ^ k / (k.factorial : ℝ)

theorem hasDerivAt_expNegPartial_succ (m : ℕ) (u : ℝ) :
    HasDerivAt (expNegPartial (m + 1)) (-expNegPartial m u) u := by
  induction m with
  | zero =>
    have : expNegPartial 1 = fun _ => 1 := by
      funext v
      simp [expNegPartial]
    rw [this]
    simpa [expNegPartial] using hasDerivAt_const u (1 : ℝ)
  | succ m ih =>
    have hsplit : expNegPartial (m + 2) =
        fun v => expNegPartial (m + 1) v + (-v) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      funext v
      simp [expNegPartial, sum_range_succ]
    rw [hsplit]
    have hpow : HasDerivAt (fun v : ℝ => (-v) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (-u) ^ m * (-1)) u := by
      have h := ((hasDerivAt_id u).neg).pow (m + 1)
      simp only [Nat.add_sub_cancel] at h
      exact h
    have hterm := hpow.div_const ((m + 1).factorial : ℝ)
    convert ih.add hterm using 1
    simp only [expNegPartial, sum_range_succ]
    rw [Nat.factorial_succ]
    push_cast
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- `(-1)^m (exp(-u) - Sₘ(u)) ≥ 0` for `u ≥ 0`. -/
theorem expNeg_alternating (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (-1 : ℝ) ^ m * (Real.exp (-u) - expNegPartial m u) := by
  induction m generalizing u with
  | zero =>
    simp only [pow_zero, one_mul, expNegPartial, range_zero, sum_empty, sub_zero]
    exact (Real.exp_pos _).le
  | succ m ih =>
    set g : ℝ → ℝ := fun v => (-1 : ℝ) ^ (m + 1) * (Real.exp (-v) - expNegPartial (m + 1) v)
      with hg
    have hderiv : ∀ v, HasDerivAt g ((-1 : ℝ) ^ m * (Real.exp (-v) - expNegPartial m v)) v := by
      intro v
      have hexp : HasDerivAt (fun w => Real.exp (-w)) (Real.exp (-v) * (-1)) v := by
        simpa using (hasDerivAt_neg v).exp
      have h := (hexp.sub (hasDerivAt_expNegPartial_succ m v)).const_mul ((-1 : ℝ) ^ (m + 1))
      convert h using 1
      ring
    have hmono : MonotoneOn g (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (fun v _ => (hderiv v).continuousAt.continuousWithinAt)
      · exact (fun v _ => (hderiv v).differentiableAt.differentiableWithinAt)
      · intro v hv
        rw [interior_Ici] at hv
        rw [(hderiv v).deriv]
        exact ih (le_of_lt hv)
    have h0 : g 0 = 0 := by
      simp [hg, expNegPartial, sum_range_succ']
    have := hmono (Set.mem_Ici.mpr le_rfl) hu hu
    rw [h0] at this
    exact this

theorem expNegPartial_odd_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    expNegPartial (2 * n + 2) u ≤ Real.exp (-u) := by
  have h := expNeg_alternating (2 * n + 2) hu
  have hs : ((-1 : ℝ)) ^ (2 * n + 2) = 1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hs, one_mul] at h
  linarith

theorem le_expNegPartial_even {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Real.exp (-u) ≤ expNegPartial (2 * n + 1) u := by
  have h := expNeg_alternating (2 * n + 1) hu
  have hs : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hs] at h
  linarith

/-! ### Integrating the bounds -/

/-- Exact partial sum `Σ_{k<m} (-1)^k q^(2k+1) / (k! (2k+1))` over `ℚ`. -/
def erfPartial (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => erfPartial q k + (-1) ^ k * q ^ (2 * k + 1) / ((k.factorial : ℚ) * (2 * k + 1))

theorem integral_expNegPartial_sq (x : ℝ) (m : ℕ) :
    ∫ t in (0 : ℝ)..x, expNegPartial m (t ^ 2) =
      ∑ k ∈ range m, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((k.factorial : ℝ) * (2 * k + 1)) := by
  have hterm : ∀ k : ℕ, (fun t : ℝ => (-(t ^ 2)) ^ k / (k.factorial : ℝ)) =
      fun t => ((-1 : ℝ) ^ k / (k.factorial : ℝ)) * t ^ (2 * k) := by
    intro k
    funext t
    rw [neg_pow, ← pow_mul]
    ring
  unfold expNegPartial
  rw [intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl ?_
    intro k _
    rw [hterm k, intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have h2 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · intro k _
    rw [hterm k]
    exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _

theorem erfPartial_cast (q : ℚ) (m : ℕ) :
    ((erfPartial q m : ℚ) : ℝ) =
      ∑ k ∈ range m, (-1 : ℝ) ^ k * (q : ℝ) ^ (2 * k + 1) / ((k.factorial : ℝ) * (2 * k + 1)) := by
  induction m with
  | zero => simp [erfPartial]
  | succ k ih =>
    rw [sum_range_succ, ← ih, erfPartial]
    push_cast
    ring

/-- `∫₀^q exp(-t²) dt` lies between consecutive partial sums, for `q ≥ 0`. -/
theorem gaussInt_mem {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    ((erfPartial q (2 * n + 2) : ℚ) : ℝ) ≤ ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2)) ∧
      ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2)) ≤ ((erfPartial q (2 * n + 1) : ℚ) : ℝ) := by
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hcontP : ∀ m, Continuous fun t : ℝ => expNegPartial m (t ^ 2) := by
    intro m
    unfold expNegPartial
    fun_prop
  have hcontE : Continuous fun t : ℝ => Real.exp (-(t ^ 2)) := by fun_prop
  rw [erfPartial_cast, erfPartial_cast, ← integral_expNegPartial_sq, ← integral_expNegPartial_sq]
  constructor
  · apply intervalIntegral.integral_mono_on hq' ((hcontP _).intervalIntegrable _ _)
      (hcontE.intervalIntegrable _ _)
    intro t _
    exact expNegPartial_odd_le (sq_nonneg t) n
  · apply intervalIntegral.integral_mono_on hq' (hcontE.intervalIntegrable _ _)
      ((hcontP _).intervalIntegrable _ _)
    intro t _
    exact le_expNegPartial_even (sq_nonneg t) n

/-! ### The factor `2/√π` -/

/-- Enclosure of `2/√π` from Machin's `π/4` and a 64-bit square root. -/
def twoDivSqrtPiComputable (n : ℕ) : IntervalRat :=
  let S := sqrtIntervalTightPrec (scale 4 (piQuarterComputable n)) 64
  if 0 < S.lo then scale 2 (invPos S) else two_div_sqrt_pi

theorem mem_twoDivSqrtPiComputable (n : ℕ) :
    2 / Real.sqrt Real.pi ∈ twoDivSqrtPiComputable n := by
  unfold twoDivSqrtPiComputable
  dsimp only
  split_ifs with h
  · have hpi : Real.pi ∈ scale 4 (piQuarterComputable n) := by
      have := mem_scale 4 (mem_piQuarterComputable n)
      push_cast at this
      rwa [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] at this
    have hs := mem_sqrtIntervalTightPrec' hpi 64
    have hinv := mem_scale 2 (mem_invPos hs h)
    push_cast at hinv
    rwa [← div_eq_mul_inv] at hinv
  · exact two_div_sqrt_pi_mem

/-! ### Real.erf: oddness and monotonicity -/

theorem erf_neg (x : ℝ) : Real.erf (-x) = -Real.erf x := by
  unfold Real.erf
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x)
    (fun t => Real.exp (-(t ^ 2)))
  simp only [neg_sq, neg_zero] at h
  have h2 : (∫ t in (0 : ℝ)..-x, Real.exp (-(t ^ 2))) =
      -∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    rw [intervalIntegral.integral_symm (-x) 0, ← h]
  rw [h2]
  ring

theorem erf_le_erf {x y : ℝ} (h : x ≤ y) : Real.erf x ≤ Real.erf y := by
  unfold Real.erf
  have hcont : Continuous fun t : ℝ => Real.exp (-(t ^ 2)) := by fun_prop
  have hfac : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi := by positivity
  apply mul_le_mul_of_nonneg_left _ hfac
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 x)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) x y)
  have hnn : 0 ≤ ∫ t in x..y, Real.exp (-(t ^ 2)) :=
    intervalIntegral.integral_nonneg h (fun t _ => (Real.exp_pos _).le)
  linarith

/-! ### Point and interval enclosures -/

/-- Point enclosure of `erf q` for `0 ≤ q`. Uses `2m + 1` and `2m + 2` series terms
    with `m = n + 3⌈q²⌉`, enough for the tail to decay geometrically. -/
def erfNonneg (q : ℚ) (n : ℕ) : IntervalRat :=
  let m := n + 3 * (q * q).ceil.toNat
  let lo := erfPartial q (2 * m + 2)
  let hi := erfPartial q (2 * m + 1)
  mul (twoDivSqrtPiComputable n) ⟨lo, max lo hi, le_max_left _ _⟩

theorem mem_erfNonneg {q : ℚ} (hq : 0 ≤ q) (n : ℕ) : Real.erf q ∈ erfNonneg q n := by
  unfold erfNonneg
  dsimp only
  set m := n + 3 * (q * q).ceil.toNat
  have hb := gaussInt_mem hq m
  apply mem_mul (mem_twoDivSqrtPiComputable n)
  simp only [mem_def]
  push_cast
  exact ⟨hb.1, le_trans hb.2 (le_max_right _ _)⟩

/-- Point enclosure of `erf q` for any rational `q`, by oddness. -/
def erfPoint (q : ℚ) (n : ℕ) : IntervalRat :=
  if 0 ≤ q then erfNonneg q n else neg (erfNonneg (-q) n)

theorem mem_erfPoint (q : ℚ) (n : ℕ) : Real.erf q ∈ erfPoint q n := by
  unfold erfPoint
  split_ifs with h
  · exact mem_erfNonneg h n
  · have hm := mem_neg (mem_erfNonneg (by linarith [lt_of_not_ge h] : 0 ≤ -q) n)
    push_cast at hm
    rwa [erf_neg, neg_neg] at hm

/-- Endpoint clamp: `1 - erf 5 < 2·10⁻¹²`. -/
def erfClampBound : ℚ := 5

/-- Round down to the `2⁻⁶⁰` grid. -/
def roundDown60 (q : ℚ) : ℚ := (⌊q * 2 ^ 60⌋ : ℚ) / 2 ^ 60

/-- Round up to the `2⁻⁶⁰` grid. -/
def roundUp60 (q : ℚ) : ℚ := (⌈q * 2 ^ 60⌉ : ℚ) / 2 ^ 60

theorem roundDown60_le (q : ℚ) : roundDown60 q ≤ q := by
  unfold roundDown60
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem le_roundUp60 (q : ℚ) : q ≤ roundUp60 q := by
  unfold roundUp60
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- Lower bound for `erf` on `[q, ∞)`. -/
def erfLowerAt (q : ℚ) (n : ℕ) : ℚ :=
  if q < -erfClampBound then -1 else (erfPoint (roundDown60 (min q erfClampBound)) n).lo

/-- Upper bound for `erf` on `(-∞, q]`. -/
def erfUpperAt (q : ℚ) (n : ℕ) : ℚ :=
  if erfClampBound < q then 1 else (erfPoint (roundUp60 (max q (-erfClampBound))) n).hi

theorem erfLowerAt_le {x : ℝ} {q : ℚ} (hqx : (q : ℝ) ≤ x) (n : ℕ) :
    ((erfLowerAt q n : ℚ) : ℝ) ≤ Real.erf x := by
  unfold erfLowerAt
  split_ifs
  · push_cast
    exact Real.neg_one_le_erf x
  · set c := roundDown60 (min q erfClampBound)
    have hc := ((mem_def _ _).mp (mem_erfPoint c n)).1
    have hle : (c : ℝ) ≤ x := by
      have h1 : c ≤ q := le_trans (roundDown60_le _) (min_le_left _ _)
      exact le_trans (by exact_mod_cast h1) hqx
    exact le_trans hc (erf_le_erf hle)

theorem le_erfUpperAt {x : ℝ} {q : ℚ} (hxq : x ≤ (q : ℝ)) (n : ℕ) :
    Real.erf x ≤ ((erfUpperAt q n : ℚ) : ℝ) := by
  unfold erfUpperAt
  split_ifs
  · push_cast
    exact Real.erf_le_one x
  · set c := roundUp60 (max q (-erfClampBound))
    have hc := ((mem_def _ _).mp (mem_erfPoint c n)).2
    have hle : x ≤ (c : ℝ) := by
      have h1 : q ≤ c := le_trans (le_max_left _ _) (le_roundUp60 _)
      exact le_trans hxq (by exact_mod_cast h1)
    exact le_trans (erf_le_erf hle) hc

/-- Interval enclosure of `erf` on `I` by monotonicity, with depth `n`. -/
def erfTight (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let lo := erfLowerAt I.lo n
  ⟨lo, max lo (erfUpperAt I.hi n), le_max_left _ _⟩

theorem mem_erfTight {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.erf x ∈ erfTight I n := by
  have hx' := (mem_def _ _).mp hx
  simp only [erfTight, mem_def]
  push_cast
  exact ⟨erfLowerAt_le hx'.1 n, le_trans (le_erfUpperAt hx'.2 n) (le_max_right _ _)⟩

end IntervalRat

end LeanCert.Core
