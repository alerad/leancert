/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.TrigReduced
import LeanCert.Core.IntervalRat.Transcendental
import LeanCert.Core.IntervalRealEndpoints
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Rational Endpoint Intervals - Derived transcendental enclosures

Tight, computable enclosures for functions that reduce to already-enclosed ones:

* `tanh x = 1 - 2 / (exp (2x) + 1)`, monotone in `exp (2x)`;
* `sinc` is even, so it is enclosed on `|x| ∈ [a, b]`: by the Taylor bound
  `|sin y - (y - y³/6)| ≤ y⁵/100` on `[0, 1]`, and by `sin y · y⁻¹` on `[1, ∞)`;
* `arsinh x = log (x + √(1 + x²))` for `x ≥ 0`, extended by oddness and
  enclosed on intervals by monotonicity.

All enclosures fall back to sound global bounds when an intermediate enclosure
is too wide to use (for instance a non-positive `log` argument).
-/

namespace LeanCert.Core

namespace IntervalRat

/-! ### tanh -/

theorem tanh_eq_one_sub_two_div (x : ℝ) : Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
  have hx := Real.exp_pos x
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg,
    show 2 * x = x + x by ring, Real.exp_add]
  field_simp
  ring

private theorem one_sub_two_div_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 - 2 / (a + 1) ≤ 1 - 2 / (b + 1) := by
  have : 2 / (b + 1) ≤ 2 / (a + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

/-- Lower tanh bound from an enclosure `E` of `exp (2x)`. -/
def tanhLoOf (E : IntervalRat) : ℚ := if 0 < E.lo then 1 - 2 / (E.lo + 1) else -1

/-- Upper tanh bound from an enclosure `E` of `exp (2x)`. -/
def tanhHiOf (E : IntervalRat) : ℚ := if 0 < E.hi then 1 - 2 / (E.hi + 1) else 1

/-- Enclosure of `tanh` on `I`, through `exp (2x)` with `n` Taylor terms. -/
def tanhViaExp (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let E := expComputable (scale 2 I) n
  ⟨tanhLoOf E, max (tanhLoOf E) (tanhHiOf E), le_max_left _ _⟩

theorem mem_tanhViaExp {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.tanh x ∈ tanhViaExp I n := by
  have hE := mem_expComputable (mem_scale 2 hx) n
  set E := expComputable (scale 2 I) n with hEdef
  have hE' := (mem_def _ _).mp hE
  push_cast at hE'
  have hexp_pos := Real.exp_pos (2 * x)
  have ht := tanh_eq_one_sub_two_div x
  have h2pos : 0 < 2 / (Real.exp (2 * x) + 1) := by positivity
  have h2lt : 2 / (Real.exp (2 * x) + 1) < 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hlo : ((tanhLoOf E : ℚ) : ℝ) ≤ Real.tanh x := by
    unfold tanhLoOf
    split_ifs with h
    · have h' : (0 : ℝ) < E.lo := by exact_mod_cast h
      push_cast
      rw [ht]
      exact one_sub_two_div_mono h' hE'.1
    · push_cast
      rw [ht]
      linarith
  have hhi : Real.tanh x ≤ ((tanhHiOf E : ℚ) : ℝ) := by
    unfold tanhHiOf
    split_ifs with h
    · push_cast
      rw [ht]
      exact one_sub_two_div_mono hexp_pos hE'.2
    · push_cast
      rw [ht]
      linarith
  simp only [mem_def, tanhViaExp, ← hEdef]
  refine ⟨hlo, le_trans hhi ?_⟩
  exact_mod_cast le_max_right _ _

theorem tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [tanh_eq_one_sub_two_div, tanh_eq_one_sub_two_div]
  exact one_sub_two_div_mono (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith))

/-- Point enclosure of `tanh c`. Negative points use oddness, so the exponential is
    evaluated at a positive argument, where its relative error is smaller. -/
def tanhPoint (c : ℚ) (n : ℕ) : IntervalRat :=
  if 0 ≤ c then tanhViaExp (singleton c) n else neg (tanhViaExp (singleton (-c)) n)

theorem mem_tanhPoint (c : ℚ) (n : ℕ) : Real.tanh c ∈ tanhPoint c n := by
  unfold tanhPoint
  split_ifs
  · exact mem_tanhViaExp (mem_singleton c) n
  · have h := mem_neg (mem_tanhViaExp (mem_singleton (-c)) n)
    push_cast at h
    rwa [Real.tanh_neg, neg_neg] at h

/-- Saturation threshold: `|tanh x| > 1 - 10⁻¹⁷` for `|x| ≥ 20`, so endpoints are
    clamped to `[-20, 20]` before evaluating `exp`, which keeps the rational
    exponentials small for huge inputs. -/
def tanhClampBound : ℚ := 20

/-- Lower bound for `tanh` on `[q, ∞)`. -/
def tanhLowerAt (q : ℚ) (n : ℕ) : ℚ :=
  if q < -tanhClampBound then -1 else (tanhPoint (min q tanhClampBound) n).lo

/-- Upper bound for `tanh` on `(-∞, q]`. -/
def tanhUpperAt (q : ℚ) (n : ℕ) : ℚ :=
  if tanhClampBound < q then 1 else (tanhPoint (max q (-tanhClampBound)) n).hi

theorem tanhLowerAt_le {x : ℝ} {q : ℚ} (hqx : (q : ℝ) ≤ x) (n : ℕ) :
    ((tanhLowerAt q n : ℚ) : ℝ) ≤ Real.tanh x := by
  unfold tanhLowerAt
  split_ifs
  · push_cast
    exact (Real.neg_one_lt_tanh x).le
  · have hc := ((mem_def _ _).mp (mem_tanhPoint (min q tanhClampBound) n)).1
    have hle : ((min q tanhClampBound : ℚ) : ℝ) ≤ x :=
      le_trans (by exact_mod_cast min_le_left q tanhClampBound) hqx
    exact le_trans hc (tanh_le_tanh hle)

theorem le_tanhUpperAt {x : ℝ} {q : ℚ} (hxq : x ≤ (q : ℝ)) (n : ℕ) :
    Real.tanh x ≤ ((tanhUpperAt q n : ℚ) : ℝ) := by
  unfold tanhUpperAt
  split_ifs
  · push_cast
    exact (Real.tanh_lt_one x).le
  · have hc := ((mem_def _ _).mp (mem_tanhPoint (max q (-tanhClampBound)) n)).2
    have hle : x ≤ ((max q (-tanhClampBound) : ℚ) : ℝ) :=
      le_trans hxq (by exact_mod_cast le_max_left q (-tanhClampBound))
    exact le_trans (tanh_le_tanh hle) hc

/-- Interval enclosure of `tanh` on `I` by monotonicity, with `n` Taylor terms for `exp`. -/
def tanhComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let lo := tanhLowerAt I.lo n
  ⟨lo, max lo (tanhUpperAt I.hi n), le_max_left _ _⟩

theorem mem_tanhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.tanh x ∈ tanhComputable I n := by
  have hx' := (mem_def _ _).mp hx
  simp only [tanhComputable, mem_def]
  push_cast
  exact ⟨tanhLowerAt_le hx'.1 n, le_trans (le_tanhUpperAt hx'.2 n) (le_max_right _ _)⟩

/-! ### sinc -/

/-- Enclosure of `sinc` on `[a, b] ⊆ [0, 1]` from the cubic Taylor bound for `sin`. -/
def sincSmall (a b : ℚ) : IntervalRat :=
  let lo := 1 - b ^ 2 / 6 - b ^ 4 / 100
  let hi := min 1 (1 - a ^ 2 / 6 + b ^ 4 / 100)
  ⟨lo, max lo hi, le_max_left _ _⟩

theorem mem_sincSmall {y : ℝ} {a b : ℚ} (ha : 0 ≤ a) (hay : (a : ℝ) ≤ y) (hyb : y ≤ b)
    (hb : b ≤ 1) : Real.sinc y ∈ sincSmall a b := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ 1 := by exact_mod_cast hb
  have hy0 : 0 ≤ y := le_trans ha' hay
  have hb0 : (0 : ℝ) ≤ b := le_trans hy0 hyb
  have hy2 : y ^ 2 ≤ (b : ℝ) ^ 2 := pow_le_pow_left₀ hy0 hyb 2
  have hy4 : y ^ 4 ≤ (b : ℝ) ^ 4 := pow_le_pow_left₀ hy0 hyb 4
  have ha2 : (a : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ ha' hay 2
  -- `|sinc y - (1 - y²/6)| ≤ y⁴/100`
  have hclose : |Real.sinc y - (1 - y ^ 2 / 6)| ≤ y ^ 4 / 100 := by
    rcases eq_or_lt_of_le hy0 with h0 | hpos
    · subst h0
      simp
    · have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; linarith
      have hs := Real.sin_bound hy1
      have key : Real.sinc y - (1 - y ^ 2 / 6) = (Real.sin y - (y - y ^ 3 / 6)) / y := by
        rw [Real.sinc_of_ne_zero hpos.ne']
        field_simp
      rw [key, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      rw [abs_of_nonneg hy0] at hs
      calc |Real.sin y - (y - y ^ 3 / 6)| ≤ y ^ 5 / 100 := hs
        _ = y ^ 4 / 100 * y := by ring
  have hc := abs_le.mp hclose
  have hle1 := Real.sinc_le_one y
  simp only [sincSmall, mem_def]
  push_cast
  constructor
  · linarith
  · refine le_trans ?_ (le_max_right _ _)
    apply le_min hle1
    linarith

/-- Reciprocal enclosure on a positive interval. -/
def invPos (J : IntervalRat) : IntervalRat :=
  if h : 0 < J.lo then
    ⟨1 / J.hi, 1 / J.lo, one_div_le_one_div_of_le h J.le⟩
  else
    ⟨0, 0, le_refl 0⟩

theorem mem_invPos {y : ℝ} {J : IntervalRat} (hy : y ∈ J) (hpos : 0 < J.lo) :
    y⁻¹ ∈ invPos J := by
  have hlo : (0 : ℝ) < J.lo := by exact_mod_cast hpos
  have hy' := (mem_def _ _).mp hy
  have hy0 : 0 < y := lt_of_lt_of_le hlo hy'.1
  simp only [invPos, hpos, ↓reduceDIte, mem_def]
  push_cast
  rw [← one_div]
  constructor
  · exact one_div_le_one_div_of_le hy0 hy'.2
  · exact one_div_le_one_div_of_le hlo hy'.1

/-- Clamp an enclosure of `sinc` to the global range `[-1, 1]`. -/
def clampUnit (P : IntervalRat) : IntervalRat :=
  let lo := max P.lo (-1)
  ⟨lo, max lo (min P.hi 1), le_max_left _ _⟩

theorem mem_clampUnit {z : ℝ} {P : IntervalRat} (hz : z ∈ P) (h1 : -1 ≤ z) (h2 : z ≤ 1) :
    z ∈ clampUnit P := by
  have hz' := (mem_def _ _).mp hz
  simp only [clampUnit, mem_def]
  push_cast
  exact ⟨max_le hz'.1 h1, le_trans (le_min hz'.2 h2) (le_max_right _ _)⟩

/-- Enclosure of `sinc` on a positive interval `J` as `sin y · y⁻¹`. -/
def sincLarge (J : IntervalRat) (n : ℕ) : IntervalRat :=
  clampUnit (mul (sinComputableReduced J n) (invPos J))

theorem mem_sincLarge {y : ℝ} {J : IntervalRat} (hy : y ∈ J) (hpos : 0 < J.lo) (n : ℕ) :
    Real.sinc y ∈ sincLarge J n := by
  have hlo : (0 : ℝ) < J.lo := by exact_mod_cast hpos
  have hy0 : 0 < y := lt_of_lt_of_le hlo ((mem_def _ _).mp hy).1
  have hprod := mem_mul (mem_sinComputableReduced hy n) (mem_invPos hy hpos)
  rw [← div_eq_mul_inv, ← Real.sinc_of_ne_zero hy0.ne'] at hprod
  exact mem_clampUnit hprod (Real.neg_one_le_sinc y) (Real.sinc_le_one y)

/-- Smallest absolute value on `I` (`0` if `I` contains `0`). -/
def absLo (I : IntervalRat) : ℚ :=
  if 0 < I.lo then I.lo else if I.hi < 0 then -I.hi else 0

/-- Largest absolute value on `I`. -/
def absHi (I : IntervalRat) : ℚ := max |I.lo| |I.hi|

theorem absLo_nonneg (I : IntervalRat) : 0 ≤ absLo I := by
  unfold absLo
  split_ifs with h1 h2 <;> linarith

theorem abs_mem_absLo_absHi {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    ((absLo I : ℚ) : ℝ) ≤ |x| ∧ |x| ≤ ((absHi I : ℚ) : ℝ) := by
  have hx' := (mem_def _ _).mp hx
  constructor
  · unfold absLo
    split_ifs with h1 h2
    · have : (0 : ℝ) < I.lo := by exact_mod_cast h1
      rw [abs_of_pos (by linarith)]
      exact hx'.1
    · have : (I.hi : ℝ) < 0 := by exact_mod_cast h2
      rw [abs_of_neg (by linarith)]
      push_cast
      linarith [hx'.2]
    · push_cast
      exact abs_nonneg x
  · unfold absHi
    push_cast
    exact abs_le_max_abs_abs hx'.1 hx'.2

theorem absLo_le_absHi (I : IntervalRat) : absLo I ≤ absHi I := by
  have h := abs_mem_absLo_absHi (mem_def (I.lo : ℝ) I |>.mpr ⟨le_refl _, by exact_mod_cast I.le⟩)
  exact_mod_cast h.1.trans h.2

/-- Intersection of two enclosures of the same value (kept nonempty structurally). -/
def meet (P Q : IntervalRat) : IntervalRat :=
  let lo := max P.lo Q.lo
  ⟨lo, max lo (min P.hi Q.hi), le_max_left _ _⟩

theorem mem_meet {z : ℝ} {P Q : IntervalRat} (hP : z ∈ P) (hQ : z ∈ Q) : z ∈ meet P Q := by
  have hP' := (mem_def _ _).mp hP
  have hQ' := (mem_def _ _).mp hQ
  simp only [meet, mem_def]
  push_cast
  exact ⟨max_le hP'.1 hQ'.1, le_trans (le_min hP'.2 hQ'.2) (le_max_right _ _)⟩

/-- Enclosure of `sinc` on `[a, b] ⊆ [0, 1]`: the Taylor bound, intersected with
    `sin y · y⁻¹` when `0 < a` (precise at points, where the Taylor bound is not). -/
def sincUnit (a b : ℚ) (hab : a ≤ b) (n : ℕ) : IntervalRat :=
  if 0 < a then meet (sincSmall a b) (sincLarge ⟨a, b, hab⟩ n) else sincSmall a b

theorem mem_sincUnit {y : ℝ} {a b : ℚ} (hab : a ≤ b) (ha : 0 ≤ a) (hay : (a : ℝ) ≤ y)
    (hyb : y ≤ b) (hb : b ≤ 1) (n : ℕ) : Real.sinc y ∈ sincUnit a b hab n := by
  unfold sincUnit
  split_ifs with hpos
  · exact mem_meet (mem_sincSmall ha hay hyb hb)
      (mem_sincLarge ((mem_def _ _).mpr ⟨hay, hyb⟩) hpos n)
  · exact mem_sincSmall ha hay hyb hb

/-- Interval enclosure of `sinc` on `I` with `n` Taylor terms for `sin`. -/
def sincComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let a := absLo I
  let b := absHi I
  if hb : b ≤ 1 then
    sincUnit a b (absLo_le_absHi I) n
  else if ha : 1 ≤ a then
    sincLarge ⟨a, b, absLo_le_absHi I⟩ n
  else
    hull (sincUnit a 1 (le_of_lt (lt_of_not_ge ha)) n)
      (sincLarge ⟨1, b, le_of_lt (lt_of_not_ge hb)⟩ n)

theorem mem_sincComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sinc x ∈ sincComputable I n := by
  have hsinc_abs : Real.sinc x = Real.sinc |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.sinc_neg]
  rw [hsinc_abs]
  obtain ⟨hlo, hhi⟩ := abs_mem_absLo_absHi hx
  have ha := absLo_nonneg I
  unfold sincComputable
  dsimp only
  split_ifs with hb h1
  · exact mem_sincUnit _ ha hlo hhi hb n
  · have hpos : (0 : ℚ) < absLo I := by linarith
    exact mem_sincLarge ((mem_def _ _).mpr ⟨hlo, hhi⟩) hpos n
  · rcases le_or_gt |x| 1 with hx1 | hx1
    · exact mem_hull_left (mem_sincUnit _ ha hlo (by exact_mod_cast hx1) le_rfl n)
    · apply mem_hull_right
      exact mem_sincLarge ((mem_def _ _).mpr ⟨by push_cast; exact hx1.le, hhi⟩)
        (by norm_num) n

/-! ### arsinh -/

/-- Point enclosure of `arsinh q` for `0 ≤ q` via `log (q + √(1 + q²))`, with a 64-bit
    square root. -/
def arsinhNonneg (q : ℚ) (n : ℕ) : IntervalRat :=
  let A := add (singleton q) (sqrtIntervalTightPrec (singleton (1 + q ^ 2)) 64)
  if 0 < A.lo then logComputable A n else ⟨0, max 0 q, le_max_left _ _⟩

theorem mem_arsinhNonneg {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    Real.arsinh q ∈ arsinhNonneg q n := by
  unfold arsinhNonneg
  dsimp only
  split_ifs with h
  · apply mem_logComputable _ h n
    have hs := mem_sqrtIntervalTightPrec' (mem_singleton (1 + q ^ 2)) 64
    have hA := mem_add (mem_singleton q) hs
    push_cast at hA
    exact hA
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    have h0 : 0 ≤ Real.arsinh q := Real.arsinh_nonneg_iff.mpr hq'
    have h1 : Real.arsinh q ≤ q := by
      have := IntervalReal.abs_arsinh_le_abs (q : ℝ)
      rw [abs_of_nonneg h0, abs_of_nonneg hq'] at this
      exact this
    simp only [mem_def]
    push_cast
    exact ⟨h0, le_trans h1 (le_max_right _ _)⟩

/-- Point enclosure of `arsinh q` for any rational `q`, by oddness. -/
def arsinhPoint (q : ℚ) (n : ℕ) : IntervalRat :=
  if 0 ≤ q then arsinhNonneg q n else neg (arsinhNonneg (-q) n)

theorem mem_arsinhPoint (q : ℚ) (n : ℕ) : Real.arsinh q ∈ arsinhPoint q n := by
  unfold arsinhPoint
  split_ifs with h
  · exact mem_arsinhNonneg h n
  · have hneg : 0 ≤ -q := by linarith [lt_of_not_ge h]
    have hm := mem_neg (mem_arsinhNonneg hneg n)
    push_cast at hm
    rwa [Real.arsinh_neg, neg_neg] at hm

/-- Interval enclosure of `arsinh` on `I` by monotonicity. -/
def arsinhComputable (I : IntervalRat) (n : ℕ := 20) : IntervalRat :=
  ⟨(arsinhPoint I.lo n).lo, (arsinhPoint I.hi n).hi, by
    have h1 := ((mem_def _ _).mp (mem_arsinhPoint I.lo n)).1
    have h2 := ((mem_def _ _).mp (mem_arsinhPoint I.hi n)).2
    have h3 : Real.arsinh (I.lo : ℝ) ≤ Real.arsinh (I.hi : ℝ) :=
      Real.arsinh_le_arsinh.mpr (by exact_mod_cast I.le)
    have : ((arsinhPoint I.lo n).lo : ℝ) ≤ (arsinhPoint I.hi n).hi := by linarith
    exact_mod_cast this⟩

theorem mem_arsinhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.arsinh x ∈ arsinhComputable I n := by
  rw [mem_def] at hx
  have h1 := ((mem_def _ _).mp (mem_arsinhPoint I.lo n)).1
  have h2 := ((mem_def _ _).mp (mem_arsinhPoint I.hi n)).2
  have hlo := Real.arsinh_le_arsinh.mpr hx.1
  have hhi := Real.arsinh_le_arsinh.mpr hx.2
  simp only [mem_def, arsinhComputable]
  constructor <;> linarith

end IntervalRat

end LeanCert.Core
