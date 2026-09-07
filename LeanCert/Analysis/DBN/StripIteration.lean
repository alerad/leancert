import LeanCert.Analysis.DBN.StripShift

/-! Finite iteration of imaginary-shift contraction. No assertion about limits
or approximation of the heat integral is made here. -/
namespace LeanCert.Analysis.DBN
open Complex Polynomial ComplexConjugate

noncomputable def shiftPolynomial (a : ℝ) (p : ℂ[X]) : ℂ[X] :=
  C (1/2) * (p.comp (X + C ((a : ℂ)*I)) + p.comp (X + C (-(a : ℂ)*I)))

@[simp] theorem eval_shiftPolynomial (a : ℝ) (p : ℂ[X]) (z : ℂ) :
    (shiftPolynomial a p).eval z = shiftAverage p.eval a z := by
  simp [shiftPolynomial, shiftAverage, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

theorem shiftPolynomial_conj (a : ℝ) (p : ℂ[X])
    (hp : p.map (starRingEnd ℂ) = p) :
    (shiftPolynomial a p).map (starRingEnd ℂ) = shiftPolynomial a p := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp [shiftPolynomial, Polynomial.map_comp, hp, add_comm, htwo]

theorem shiftPolynomial_ne_zero (a : ℝ) (p : ℂ[X]) (hp : p ≠ 0) :
    shiftPolynomial a p ≠ 0 := by
  have hc (c : ℂ) : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff := by
    rw [leadingCoeff_comp (by simp)]
    simp
  have hd (c : ℂ) : (p.comp (X + C c)).natDegree = p.natDegree := by
    simp [natDegree_comp]
  have hn (c : ℂ) : p.comp (X + C c) ≠ 0 := comp_X_add_C_ne_zero_iff.mpr hp
  have he : (p.comp (X + C ((a : ℂ)*I))).degree =
      (p.comp (X + C (-(a : ℂ)*I))).degree := by
    rw [degree_eq_natDegree (hn _), degree_eq_natDegree (hn _), hd, hd]
  have hl : p.leadingCoeff + p.leadingCoeff ≠ 0 := by
    intro h
    have : p.leadingCoeff = 0 := by linear_combination h / 2
    exact (leadingCoeff_ne_zero.mpr hp) this
  have hs : p.comp (X + C ((a : ℂ)*I)) + p.comp (X + C (-(a : ℂ)*I)) ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [leadingCoeff_add_of_degree_eq he (by simpa only [hc] using hl), hc, hc]
    exact hl
  exact mul_ne_zero (by simp) hs

noncomputable def shiftPolynomialIter (a : ℝ) : ℕ → ℂ[X] → ℂ[X]
  | 0, p => p
  | n+1, p => shiftPolynomial a (shiftPolynomialIter a n p)

theorem shiftPolynomialIter_ne_zero (a : ℝ) (n : ℕ) (p : ℂ[X]) (hp : p ≠ 0) :
    shiftPolynomialIter a n p ≠ 0 := by
  induction n with
  | zero => exact hp
  | succ n ih => exact shiftPolynomial_ne_zero a _ ih

theorem shiftPolynomialIter_conj (a : ℝ) (n : ℕ) (p : ℂ[X])
    (hp : p.map (starRingEnd ℂ) = p) :
    (shiftPolynomialIter a n p).map (starRingEnd ℂ) = shiftPolynomialIter a n p := by
  induction n with
  | zero => exact hp
  | succ n ih => exact shiftPolynomial_conj a _ ih

/-- Each step subtracts exactly `a²` from the squared strip budget, until zero. -/
theorem shiftPolynomialIter_strip (p : ℂ[X]) (hp : p ≠ 0)
    (hc : p.map (starRingEnd ℂ) = p) {b a : ℝ} (ha : 0 < a)
    (hstrip : ∀ z : ℂ, p.eval z = 0 → z.im^2 ≤ b^2) (n : ℕ)
    {z : ℂ} (hz : (shiftPolynomialIter a n p).eval z = 0) :
    z.im^2 ≤ max (b^2 - (n : ℝ)*a^2) 0 := by
  induction n generalizing z with
  | zero => simpa using (hstrip z hz).trans (le_max_left (b^2) 0)
  | succ n ih =>
    let B := max (b^2 - (n : ℝ)*a^2) 0
    have hB : 0 ≤ B := le_max_right _ _
    have h := polynomial_shiftAverage_strip (shiftPolynomialIter a n p)
      (shiftPolynomialIter_ne_zero a n p hp) (shiftPolynomialIter_conj a n p hc)
      (b := Real.sqrt B) ha
      (by intro w hw; simpa only [Real.sq_sqrt hB] using ih hw)
      (by simpa only [shiftPolynomialIter, eval_shiftPolynomial] using hz)
    rw [Real.sq_sqrt hB] at h
    have he : max (B-a^2) 0 = max (b^2 - ((n+1 : ℕ) : ℝ)*a^2) 0 := by
      dsimp [B]
      rw [Nat.cast_add, Nat.cast_one]
      by_cases hb : 0 ≤ b^2 - (n : ℝ)*a^2
      · rw [max_eq_left hb]
        congr 1; ring
      · rw [max_eq_right (le_of_not_ge hb), max_eq_right (by nlinarith [sq_nonneg a]),
          max_eq_right (by nlinarith [sq_nonneg a])]
    rwa [he] at h

/-- A total squared shift budget covering the initial strip gives real zeros. -/
theorem shiftPolynomialIter_real (p : ℂ[X]) (hp : p ≠ 0)
    (hc : p.map (starRingEnd ℂ) = p) {b a : ℝ} (ha : 0 < a)
    (hstrip : ∀ z : ℂ, p.eval z = 0 → z.im^2 ≤ b^2) (n : ℕ)
    (hbudget : b^2 ≤ (n : ℝ)*a^2) {z : ℂ}
    (hz : (shiftPolynomialIter a n p).eval z = 0) : z.im = 0 := by
  have h := shiftPolynomialIter_strip p hp hc ha hstrip n hz
  rw [max_eq_right (sub_nonpos.mpr hbudget)] at h
  nlinarith [sq_nonneg z.im]

/-- The exact finite approximants proposed for time `1/2` have only real zeros. -/
theorem shiftPolynomialIter_unit_real (p : ℂ[X]) (hp : p ≠ 0)
    (hc : p.map (starRingEnd ℂ) = p)
    (hstrip : ∀ z : ℂ, p.eval z = 0 → z.im^2 ≤ 1)
    (n : ℕ) (hn : 0 < n) {z : ℂ}
    (hz : (shiftPolynomialIter (Real.sqrt (1/(n : ℝ))) n p).eval z = 0) : z.im = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply shiftPolynomialIter_real p hp hc (b := 1)
    (Real.sqrt_pos.mpr (one_div_pos.mpr hn')) (by simpa using hstrip) n ?_ hz
  rw [Real.sq_sqrt (by positivity)]
  simp [ne_of_gt hn']

end LeanCert.Analysis.DBN
