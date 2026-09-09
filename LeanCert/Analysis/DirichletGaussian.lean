/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.SeriesTail
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Group.Tannery
import LeanCert.Analysis.HadamardSupport.Analysis.Complex.ExpPoly
import Mathlib.Analysis.Polynomial.Basic

/-!
# Gaussian-damped Dirichlet series

Index n denotes the positive integer n+1. The damping parameter a is positive;
the DBN specialization is a = -t/4, for t < 0.
-/
namespace LeanCert.Analysis.DirichletGaussian
open Complex Filter Set
open scoped Topology

noncomputable def term (a : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp ((-a * (Real.log ((n : ℝ)+1))^2 : ℝ) -
    s * (Real.log ((n : ℝ)+1) : ℂ))

noncomputable def series (a : ℝ) (s : ℂ) : ℂ := ∑' n, term a s n
noncomputable def partialSum (a : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, term a s n

@[simp] theorem term_zero (a : ℝ) (s : ℂ) : term a s 0 = 1 := by simp [term]

theorem norm_term (a : ℝ) (s : ℂ) (n : ℕ) :
    ‖term a s n‖ = Real.exp (-a*(Real.log ((n : ℝ)+1))^2 -
      s.re*Real.log ((n : ℝ)+1)) := by
  simp only [term, Complex.norm_exp, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- A telescoping majorant with an explicit tail mass. -/
noncomputable def envelope (n : ℕ) : ℝ :=
  2 * (((n : ℝ)+1)⁻¹ - ((n : ℝ)+2)⁻¹)

theorem envelope_nonneg (n : ℕ) : 0 ≤ envelope n := by
  unfold envelope
  have h := one_div_le_one_div_of_le
    (by positivity : 0 < (n : ℝ)+1) (by linarith : (n : ℝ)+1 ≤ (n : ℝ)+2)
  simp only [one_div] at h
  positivity

theorem envelope_hasSum (N : ℕ) :
    HasSum (fun k => envelope (k+N)) (2/((N : ℝ)+1)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => envelope_nonneg _) _).mpr
  have he (m : ℕ) : (∑ k ∈ Finset.range m, envelope (k+N)) =
      2 * (((N : ℝ)+1)⁻¹ - ((m : ℝ)+(N : ℝ)+1)⁻¹) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [envelope, Nat.cast_add, Nat.cast_one]
      ring
  simp only [he]
  have hi : Tendsto (fun m : ℕ => ((m : ℝ)+(N : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (by simpa [add_assoc] using
        tendsto_atTop_add_const_right atTop ((N : ℝ)+1) tendsto_natCast_atTop_atTop)
  simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_const_nhds.sub hi)

theorem inv_sq_le_envelope (n : ℕ) : ((n : ℝ)+1)⁻¹^2 ≤ envelope n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have he : envelope n = 2 / (((n : ℝ)+1)*((n : ℝ)+2)) := by
    unfold envelope
    field_simp
    ring
  rw [he, inv_pow, ← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Completing the square gives a summable bound, uniformly on a half-plane. -/
theorem norm_term_le {a R : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : -R ≤ s.re) (n : ℕ) :
    ‖term a s n‖ ≤ Real.exp ((R+2)^2/(4*a)) * envelope n := by
  let L := Real.log ((n : ℝ)+1)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hsq : -a*L^2 - s.re*L ≤ (R+2)^2/(4*a) - 2*L := by
    have h := sq_nonneg (2*a*L-(R+2))
    have hd : 4*a*((R+2)^2/(4*a)) = (R+2)^2 := by field_simp
    nlinarith [mul_nonneg (show 0 ≤ s.re+R by linarith) hL]
  have he : Real.exp (-2*L) = ((n : ℝ)+1)⁻¹^2 := by
    rw [show -2*L = -(2*L) by ring, Real.exp_neg, show 2*L = L+L by ring, Real.exp_add,
      Real.exp_log (by positivity), mul_inv_rev]
    ring
  rw [norm_term]
  calc
    Real.exp (-a*L^2-s.re*L) ≤ Real.exp ((R+2)^2/(4*a)-2*L) :=
      Real.exp_le_exp.mpr hsq
    _ = Real.exp ((R+2)^2/(4*a))*((n : ℝ)+1)⁻¹^2 := by
      rw [sub_eq_add_neg, Real.exp_add, show -(2*L) = -2*L by ring, he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_sq_le_envelope n) (Real.exp_pos _).le

theorem summable_term {a : ℝ} (ha : 0 < a) (s : ℂ) : Summable (term a s) :=
  ((by simpa using (envelope_hasSum 0).summable : Summable envelope).mul_left
    (Real.exp ((-s.re+2)^2/(4*a)))).of_norm_bounded
      (norm_term_le ha (R := -s.re) (by linarith))

theorem entire_series {a : ℝ} (ha : 0 < a) : Differentiable ℂ (series a) := by
  intro s
  let R := |s.re|+1
  have hu : IsOpen {w : ℂ | -R < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (series a) {w : ℂ | -R < w.re} := by
    apply differentiableOn_tsum_of_summable_norm
      ((by simpa using (envelope_hasSum 0).summable : Summable envelope).mul_left
        (Real.exp ((R+2)^2/(4*a))))
      (fun n => (show Differentiable ℂ (fun s => term a s n) by
        unfold term; fun_prop).differentiableOn) hu
    intro n w hw
    exact norm_term_le ha hw.le n
  apply (hd s (by dsimp [R]; have := neg_abs_le s.re; linarith)).differentiableAt
  exact hu.mem_nhds (by dsimp [R]; have := neg_abs_le s.re; linarith)

/-- Uniform convergence on every left-bounded half-plane, hence on rectangles. -/
theorem partialSum_convergence {a : ℝ} (ha : 0 < a) (R : ℝ) :
    TendstoUniformlyOn (partialSum a) (series a) atTop {s : ℂ | -R ≤ s.re} :=
  tendstoUniformlyOn_tsum_nat
    ((by simpa using (envelope_hasSum 0).summable : Summable envelope).mul_left
      (Real.exp ((R+2)^2/(4*a))))
    (fun n s hs => norm_term_le ha hs n)

/-- A simple executable-checker target: the cutoff condition gives a 2/(N+1) tail. -/
theorem tail_bound {a R : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : R+2 ≤ a*Real.log ((N : ℝ)+1)) {s : ℂ} (hs : -R ≤ s.re) :
    ‖series a s - partialSum a N s‖ ≤ 2/((N : ℝ)+1) := by
  have hb (k : ℕ) : ‖term a s (k+N)‖ ≤ envelope (k+N) := by
    let L := Real.log (((k+N : ℕ) : ℝ)+1)
    have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (k+N)])
    have hlog : Real.log ((N : ℝ)+1) ≤ L := by
      apply Real.log_le_log (by positivity)
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hx : -a*L^2-s.re*L ≤ -2*L := by
      nlinarith [mul_nonneg (show 0 ≤ a*L-(R+2) by nlinarith) hL,
        mul_nonneg (show 0 ≤ s.re+R by linarith) hL]
    have he : Real.exp (-2*L) = (((k+N : ℕ) : ℝ)+1)⁻¹^2 := by
      rw [show -2*L = -(2*L) by ring, Real.exp_neg, show 2*L = L+L by ring, Real.exp_add,
        Real.exp_log (by positivity), mul_inv_rev]
      ring
    rw [norm_term]
    exact (Real.exp_le_exp.mpr hx |>.trans_eq he).trans (inv_sq_le_envelope _)
  have h := SeriesTail.of_majorant (term a s) N _ (envelope_hasSum N).summable hb
  simpa only [series, partialSum, (envelope_hasSum N).tsum_eq] using h.2

/-- An explicit global bound of order at most two. -/
theorem growth_bound {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ‖series a s‖ ≤ Real.exp ((2+1/a)*(1+‖s‖)^2) := by
  have hs : -‖s‖ ≤ s.re := by
    have := Complex.abs_re_le_norm s
    have := neg_abs_le s.re
    linarith
  have hb : ‖series a s‖ ≤ Real.exp ((‖s‖+2)^2/(4*a))*2 := by
    apply tsum_of_norm_bounded
      (show HasSum (fun n => Real.exp ((‖s‖+2)^2/(4*a))*envelope n)
        (Real.exp ((‖s‖+2)^2/(4*a))*2) by
        simpa using (envelope_hasSum 0).mul_left (Real.exp ((‖s‖+2)^2/(4*a))))
    exact norm_term_le ha hs
  have he : (‖s‖+2)^2/(4*a)+2 ≤ (2+1/a)*(1+‖s‖)^2 := by
    have hn := norm_nonneg s
    have hi : 0 < 1/a := by positivity
    have hid : a*(1/a) = 1 := by field_simp
    have hd : 4*a*((‖s‖+2)^2/(4*a)) = (‖s‖+2)^2 := by field_simp
    nlinarith [sq_nonneg ‖s‖, mul_nonneg hi.le (sq_nonneg ‖s‖)]
  calc
    ‖series a s‖ ≤ Real.exp ((‖s‖+2)^2/(4*a))*2 := hb
    _ ≤ Real.exp ((‖s‖+2)^2/(4*a))*Real.exp 2 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by positivity)
    _ = Real.exp ((‖s‖+2)^2/(4*a)+2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem term_real (a x : ℝ) (n : ℕ) :
    term a (x : ℂ) n = (Real.exp (-a*Real.log ((n : ℝ)+1)^2 -
      x*Real.log ((n : ℝ)+1)) : ℂ) := by
  simp only [term, Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_mul]

/-- On the positive real axis the series tends to its first coefficient. -/
theorem tendsto_series_real {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => series a (x : ℂ)) atTop (𝓝 1) := by
  have ht (n : ℕ) : Tendsto (fun x : ℝ => term a (x : ℂ) n) atTop
      (𝓝 (if n = 0 then 1 else 0)) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hL : 0 < Real.log ((n : ℝ)+1) := Real.log_pos (by
        have : 0 < n := Nat.pos_of_ne_zero hn
        exact_mod_cast (show 1 < n+1 by omega))
      simp only [term_real, hn, ↓reduceIte]
      have hx : Tendsto (fun x : ℝ => -a*Real.log ((n : ℝ)+1)^2 -
          x*Real.log ((n : ℝ)+1)) atTop atBot := by
        convert tendsto_atBot_add_const_left atTop (-a*Real.log ((n : ℝ)+1)^2)
          (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hL)) using 1
        ext x
        simp only [Function.comp_def, id_eq]
        ring
      simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp
        (Real.tendsto_exp_atBot.comp hx)
  have h := tendsto_tsum_of_dominated_convergence
    ((by simpa using (envelope_hasSum 0).summable : Summable envelope).mul_left
      (Real.exp ((0+2)^2/(4*a)))) ht
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx n
        exact norm_term_le ha (R := 0) (by simpa using hx) n)
  simpa [series] using h

/-- The series is not the constant one: its second coefficient is positive. -/
theorem one_lt_re_series_zero {a : ℝ} (ha : 0 < a) : 1 < (series a 0).re := by
  have ht (n : ℕ) : 0 < (term a 0 n).re := by
    simpa only [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, term_real,
      Complex.ofReal_re] using Real.exp_pos (-a*Real.log ((n : ℝ)+1)^2 -
        0*Real.log ((n : ℝ)+1))
  have hr := Complex.reCLM.summable (summable_term ha 0)
  have hb := hr.sum_le_tsum (Finset.range 2) (fun n _ => (ht n).le)
  have he := Complex.reCLM.map_tsum (summable_term ha 0)
  change (series a 0).re = ∑' n, (term a 0 n).re at he
  rw [← he] at hb
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    term_zero, Complex.one_re] at hb
  linarith [ht 1]

/-- Every positively damped Dirichlet series has a complex zero.
This is symbolic in a; no finite zero search is used. -/
theorem exists_zero {a : ℝ} (ha : 0 < a) : ∃ s : ℂ, series a s = 0 := by
  classical
  by_contra hz
  have hn : ∀ s, series a s ≠ 0 := by simpa using hz
  obtain ⟨P, hdeg, hP⟩ := Complex.Hadamard.zero_free_polynomial_growth_is_exp_poly
    (n := 2) (entire_series ha) hn
    ⟨2+1/a, by positivity, growth_bound ha⟩
  let Q : Polynomial ℝ := Polynomial.C (P.coeff 0).re +
    Polynomial.C (P.coeff 1).re * Polynomial.X +
    Polynomial.C (P.coeff 2).re * Polynomial.X^2
  have hQ (x : ℝ) : Q.eval x = (P.eval (x : ℂ)).re := by
    rw [Polynomial.eval_eq_sum_range' (show P.natDegree < 3 by omega)]
    simp [Q, Finset.sum_range_succ, Complex.mul_re, ← Complex.ofReal_pow]
  have hlim : Tendsto (fun x : ℝ => Q.eval x) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.comp
      (by simpa only [norm_one] using (tendsto_series_real ha).norm)
    have he (x : ℝ) : Real.log ‖series a (x : ℂ)‖ = Q.eval x := by
      rw [hP, Complex.norm_exp, Real.log_exp, hQ]
    simpa only [Function.comp_def, norm_one, Real.log_one, he] using h
  have hzero : Q = 0 := Polynomial.leadingCoeff_eq_zero.mp
    ((Polynomial.tendsto_nhds_iff Q).mp hlim).1
  have hr : (P.eval (0 : ℂ)).re = 0 := by
    simpa [hzero] using (hQ 0).symm
  have hnorm : ‖series a 0‖ = 1 := by rw [hP, Complex.norm_exp, hr, Real.exp_zero]
  have := Complex.abs_re_le_norm (series a 0)
  have := le_abs_self (series a 0).re
  linarith [one_lt_re_series_zero ha]

/-- DBN time normalization: a = -t/4. This is not yet a zero of the heat integral. -/
theorem negative_time_exists_zero {t : ℝ} (ht : t < 0) :
    ∃ s : ℂ, series (-t/4) s = 0 := exists_zero (by linarith)

end LeanCert.Analysis.DirichletGaussian
