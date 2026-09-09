/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Relative Gamma estimates from finite Euler approximants. -/
namespace LeanCert.Analysis.GammaRatio
open Complex Finset Filter Set
open scoped Topology

private theorem add_nat_ne_zero {s : ℂ} (hs : 0 < s.im) (j : ℕ) : s+j ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private theorem im_le_norm_add_nat {s : ℂ} (hs : 0 ≤ s.im) (j : ℕ) : s.im ≤ ‖s+j‖ := by
  simpa [abs_of_nonneg hs] using Complex.abs_im_le_norm (s+j)

/-- A discrete resolvent square bound uniform in the number of Euler factors. -/
theorem sum_inv_norm_sq_le {s : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 1 ≤ s.im) (N : ℕ) :
    (∑ j ∈ range N, ‖s+j‖⁻¹^2) ≤ 8/s.im := by
  have hy : 0 < s.im := by linarith
  have hstep (j : ℕ) : ‖s+j‖⁻¹^2 ≤
      8*((s.im+j)⁻¹-(s.im+(j+1 : ℕ))⁻¹) := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hn : 0 < ‖s+j‖ := norm_pos_iff.mpr (add_nat_ne_zero hy j)
    have hn2 : (s.im+(j : ℝ))^2 ≤ 4*‖s+j‖^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [add_re, add_im, natCast_re, natCast_im, add_zero]
      nlinarith [sq_nonneg (s.im-j), sq_nonneg s.re, mul_nonneg hr hj]
    calc
      ‖s+j‖⁻¹^2 ≤ 4/(s.im+(j : ℝ))^2 := by
        rw [inv_pow, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      _ ≤ _ := by
        push_cast
        have hp : 0 < s.im+j := by positivity
        have hp' : 0 < s.im+(j : ℝ)+1 := by positivity
        field_simp
        nlinarith
  have hsum (n : ℕ) :
      (∑ j ∈ range n, 8*((s.im+j)⁻¹-(s.im+(j+1 : ℕ))⁻¹)) =
        8*(s.im⁻¹-(s.im+n)⁻¹) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  calc
    _ ≤ ∑ j ∈ range N, 8*((s.im+j)⁻¹-(s.im+(j+1 : ℕ))⁻¹) := sum_le_sum (fun j _ => hstep j)
    _ = 8*(s.im⁻¹-(s.im+N)⁻¹) := hsum N
    _ ≤ _ := by
      have hn : 0 ≤ (s.im+(N : ℝ))⁻¹ := by positivity
      rw [div_eq_mul_inv]
      linarith

/-- Cubic remainders in logarithmic Euler factors are summably bounded. -/
theorem sum_inv_norm_cube_le {s : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 1 ≤ s.im) (N : ℕ) :
    (∑ j ∈ range N, ‖s+j‖⁻¹^3) ≤ 8/s.im^2 := by
  have hy : 0 < s.im := by linarith
  have hstep (j : ℕ) : ‖s+j‖⁻¹^3 ≤ s.im⁻¹*‖s+j‖⁻¹^2 := by
    have hn := im_le_norm_add_nat hy.le j
    have h := inv_anti₀ hy hn
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖s+j‖⁻¹)]
  calc
    _ ≤ ∑ j ∈ range N, s.im⁻¹*‖s+j‖⁻¹^2 := sum_le_sum (fun j _ => hstep j)
    _ = s.im⁻¹ * ∑ j ∈ range N, ‖s+j‖⁻¹^2 := by rw [mul_sum]
    _ ≤ s.im⁻¹ * (8/s.im) := mul_le_mul_of_nonneg_left (sum_inv_norm_sq_le hr hi N) (by positivity)
    _ = _ := by field_simp

private theorem norm_log_linear_error {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖Complex.log (1+z)-z‖ ≤ ‖z‖^2 := by
  have h := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hz (by norm_num))
  have hd : (1-‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1-‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg ‖z‖)]

private theorem norm_log_quadratic_error {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖Complex.log (1+z)-z+z^2/2‖ ≤ ‖z‖^3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2 (lt_of_le_of_lt hz (by norm_num))
  have ht : Complex.logTaylor 3 z = z-z^2/2 := by
    simp [Complex.logTaylor, sum_range_succ]
    ring
  rw [ht] at h
  have hd : (1-‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1-‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have he : Complex.log (1+z)-(z-z^2/2) = Complex.log (1+z)-z+z^2/2 := by ring
  rw [he] at h
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  nlinarith [mul_le_mul_of_nonneg_left hd (pow_nonneg (norm_nonneg z) 3),
    pow_nonneg (norm_nonneg z) 3]

/-- The principal logarithms telescope along this pole-free horizontal ray. -/
theorem log_step {s : ℂ} (hi : 0 < s.im) :
    Complex.log (1+s⁻¹) = Complex.log (s+1)-Complex.log s := by
  have hs : s ≠ 0 := by intro h; simp [h] at hi
  have hs' : s+1 ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; linarith
  have ha : 0 ≤ s.arg := Complex.arg_nonneg_iff.mpr hi.le
  have hb : s.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hi))
  have ha' : 0 ≤ (s+1).arg := Complex.arg_nonneg_iff.mpr (by simpa using hi.le)
  have hb' : (s+1).arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (by simpa using ne_of_gt hi))
  have hπ : s.arg ≠ Real.pi := ne_of_lt hb
  have hlog := Complex.log_mul (inv_ne_zero hs) hs' (show (s⁻¹).arg+(s+1).arg ∈ Ioc (-Real.pi) Real.pi from by
    rw [Complex.arg_inv, if_neg hπ]
    constructor <;> linarith)
  rw [Complex.log_inv _ hπ] at hlog
  have he : s⁻¹*(s+1) = 1+s⁻¹ := by field_simp
  rw [he] at hlog
  linear_combination hlog

/-- First Euler sum/integral discrepancy, obtained without differentiating a limit. -/
theorem harmonic_error_bound {s : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 2 ≤ s.im) (N : ℕ) :
    ‖(∑ j ∈ range N, (s+j)⁻¹) - (Complex.log (s+N)-Complex.log s)‖ ≤ 8/s.im := by
  have hy : 0 < s.im := by linarith
  have ht (n : ℕ) : (∑ j ∈ range n, Complex.log (1+(s+j)⁻¹)) =
      Complex.log (s+n)-Complex.log s := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, log_step (by simpa using hy)]
      push_cast
      simp only [add_assoc]
      abel
  rw [← ht, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun j hj => ?_)).trans (sum_inv_norm_sq_le hr (by linarith) N)
  rw [norm_sub_rev]
  apply (norm_log_linear_error (z := (s+j)⁻¹) ?_).trans_eq
  · simp [norm_inv]
  · rw [norm_inv, inv_le_comm₀ (by linarith [im_le_norm_add_nat hy.le j] : 0 < ‖s+j‖) (by norm_num : (0 : ℝ) < 1/2)]
    linarith [im_le_norm_add_nat hy.le j]

/-- The quadratic Euler coefficient is an inverse, up to a uniform O(y^-2) error. -/
theorem inverse_square_error_bound {s : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 1 ≤ s.im) (N : ℕ) :
    ‖(∑ j ∈ range N, (s+j)⁻¹^2) - (s⁻¹-(s+N)⁻¹)‖ ≤ 8/s.im^2 := by
  have hy : 0 < s.im := by linarith
  have ht (n : ℕ) : (∑ j ∈ range n, ((s+j)⁻¹-(s+(j+1 : ℕ))⁻¹)) = s⁻¹-(s+n)⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [← ht, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun j hj => ?_)).trans (show (∑ j ∈ range N, s.im⁻¹*‖s+j‖⁻¹^2) ≤ 8/s.im^2 from by
    rw [← mul_sum]
    calc
      _ ≤ s.im⁻¹*(8/s.im) := mul_le_mul_of_nonneg_left (sum_inv_norm_sq_le hr hi N) (by positivity)
      _ = _ := by field_simp)
  have hn := add_nat_ne_zero hy j
  have hn' := add_nat_ne_zero hy (j+1)
  have he : (s+j)⁻¹^2 - ((s+j)⁻¹-(s+(j+1 : ℕ))⁻¹) =
      (s+j)⁻¹^2 * (s+(j+1 : ℕ))⁻¹ := by
    field_simp
    push_cast
    ring
  rw [he, norm_mul, norm_pow, norm_inv, norm_inv]
  have hinv := inv_anti₀ hy (im_le_norm_add_nat hy.le (j+1))
  nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖s+j‖⁻¹)]

/-- A quadratic expansion of ALL finite Euler log factors with a remainder
independent of the number of factors. -/
theorem euler_log_remainder_bound {s u : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 1 ≤ s.im)
    (hu : ‖u‖ ≤ s.im/2) (N : ℕ) :
    ‖(∑ j ∈ range N, Complex.log (1+u/(s+j))) -
      (u*(∑ j ∈ range N, (s+j)⁻¹) - u^2/2*(∑ j ∈ range N, (s+j)⁻¹^2))‖ ≤
        8*‖u‖^3/s.im^2 := by
  have hy : 0 < s.im := by linarith
  have he : (∑ j ∈ range N, Complex.log (1+u/(s+j))) -
      (u*(∑ j ∈ range N, (s+j)⁻¹) - u^2/2*(∑ j ∈ range N, (s+j)⁻¹^2)) =
      ∑ j ∈ range N, (Complex.log (1+u/(s+j)) - u/(s+j) + (u/(s+j))^2/2) := by
    simp only [sum_add_distrib, sum_sub_distrib, div_eq_mul_inv, mul_pow, mul_sum]
    simp only [mul_assoc, mul_comm]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j ∈ range N, ‖Complex.log (1+u/(s+j)) - u/(s+j) + (u/(s+j))^2/2‖) ≤
        ∑ j ∈ range N, ‖u‖^3 * ‖s+j‖⁻¹^3 := by
      apply sum_le_sum
      intro j hj
      have hh : ‖u/(s+j)‖ ≤ 1/2 := by
        rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (add_nat_ne_zero hy j))]
        linarith [im_le_norm_add_nat hy.le j]
      simpa only [norm_div, div_pow, div_eq_mul_inv, inv_pow, norm_mul, norm_inv, mul_pow] using norm_log_quadratic_error hh
    _ = ‖u‖^3 * ∑ j ∈ range N, ‖s+j‖⁻¹^3 := by rw [mul_sum]
    _ ≤ ‖u‖^3 * (8/s.im^2) :=
      mul_le_mul_of_nonneg_left (sum_inv_norm_cube_le hr hi N) (by positivity)
    _ = _ := by ring

/-- Analytic logarithm of the relative Euler approximant, with a positive
natural index so that the power is never evaluated at zero. -/
noncomputable def logEulerRatio (s u : ℂ) (N : ℕ) : ℂ :=
  u*(Real.log ((N : ℝ)+1) : ℂ) -
    ∑ j ∈ range (N+2), Complex.log (1+u/(s+j))

noncomputable def ratioError (y r : ℝ) : ℝ :=
  8*r/y + 4*r^2/y^2 + 8*r^3/y^2

/-- Explicit bound on the logarithmic error before the Euler limit is taken. -/
theorem logEulerRatio_error_bound {s u : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 2 ≤ s.im)
    (hu : ‖u‖ ≤ s.im/2) (N : ℕ) :
    ‖logEulerRatio s u N - (u*Complex.log s+u^2/(2*s))‖ ≤
      ratioError s.im ‖u‖ +
      ‖u‖*‖(Real.log ((N : ℝ)+1) : ℂ)-Complex.log (s+(N+2 : ℕ))‖ +
      (‖u‖^2/2)*‖(s+(N+2 : ℕ))⁻¹‖ := by
  let H := (∑ j ∈ range (N+2), (s+j)⁻¹) - (Complex.log (s+(N+2 : ℕ))-Complex.log s)
  let Q := (∑ j ∈ range (N+2), (s+j)⁻¹^2) - (s⁻¹-(s+(N+2 : ℕ))⁻¹)
  let R := (∑ j ∈ range (N+2), Complex.log (1+u/(s+j))) -
      (u*(∑ j ∈ range (N+2), (s+j)⁻¹)-u^2/2*(∑ j ∈ range (N+2), (s+j)⁻¹^2))
  let A := u*((Real.log ((N : ℝ)+1) : ℂ)-Complex.log (s+(N+2 : ℕ)))
  let D := u^2/2*(s+(N+2 : ℕ))⁻¹
  have hH : ‖H‖ ≤ 8/s.im := harmonic_error_bound hr hi _
  have hQ : ‖Q‖ ≤ 8/s.im^2 := inverse_square_error_bound hr (by linarith) _
  have hR : ‖R‖ ≤ 8*‖u‖^3/s.im^2 := euler_log_remainder_bound hr (by linarith) hu _
  have he : logEulerRatio s u N - (u*Complex.log s+u^2/(2*s)) =
      A-u*H+(u^2/2)*Q-D-R := by
    dsimp [logEulerRatio, A, H, Q, D, R]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [he]
  have hn : ‖A-u*H+(u^2/2)*Q-D-R‖ ≤
      ‖A‖+‖u*H‖+‖(u^2/2)*Q‖+‖D‖+‖R‖ := by
    have h1 := norm_sub_le A (u*H)
    have h2 := norm_add_le (A-u*H) ((u^2/2)*Q)
    have h3 := norm_sub_le (A-u*H+(u^2/2)*Q) D
    have h4 := norm_sub_le (A-u*H+(u^2/2)*Q-D) R
    linarith
  apply hn.trans
  simp only [A, D, norm_mul, norm_div, norm_pow, Complex.norm_ofNat]
  have hmH := mul_le_mul_of_nonneg_left hH (norm_nonneg u)
  have hmQ := mul_le_mul_of_nonneg_left hQ (show 0 ≤ ‖u‖^2/2 by positivity)
  unfold ratioError
  convert add_le_add (add_le_add (add_le_add (le_refl ‖A‖) hmH) hmQ) (add_le_add (le_refl ‖D‖) hR) using 1 <;>
    dsimp [A, D] <;> simp only [norm_mul, norm_div, norm_pow, Complex.norm_ofNat] <;> ring

private theorem shift_im_pos {s u : ℂ} (hi : 0 < s.im) (hu : ‖u‖ ≤ s.im/2) :
    0 < (s+u).im := by
  have := Complex.abs_im_le_norm u
  have := neg_abs_le u.im
  simp only [add_im]
  linarith

/-- The exponentials of the finite logarithmic expressions are the ACTUAL
ratios of Euler approximants, not a separately assumed Gamma model. -/
theorem exp_logEulerRatio {s u : ℂ} (hi : 0 < s.im) (hu : ‖u‖ ≤ s.im/2) (N : ℕ) :
    Complex.exp (logEulerRatio s u N) =
      Complex.GammaSeq (s+u) (N+1) / Complex.GammaSeq s (N+1) := by
  have hs : ∀ j : ℕ, s+j ≠ 0 := add_nat_ne_zero hi
  have hsu : ∀ j : ℕ, s+u+j ≠ 0 := add_nat_ne_zero (shift_im_pos hi hu)
  have hn : ((N+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hf : (((N+1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N+1)
  have hprod : ∏ j ∈ range (N+2), (1+u/(s+j)) =
      (∏ j ∈ range (N+2), (s+u+j)) / (∏ j ∈ range (N+2), (s+j)) := by
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro j hj
    field_simp [hs j]
    ring
  have hexp : Complex.exp (∑ j ∈ range (N+2), Complex.log (1+u/(s+j))) =
      ∏ j ∈ range (N+2), (1+u/(s+j)) := by
    rw [Complex.exp_sum]
    apply prod_congr rfl
    intro j hj
    apply Complex.exp_log
    have he : 1+u/(s+j) = (s+u+j)/(s+j) := by field_simp [hs j]; ring
    rw [he]
    exact div_ne_zero (hsu j) (hs j)
  have hpow : Complex.exp (u*(Real.log ((N : ℝ)+1) : ℂ)) = ((N+1 : ℕ) : ℂ)^u := by
    rw [Complex.cpow_def_of_ne_zero hn]
    congr 1
    rw [show ((N+1 : ℕ) : ℂ) = (((N : ℝ)+1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by positivity)]
    ring
  rw [logEulerRatio, Complex.exp_sub, hexp, hprod, hpow, Complex.GammaSeq, Complex.GammaSeq,
    Complex.cpow_add _ _ hn]
  have hp := Finset.prod_ne_zero_iff.mpr (fun j (hj : j ∈ Finset.range (N+2)) => hs j)
  have hp' := Finset.prod_ne_zero_iff.mpr (fun j (hj : j ∈ Finset.range (N+2)) => hsu j)
  have hcp : ((N+1 : ℕ) : ℂ)^s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn]; exact Complex.exp_ne_zero _
  simp only [show N+1+1 = N+2 by omega]
  field_simp

/-- Pass to Gamma using only the already-proved Euler limit theorem. -/
theorem exp_logEulerRatio_tendsto {s u : ℂ} (hi : 0 < s.im) (hu : ‖u‖ ≤ s.im/2) :
    Tendsto (fun N => Complex.exp (logEulerRatio s u N)) atTop
      (𝓝 (Complex.Gamma (s+u)/Complex.Gamma s)) := by
  have hg : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hN : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  simpa only [exp_logEulerRatio hi hu, Function.comp_def, Pi.div_def] using
    ((Complex.GammaSeq_tendsto_Gamma (s+u)).comp hN).div
      ((Complex.GammaSeq_tendsto_Gamma s).comp hN) hg

private theorem endpoint_limits (s : ℂ) (hi : 0 < s.im) :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ)+1) : ℂ) -
      Complex.log (s+(N+2 : ℕ))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (s+(N+2 : ℕ))⁻¹) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsmall : Tendsto (fun N : ℕ => (s+1)/((N+1 : ℕ) : ℂ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (s+1)).comp hN
  have hone : Tendsto (fun N : ℕ => 1+(s+1)/((N+1 : ℕ) : ℂ)) atTop (𝓝 1) := by
    simpa using hsmall.const_add 1
  have hlog := (continuousAt_clog (show (1 : ℂ) ∈ Complex.slitPlane by simp)).tendsto.comp hone
  have hinv : Tendsto (fun N : ℕ => (((N+1 : ℕ) : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℂ)).comp hN
  have hfac (N : ℕ) : s+(N+2 : ℕ) =
      ((N+1 : ℕ) : ℂ) * (1+(s+1)/((N+1 : ℕ) : ℂ)) := by
    have hn : ((N+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    field_simp
    push_cast
    ring
  have hnz (N : ℕ) : 1+(s+1)/((N+1 : ℕ) : ℂ) ≠ 0 := by
    intro h
    have := hfac N
    rw [h, mul_zero] at this
    exact add_nat_ne_zero hi (N+2) this
  constructor
  · convert hlog.neg using 1
    · ext N
      rw [hfac N]
      have he := Complex.log_ofReal_mul (show (0 : ℝ) < (N+1 : ℕ) by positivity) (hnz N)
      push_cast at he ⊢
      rw [he]
      simp only [Function.comp_apply]
      abel
    · simp
  · convert hinv.mul (hone.inv₀ (by norm_num)) using 1
    · ext N
      rw [hfac N, mul_inv]
    · simp

/-- A uniform, quantitative quadratic Gamma-ratio estimate, obtained from the
actual Euler limit. No Stirling formula or asymptotic hypothesis is assumed. -/
theorem relative_error_bound {s u : ℂ} (hr : 0 ≤ s.re+s.im/2) (hi : 2 ≤ s.im)
    (hu : ‖u‖ ≤ s.im/2) :
    ‖Complex.Gamma (s+u) / Complex.Gamma s /
        Complex.exp (u*Complex.log s+u^2/(2*s)) - 1‖ ≤
      Real.exp (ratioError s.im ‖u‖) - 1 := by
  let model := u*Complex.log s+u^2/(2*s)
  let E := fun N : ℕ => ratioError s.im ‖u‖ +
    ‖u‖*‖(Real.log ((N : ℝ)+1) : ℂ)-Complex.log (s+(N+2 : ℕ))‖ +
    ‖u‖^2/2*‖(s+(N+2 : ℕ))⁻¹‖
  have hb (N : ℕ) : ‖Complex.exp (logEulerRatio s u N)/Complex.exp model-1‖ ≤
      Real.exp (E N)-1 := by
    rw [← Complex.exp_sub]
    have he : ‖Complex.exp (logEulerRatio s u N-model)-1‖ ≤
        Real.exp ‖logEulerRatio s u N-model‖-1 := by
      simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (logEulerRatio s u N-model) 1
    exact he.trans (sub_le_sub_right (Real.exp_le_exp.mpr (logEulerRatio_error_bound hr hi hu N)) 1)
  have hl := endpoint_limits s (by linarith)
  have hE : Tendsto E atTop (𝓝 (ratioError s.im ‖u‖)) := by
    simpa [E] using ((hl.1.norm.const_mul ‖u‖).const_add (ratioError s.im ‖u‖)).add
      (hl.2.norm.const_mul (‖u‖^2/2))
  exact le_of_tendsto_of_tendsto
    (((exp_logEulerRatio_tendsto (by linarith) hu).div_const (Complex.exp model)).sub_const 1).norm
    (((Real.continuous_exp.tendsto _).comp hE).sub_const 1) (Filter.Eventually.of_forall hb)

/-- A concrete growing-radius specialization: displacements of size `h^3`
at height at least `h^5` have relative error at most `exp(20/h)-1`.
In particular this is not restricted to fixed displacements. -/
theorem relative_error_bound_growing {s u : ℂ} {h : ℝ} (hh : 2 ≤ h)
    (hr : 0 ≤ s.re+s.im/2) (hy : h^5 ≤ s.im) (hu : ‖u‖ ≤ h^3) :
    ‖Complex.Gamma (s+u) / Complex.Gamma s /
        Complex.exp (u*Complex.log s+u^2/(2*s)) - 1‖ ≤ Real.exp (20/h)-1 := by
  have hp : 0 < h := by linarith
  have h1 : 1 ≤ h := by linarith
  have h2 : 2 ≤ h^2 := by nlinarith
  have h3p : 0 < h^3 := by positivity
  have h5 : 2 ≤ h^5 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hh 5
    norm_num at this
    linarith
  have hub : ‖u‖ ≤ s.im/2 := by
    have hx : 2*h^3 ≤ h^5 := by nlinarith [mul_le_mul_of_nonneg_right h2 (le_of_lt h3p)]
    linarith
  apply (relative_error_bound hr (h5.trans hy) hub).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hypos : 0 < s.im := by linarith
  have hmono : ratioError s.im ‖u‖ ≤ ratioError (h^5) (h^3) := by
    unfold ratioError
    gcongr
  apply hmono.trans
  have he : ratioError (h^5) (h^3) = 8/h^2+4/h^4+8/h := by
    unfold ratioError
    field_simp
  rw [he]
  have hs2 : h ≤ h^2 := by nlinarith
  have hs4 : h ≤ h^4 := by nlinarith [sq_nonneg (h^2-1)]
  have hq2 : 8/h^2 ≤ 8/h := by gcongr
  have hq4 : 4/h^4 ≤ 4/h := by gcongr
  calc
    _ ≤ 8/h+4/h+8/h := by linarith
    _ = 20/h := by ring

end LeanCert.Analysis.GammaRatio
