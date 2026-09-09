/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DirichletGaussian
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Sequences
import LeanCert.Analysis.DBN.ZeroTransfer

/-! Simultaneous recurrence of the countably many Dirichlet phases. -/
namespace LeanCert.Analysis.DirichletGaussian
open Complex Filter Set
open scoped Topology

/-- Compactness of the countable torus supplies unbounded simultaneous returns.
The differences of the 2n-th and n-th subsequence indices are at least n. -/
theorem exists_phase_returns (ω : ℕ → ℝ) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
      ∀ k, Tendsto (fun n => Circle.exp (τ n * ω k)) atTop (𝓝 1) := by
  obtain ⟨v, φ, hφ, hv⟩ := CompactSpace.tendsto_subseq
    (fun n : ℕ => fun k : ℕ => Circle.exp ((n : ℝ) * ω k))
  let τ : ℕ → ℝ := fun n => (φ (2*n) : ℝ) - (φ n : ℝ)
  have hτ (n : ℕ) : (n : ℝ) ≤ τ n := by
    have h := hφ.add_le_nat n n
    dsimp [τ]
    have h' : φ n + n ≤ φ (2*n) := by simpa [two_mul, add_comm] using h
    exact_mod_cast (show (n : ℤ) ≤ (φ (2*n) : ℤ) - (φ n : ℤ) by omega)
  refine ⟨τ, tendsto_atTop_mono hτ tendsto_natCast_atTop_atTop, ?_⟩
  intro k
  have hk := (continuous_apply k).tendsto v |>.comp hv
  have h2 : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hd := (hk.comp h2).div' hk
  simpa [τ, sub_mul, Circle.exp_sub, Function.comp_def] using hd

/-- Imaginary translation changes only a unit-modulus phase. -/
theorem term_translate (a y : ℝ) (s : ℂ) (k : ℕ) :
    term a (s + (y : ℂ)*I) k = term a s k *
      (Circle.exp (y * (-Real.log ((k : ℝ)+1))) : ℂ) := by
  rw [term, term, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A single scalar majorant controls the translation error throughout a half-plane. -/
theorem translation_error_bound {a : ℝ} (ha : 0 < a) (R y : ℝ)
    {s : ℂ} (hs : -R ≤ s.re) :
    ‖series a (s + (y : ℂ)*I) - series a s‖ ≤
      ∑' k, (Real.exp ((R+2)^2/(4*a))*envelope k) *
        ‖(Circle.exp (y * (-Real.log ((k : ℝ)+1))) : ℂ) - 1‖ := by
  have hp (k : ℕ) : ‖(Circle.exp (y * (-Real.log ((k : ℝ)+1))) : ℂ) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(Circle.exp (y * (-Real.log ((k : ℝ)+1))) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num
  have hm : Summable (fun k => Real.exp ((R+2)^2/(4*a))*envelope k) :=
    (by simpa using (envelope_hasSum 0).summable : Summable envelope).mul_left _
  have hb (k : ℕ) : 0 ≤ Real.exp ((R+2)^2/(4*a))*envelope k :=
    mul_nonneg (Real.exp_pos _).le (envelope_nonneg k)
  have hg : Summable (fun k => (Real.exp ((R+2)^2/(4*a))*envelope k) *
      ‖(Circle.exp (y * (-Real.log ((k : ℝ)+1))) : ℂ) - 1‖) :=
    (hm.mul_right 2).of_nonneg_of_le (fun k => mul_nonneg (hb k) (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (hp k) (hb k))
  rw [series, series, ← (summable_term ha _).tsum_sub (summable_term ha _)]
  apply tsum_of_norm_bounded hg.hasSum
  intro k
  rw [term_translate, ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_term_le ha hs k) (norm_nonneg _)

/-- Recurring phases imply uniform recurrence on every left-bounded half-plane. -/
theorem translate_convergence {a : ℝ} (ha : 0 < a) {τ : ℕ → ℝ}
    (hτ : ∀ k : ℕ, Tendsto (fun n => Circle.exp (τ n * (-Real.log ((k : ℝ)+1))))
      atTop (𝓝 1)) (R : ℝ) :
    TendstoUniformlyOn (fun n s => series a (s + (τ n : ℂ)*I)) (series a)
      atTop {s : ℂ | -R ≤ s.re} := by
  let M : ℕ → ℝ := fun k => Real.exp ((R+2)^2/(4*a))*envelope k
  let e : ℕ → ℕ → ℝ := fun n k => M k *
    ‖(Circle.exp (τ n * (-Real.log ((k : ℝ)+1))) : ℂ) - 1‖
  have hM : Summable M :=
    (by simpa using (envelope_hasSum 0).summable : Summable envelope).mul_left _
  have hb (k : ℕ) : 0 ≤ M k := mul_nonneg (Real.exp_pos _).le (envelope_nonneg k)
  have he (k : ℕ) : Tendsto (fun n => e n k) atTop (𝓝 0) := by
    have h := (show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).tendsto 1 |>.comp (hτ k)
    simpa [e] using (tendsto_const_nhds (x := M k)).mul (h.sub (tendsto_const_nhds (x := (1 : ℂ)))).norm
  have hlim : Tendsto (fun n => ∑' k, e n k) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (hM.mul_right 2) he
      (Filter.Eventually.of_forall (fun n k => by
        have hp : ‖(Circle.exp (τ n * (-Real.log ((k : ℝ)+1))) : ℂ) - 1‖ ≤ 2 := by
          calc
            _ ≤ ‖(Circle.exp (τ n * (-Real.log ((k : ℝ)+1))) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb k) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left hp (hb k)))
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn s hs
  rw [dist_comm, dist_eq_norm]
  exact (translation_error_bound ha R (τ n) hs).trans_lt hn

/-- One unbounded sequence of translations works locally uniformly everywhere. -/
theorem exists_vertical_recurrence {a : ℝ} (ha : 0 < a) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
      TendstoLocallyUniformly (fun n s => series a (s + (τ n : ℂ)*I)) (series a) atTop := by
  obtain ⟨τ, ht, hp⟩ := exists_phase_returns (fun k => -Real.log ((k : ℝ)+1))
  refine ⟨τ, ht, tendstoLocallyUniformly_iff_forall_isCompact.mpr ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact (translate_convergence ha hp R).mono (fun s hs => by
    have h := Complex.abs_re_le_norm s
    have h' := neg_abs_le s.re
    have := hR s hs
    dsimp
    linarith)

/-- The zeros recur at arbitrarily large positive heights in one fixed strip. -/
theorem zeros_at_arbitrary_height {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, ∀ B : ℝ, ∃ s : ℂ,
      |s.re-c| < 1 ∧ B < s.im ∧ series a s = 0 := by
  obtain ⟨z, hz⟩ := exists_zero ha
  obtain ⟨τ, ht, hlim⟩ := exists_vertical_recurrence ha
  have hn : ∃ w, series a w ≠ 0 := by
    refine ⟨0, ?_⟩
    intro h
    have := one_lt_re_series_zero ha
    norm_num [h] at this
  have he := DBN.eventually_exists_zero_of_locally_uniform
    (F := fun n s => series a (s + (τ n : ℂ)*I))
    (fun K _ => Filter.Eventually.of_forall (fun n =>
      ((entire_series ha).comp (by fun_prop)).differentiableOn))
    (entire_series ha) hn hlim Metric.isOpen_ball
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) hz
  refine ⟨z.re, fun B => ?_⟩
  obtain ⟨n, hn, hnt⟩ := (he.and (ht.eventually (eventually_gt_atTop (B-z.im+1)))).exists
  obtain ⟨w, hw, hwzero⟩ := hn
  have hdist : ‖w-z‖ < 1 := by simpa [dist_eq_norm] using hw
  have hre : |w.re-z.re| < 1 := lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w-z)) hdist
  have him : |w.im-z.im| < 1 := lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w-z)) hdist
  refine ⟨w+(τ n : ℂ)*I, ?_, ?_, hwzero⟩
  · simpa using hre
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith [(abs_lt.mp him).1]

end LeanCert.Analysis.DirichletGaussian
