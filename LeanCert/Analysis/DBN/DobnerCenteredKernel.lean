/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerLinearBounds

namespace LeanCert.Analysis.DBN
open Complex Filter Set MeasureTheory
open scoped Topology

noncomputable def saddleOffset (a : ℝ) (s : ℂ) (L : ℝ) : ℝ :=
  max (2-s.re-2*a*L) 0

noncomputable def saddleDisplacement (a : ℝ) (s : ℂ) (L v : ℝ) : ℂ :=
  ((2*a*L+saddleOffset a s L : ℝ) : ℂ)+(v : ℂ)*I

noncomputable def centeredKernel (a : ℝ) (s : ℂ) (L v : ℝ) : ℂ :=
  saddleIntegrand (4*a) (dobnerMap a s) L (s+saddleDisplacement a s L v) / dobnerGamma a s

theorem saddleOffset_nonneg (a : ℝ) (s : ℂ) (L : ℝ) : 0 ≤ saddleOffset a s L := le_max_right _ _

theorem saddleOffset_le {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) {s : ℂ}
    (hs : |s.re| ≤ M) {L : ℝ} (hL : 0 ≤ L) : saddleOffset a s L ≤ M+2 := by
  unfold saddleOffset
  apply max_le
  · have := (abs_le.mp hs).1
    nlinarith [mul_nonneg ha.le hL]
  · linarith

theorem saddleDisplacement_re (a : ℝ) (s : ℂ) (L v : ℝ) :
    (saddleDisplacement a s L v).re = 2*a*L+saddleOffset a s L := by simp [saddleDisplacement]
theorem saddleDisplacement_im (a : ℝ) (s : ℂ) (L v : ℝ) :
    (saddleDisplacement a s L v).im = v := by simp [saddleDisplacement]
theorem saddleLine_re (a : ℝ) (s : ℂ) (L v : ℝ) :
    (s+saddleDisplacement a s L v).re = max 2 (s.re+2*a*L) := by
  rw [add_re, saddleDisplacement_re]
  unfold saddleOffset
  by_cases h : 2-s.re-2*a*L ≤ 0
  · rw [max_eq_right h, add_zero, max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith : 0 ≤ 2-s.re-2*a*L), max_eq_left (by linarith)]
    ring

theorem centeredKernel_factorization {a : ℝ} (ha : 0 < a) (s : ℂ) (L v : ℝ) :
    centeredKernel a s L v =
      (xiGamma (s+saddleDisplacement a s L v)/xiGamma s *
        Complex.exp (-Complex.log (s/(2*Real.pi))*saddleDisplacement a s L v/2)) *
      Complex.exp (-s*(L : ℂ)+(saddleDisplacement a s L v)^2/(4*(a : ℂ))-
        saddleDisplacement a s L v*(L : ℂ)) := by
  simpa only [centeredKernel, neg_mul] using
    saddleIntegrand_normalized_factorization ha s (saddleDisplacement a s L v) L

theorem centeredKernel_norm_eq {a : ℝ} (ha : 0 < a) (s : ℂ) (L v : ℝ) :
    ‖centeredKernel a s L v‖ =
      ‖xiGamma (s+saddleDisplacement a s L v)‖ * ‖(xiGamma s)⁻¹‖ *
      Real.exp (-a*L^2-s.re*L+(saddleOffset a s L)^2/(4*a)-v^2/(4*a)-
        (a*L+saddleOffset a s L/2)*(Complex.log (s/(2*Real.pi))).re+
        (Complex.log (s/(2*Real.pi))).im*v/2) := by
  rw [centeredKernel_factorization ha]
  simp only [norm_mul, norm_div, norm_inv, Complex.norm_exp, mul_assoc, ← Real.exp_add]
  rw [div_eq_mul_inv, mul_assoc]
  congr 2
  have he : (4 : ℂ)*(a : ℂ) = ((4*a : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  simp only [sub_re, add_re, neg_re, mul_re, div_ofNat_re, div_ofReal_re,
    pow_two, saddleDisplacement_re, saddleDisplacement_im, neg_im, ofReal_re,
    ofReal_im, mul_zero, sub_zero]
  field_simp
  ring

theorem centeredGaussian_re {a : ℝ} (ha : 0 < a) (s : ℂ) (L v : ℝ) :
    (-s*(L : ℂ)+(saddleDisplacement a s L v)^2/(4*(a : ℂ))-
      saddleDisplacement a s L v*(L : ℂ)).re =
      -a*L^2-s.re*L+(saddleOffset a s L)^2/(4*a)-v^2/(4*a) := by
  have he : (4 : ℂ)*(a : ℂ) = ((4*a : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  simp only [sub_re, add_re, neg_re, mul_re, div_ofReal_re, pow_two,
    saddleDisplacement_re, saddleDisplacement_im, ofReal_re, ofReal_im,
    mul_zero, sub_zero]
  field_simp
  ring

theorem centeredKernel_local_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 4 ≤ s.im → 2*M ≤ s.im →
      8*(M+2) ≤ s.im → 72*a ≤ s.im → ∀ L v : ℝ, 0 ≤ L → L ≤ s.im/(16*a) →
      |v| ≤ s.im/4 → ‖centeredKernel a s L v‖ ≤ C*Real.exp (-a*L^2/2-v^2/(8*a)) := by
  refine ⟨(9/4 : ℝ)*Real.exp 5 * Real.exp ((M+2)^2/(4*a)+9*(M+2)^2/2+M^2/a), by positivity, ?_⟩
  intro s hs hy hyM hyD hya L v hL hLy hv
  have hyp : 0 < s.im := by linarith
  have he0 := saddleOffset_nonneg a s L
  have heD := saddleOffset_le ha hM hs hL
  have hd0 : 0 ≤ 2*a*L+saddleOffset a s L := by positivity
  have hd : 2*a*L+saddleOffset a s L ≤ s.im/4 := by
    have h := (le_div_iff₀ (show 0 < 16*a by positivity)).mp hLy
    nlinarith
  have hsq : ‖saddleDisplacement a s L v‖^2 = (2*a*L+saddleOffset a s L)^2+v^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, saddleDisplacement_re, saddleDisplacement_im]
    ring
  have hv2 : v^2 ≤ (s.im/4)^2 := by nlinarith [sq_abs v, abs_nonneg v]
  have hu : ‖saddleDisplacement a s L v‖ ≤ s.im/2 := by
    nlinarith [norm_nonneg (saddleDisplacement a s L v)]
  have hr : 0 ≤ s.re+s.im/2 := by have := (abs_le.mp hs).1; linarith
  have hrat := norm_xiGamma_linearRatio_le hr hy hu
  rw [centeredKernel_factorization ha, norm_mul, Complex.norm_exp, centeredGaussian_re ha]
  apply (mul_le_mul_of_nonneg_right hrat (Real.exp_pos _).le).trans
  simp only [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hur : ‖saddleDisplacement a s L v‖^2 ≤ 8*a^2*L^2+2*(M+2)^2+v^2 := by
    rw [hsq]
    nlinarith [sq_nonneg (2*a*L-saddleOffset a s L)]
  have hy1 : 1 ≤ s.im := by linarith
  have hlocal : 9*‖saddleDisplacement a s L v‖^2/(4*s.im) ≤
      a*L^2/4+9*(M+2)^2/2+v^2/(8*a) := by
    have h1 : 9*(8*a^2*L^2)/(4*s.im) ≤ a*L^2/4 := by
      apply (div_le_iff₀ (show 0 < 4*s.im by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hya (show 0 ≤ a*L^2 by positivity)]
    have h2 : 9*(2*(M+2)^2)/(4*s.im) ≤ 9*(M+2)^2/2 := by
      apply (div_le_iff₀ (show 0 < 4*s.im by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hy1 (sq_nonneg (M+2))]
    have h3 : 9*v^2/(4*s.im) ≤ v^2/(8*a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hya (sq_nonneg v)]
    calc
      _ ≤ 9*(8*a^2*L^2+2*(M+2)^2+v^2)/(4*s.im) := by gcongr
      _ ≤ _ := by rw [mul_add, mul_add, add_div, add_div]; linarith
  have hML : -s.re*L ≤ a*L^2/4+M^2/a := by
    have h := (abs_le.mp hs).1
    have hx : -s.re*L ≤ M*L := by nlinarith
    apply hx.trans
    apply (mul_le_mul_iff_right₀ ha).mp
    field_simp
    nlinarith [sq_nonneg (a*L-2*M)]
  have he2 : (saddleOffset a s L)^2/(4*a) ≤ (M+2)^2/(4*a) := by gcongr
  ring_nf at hlocal hML he2 ⊢
  linarith

set_option maxHeartbeats 1200000 in
theorem centeredKernel_coarse_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 2 ≤ s.im → 2*Real.pi ≤ s.im →
      ∀ L v : ℝ, 0 ≤ L → ‖centeredKernel a s L v‖ ≤
        C*Real.exp ((Real.pi/2+1)*s.im-a*L^2/2-v^2/(16*a)) := by
  obtain ⟨B, hB, hb⟩ := norm_xiGamma_le_exp_sq (1/(32*a)) (by positivity)
  obtain ⟨G, hG, hg⟩ := norm_inv_xiGamma_le_exp_on_strip M hM
  let D := M+2
  let F := D^2/(16*a)+D^2/(4*a)+a*Real.pi^2/2+M^2/a
  refine ⟨B*G*(6*(1+1/(1/(16*a))))*Real.exp F, by dsimp [F]; positivity, ?_⟩
  intro s hs hy hypi L v hL
  have hyp : 0 < s.im := by linarith
  have he0 := saddleOffset_nonneg a s L
  have heD := saddleOffset_le ha hM hs hL
  have hzre : 2 ≤ (s+saddleDisplacement a s L v).re := by rw [saddleLine_re]; exact le_max_left _ _
  have hzup : (s+saddleDisplacement a s L v).re ≤ 2*a*L+D := by
    rw [saddleLine_re]
    apply max_le
    · dsimp [D]; nlinarith [mul_nonneg ha.le hL]
    · dsimp [D]; have := (abs_le.mp hs).2; linarith
  have hzsq : (s+saddleDisplacement a s L v).re^2 ≤ 8*a^2*L^2+2*D^2 := by
    have hD : 0 ≤ D := by dsimp [D]; linarith
    nlinarith [sq_nonneg (2*a*L-D)]
  have hxi := hb (s+saddleDisplacement a s L v) hzre
  have hinv := hg s hs hy
  have him : (s+saddleDisplacement a s L v).im = s.im+v := by rw [add_im, saddleDisplacement_im]
  rw [him] at hxi
  have hn : 2*Real.pi ≤ ‖s‖ := hypi.trans ((le_abs_self _).trans (Complex.abs_im_le_norm s))
  have hl : 0 ≤ (Complex.log (s/(2*Real.pi))).re := by
    rw [Complex.log_re]
    apply Real.log_nonneg
    rw [norm_div]
    have hp : ‖(2 : ℂ)*(Real.pi : ℂ)‖ = 2*Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [hp]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hn)
  have htheta : (Complex.log (s/(2*Real.pi))).im^2 ≤ Real.pi^2 := by
    have h := Complex.abs_arg_le_pi (s/(2*Real.pi))
    rw [← Complex.log_im] at h
    nlinarith [sq_abs (Complex.log (s/(2*Real.pi))).im, abs_nonneg (Complex.log (s/(2*Real.pi))).im, Real.pi_pos]
  have ht : (Complex.log (s/(2*Real.pi))).im*v/2 ≤ v^2/(8*a)+a*Real.pi^2/2 := by
    have hθ : (Complex.log (s/(2*Real.pi))).im*v/2 ≤
        v^2/(8*a)+a*(Complex.log (s/(2*Real.pi))).im^2/2 := by
      apply (mul_le_mul_iff_right₀ ha).mp
      field_simp
      nlinarith [sq_nonneg (v-2*a*(Complex.log (s/(2*Real.pi))).im)]
    calc
      _ ≤ v^2/(8*a)+a*(Complex.log (s/(2*Real.pi))).im^2/2 := hθ
      _ ≤ _ := by gcongr
  have hdiscard : 0 ≤ (a*L+saddleOffset a s L/2)*(Complex.log (s/(2*Real.pi))).re := by positivity
  have he2 : (saddleOffset a s L)^2/(4*a) ≤ D^2/(4*a) := by dsimp [D]; gcongr
  have hsig : (1/(32*a))*(s+saddleDisplacement a s L v).re^2 ≤ a*L^2/4+D^2/(16*a) := by
    calc
      _ ≤ (1/(32*a))*(8*a^2*L^2+2*D^2) := by gcongr
      _ = _ := by field_simp; ring
  have hML : -s.re*L ≤ a*L^2/4+M^2/a := by
    have hx : -s.re*L ≤ M*L := by have := (abs_le.mp hs).1; nlinarith
    apply hx.trans
    apply (mul_le_mul_iff_right₀ ha).mp
    field_simp
    nlinarith [sq_nonneg (a*L-2*M)]
  have hpoly : 1+(s.im+v)^2 ≤ 6*(1+1/(1/(16*a)))*Real.exp (s.im+v^2/(16*a)) := by
    have hp : 1+(s.im+v)^2 ≤ 2*(1+s.im^2)*(1+v^2) := by
      nlinarith [sq_nonneg (s.im-v), mul_nonneg (sq_nonneg s.im) (sq_nonneg v)]
    have hp' : 1+s.im^2 ≤ 3*Real.exp s.im := by
      have h1 := Real.one_le_exp hyp.le
      have h2 := Real.pow_div_factorial_le_exp s.im hyp.le 2
      norm_num at h2
      linarith
    have hv := one_add_sq_le_mul_exp (1/(16*a)) (by positivity) v
    calc
      _ ≤ 2*(3*Real.exp s.im)*((1+1/(1/(16*a)))*Real.exp ((1/(16*a))*v^2)) := by
        apply hp.trans
        gcongr
      _ = _ := by
        rw [show (1/(16*a))*v^2 = v^2/(16*a) by ring, Real.exp_add]
        ring
  rw [centeredKernel_norm_eq ha]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul hxi hinv (norm_nonneg _) (by positivity)) (Real.exp_pos _).le).trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hB.le) (Real.exp_pos _).le)
    (show 0 ≤ G*Real.exp (Real.pi*s.im/2) by positivity)) (Real.exp_pos _).le).trans
  have hE : (1/(32*a))*(s+saddleDisplacement a s L v).re^2 +
      (-a*L^2-s.re*L+(saddleOffset a s L)^2/(4*a)-v^2/(4*a)-
        (a*L+saddleOffset a s L/2)*(Complex.log (s/(2*Real.pi))).re+
        (Complex.log (s/(2*Real.pi))).im*v/2) ≤ F-a*L^2/2-v^2/(8*a) := by
    dsimp [F]
    simp only [add_re] at hsig ⊢
    ring_nf at ht hsig hML he2 hdiscard ⊢
    linarith
  have he :
      B*(6*(1+1/(1/(16*a)))*Real.exp (s.im+v^2/(16*a)))*
          Real.exp ((1/(32*a))*(s+saddleDisplacement a s L v).re^2)*
        (G*Real.exp (Real.pi*s.im/2))*
        Real.exp (-a*L^2-s.re*L+(saddleOffset a s L)^2/(4*a)-v^2/(4*a)-
          (a*L+saddleOffset a s L/2)*(Complex.log (s/(2*Real.pi))).re+
          (Complex.log (s/(2*Real.pi))).im*v/2) =
      (B*G*(6*(1+1/(1/(16*a)))))*Real.exp
        (s.im+v^2/(16*a)+Real.pi*s.im/2 +
          ((1/(32*a))*(s+saddleDisplacement a s L v).re^2+
          (-a*L^2-s.re*L+(saddleOffset a s L)^2/(4*a)-v^2/(4*a)-
          (a*L+saddleOffset a s L/2)*(Complex.log (s/(2*Real.pi))).re+
          (Complex.log (s/(2*Real.pi))).im*v/2))) := by
    simp only [Real.exp_add]
    ring
  rw [he]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  ring_nf at hE ⊢
  linarith

set_option maxHeartbeats 800000 in
/-- One integrable and summable envelope, uniform simultaneously in height,
strip coordinate, every nonnegative logarithmic index, and contour variable. -/
theorem centeredKernel_joint_majorant {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ s : ℂ, |s.re| ≤ M → Y ≤ s.im →
      ∀ L v : ℝ, 0 ≤ L → ‖centeredKernel a s L v‖ ≤
        C*Real.exp (-a*L^2/4)*Real.exp (-v^2/(32*a)) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := centeredKernel_local_bound ha hM
  obtain ⟨C₂, hC₂, hb₂⟩ := centeredKernel_coarse_bound ha hM
  let c := Real.pi/2+1
  have hc : 0 < c := by dsimp [c]; positivity
  let Y := 4+2*Real.pi+2*M+8*(M+2)+72*a+1024*a*c
  have hY : 0 < Y := by dsimp [Y]; positivity
  refine ⟨max C₁ C₂, Y, lt_of_lt_of_le hC₁ (le_max_left _ _), hY, ?_⟩
  intro s hs hy L v hL
  have hy4 : 4 ≤ s.im := by dsimp [Y] at hy; nlinarith [Real.pi_pos, mul_pos ha hc]
  have hyp : 0 < s.im := by linarith
  have hyπ : 2*Real.pi ≤ s.im := by dsimp [Y] at hy; nlinarith [mul_pos ha hc]
  have hyM : 2*M ≤ s.im := by dsimp [Y] at hy; nlinarith [Real.pi_pos, mul_pos ha hc]
  have hyD : 8*(M+2) ≤ s.im := by dsimp [Y] at hy; nlinarith [Real.pi_pos, mul_pos ha hc]
  have hya : 72*a ≤ s.im := by dsimp [Y] at hy; nlinarith [Real.pi_pos, mul_pos ha hc]
  have hybig : 1024*a*c ≤ s.im := by dsimp [Y] at hy; nlinarith [Real.pi_pos]
  have hbig := mul_le_mul_of_nonneg_right hybig hyp.le
  rw [mul_assoc, ← Real.exp_add]
  by_cases hsmall : L ≤ s.im/(16*a)
  · by_cases hnear : |v| ≤ s.im/4
    · apply (hb₁ s hs hy4 hyM hyD hya L v hL hsmall hnear).trans
      apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left _ _)))
      apply Real.exp_le_exp.mpr
      have hLv : 0 ≤ a*L^2 := by positivity
      have hv : 0 ≤ v^2/a := by positivity
      ring_nf at hv ⊢
      nlinarith
    · have hv : s.im/4 ≤ |v| := le_of_lt (lt_of_not_ge hnear)
      have hv2 : s.im^2 ≤ 16*v^2 := by nlinarith [sq_abs v, abs_nonneg v]
      have hcost : c*s.im ≤ v^2/(32*a) := by
        apply (le_div_iff₀ (show 0 < 32*a by positivity)).mpr
        nlinarith
      apply (hb₂ s hs (by linarith) hyπ L v hL).trans
      apply mul_le_mul (le_max_right _ _) _ (Real.exp_pos _).le (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left _ _)))
      apply Real.exp_le_exp.mpr
      change c*s.im-a*L^2/2-v^2/(16*a) ≤ -a*L^2/4+-v^2/(32*a)
      have hLv : 0 ≤ a*L^2 := by positivity
      ring_nf at hcost ⊢
      nlinarith
  · have hlarge : s.im < L*(16*a) := (div_lt_iff₀ (show 0 < 16*a by positivity)).mp (lt_of_not_ge hsmall)
    have hsquare : s.im^2 ≤ 256*a^2*L^2 := by
      nlinarith [mul_nonneg ha.le hL]
    have hcost : c*s.im ≤ a*L^2/4 := by
      apply (mul_le_mul_iff_left₀ ha).mp
      nlinarith
    apply (hb₂ s hs (by linarith) hyπ L v hL).trans
    apply mul_le_mul (le_max_right _ _) _ (Real.exp_pos _).le (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left _ _)))
    apply Real.exp_le_exp.mpr
    change c*s.im-a*L^2/2-v^2/(16*a) ≤ -a*L^2/4+-v^2/(32*a)
    have hv : 0 ≤ v^2/a := by positivity
    ring_nf at hcost hv ⊢
    linarith

end LeanCert.Analysis.DBN
