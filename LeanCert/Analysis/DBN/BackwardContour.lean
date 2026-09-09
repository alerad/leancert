/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerGeometry
import LeanCert.Analysis.DBN.KernelRegularity
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact Gaussian averaging of the actual heat integral at backward times. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set

private theorem gaussian_exp_integrable (c d : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-(x : ℂ)^2+c*x+d)) := by
  simpa using integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num) c d

private theorem gaussian_exp_integral (c d : ℂ) :
    (∫ x : ℝ, Complex.exp (-(x : ℂ)^2+c*x+d)) =
      (Real.sqrt Real.pi : ℂ)*Complex.exp (d+c^2/4) := by
  have hp : (Real.pi : ℂ)^(1/2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow Real.pi_pos.le (1/2)).symm
  have h := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num) c d
  simp only [neg_one_mul, neg_neg, div_one] at h
  rw [hp] at h
  rw [h]
  congr 2
  ring

private theorem gaussian_cos_integrable (z : ℂ) (c : ℝ) :
    Integrable (fun x : ℝ => (Real.exp (-x^2) : ℂ)*Complex.cos (z+(c*x : ℝ))) := by
  have he (x : ℝ) : (Real.exp (-x^2) : ℂ)*Complex.cos (z+(c*x : ℝ)) =
      (Complex.exp (-(x : ℂ)^2 + ((c : ℂ)*I)*x + z*I) +
       Complex.exp (-(x : ℂ)^2 + (-(c : ℂ)*I)*x + (-z)*I))/2 := by
    simp only [Complex.cos]
    push_cast
    rw [← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> congr 1 <;> ring
  simp only [he]
  exact ((gaussian_exp_integrable _ _).add (gaussian_exp_integrable _ _)).div_const 2

private theorem gaussian_cos_integral (z : ℂ) (c : ℝ) :
    (∫ x : ℝ, (Real.exp (-x^2) : ℂ)*Complex.cos (z+(c*x : ℝ))) =
      (Real.sqrt Real.pi * Real.exp (-c^2/4) : ℝ) * Complex.cos z := by
  have he (x : ℝ) : (Real.exp (-x^2) : ℂ)*Complex.cos (z+(c*x : ℝ)) =
      (Complex.exp (-(x : ℂ)^2 + ((c : ℂ)*I)*x + z*I) +
       Complex.exp (-(x : ℂ)^2 + (-(c : ℂ)*I)*x + (-z)*I))/2 := by
    simp only [Complex.cos]
    push_cast
    rw [← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> congr 1 <;> ring
  simp only [he, integral_div]
  rw [integral_add (gaussian_exp_integrable _ _) (gaussian_exp_integrable _ _),
    gaussian_exp_integral, gaussian_exp_integral]
  have h1 : ((c : ℂ)*I)^2/4 = -(c : ℂ)^2/4 := by rw [mul_pow, I_sq]; ring
  have h2 : (-(c : ℂ)*I)^2/4 = -(c : ℂ)^2/4 := by rw [mul_pow, I_sq]; ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add]
  simp only [Complex.cos, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

private theorem gaussian_heat_joint_integrable (z : ℂ) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => (Real.exp (-p.1^2) : ℂ) *
      heatIntegrand 0 (z+(c*p.1 : ℝ)) p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
  have hm := hg.mul_prod ((hg.integrableOn (s := Ioi (0 : ℝ))).const_mul (heatMajorant 0 z))
  have hp := continuous_Phi
  have hc : Continuous (fun p : ℝ × ℝ => (Real.exp (-p.1^2) : ℂ) *
      heatIntegrand 0 (z+(c*p.1 : ℝ)) p.2) := by unfold heatIntegrand; fun_prop
  apply hm.mono' hc.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (by
    apply measurableSet_le hc.norm.measurable
    fun_prop)).mpr
  apply Filter.Eventually.of_forall
  intro x
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  apply Filter.Eventually.of_forall
  intro u hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := heatIntegrand_bound 0 (z+(c*x : ℝ)) hu.le
  have he : heatMajorant 0 (z+(c*x : ℝ)) = heatMajorant 0 z := by simp [heatMajorant]
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- Exact backward heat evolution as real Gaussian averaging. -/
theorem gaussian_average_H_zero (z : ℂ) (c : ℝ) :
    (∫ x : ℝ, (Real.exp (-x^2) : ℂ)*H 0 (z+(c*x : ℝ))) =
      (Real.sqrt Real.pi : ℂ)*H (-c^2/4) z := by
  have hj := gaussian_heat_joint_integrable z c
  have he (u : ℝ) :
      (∫ x : ℝ, (Real.exp (-x^2) : ℂ)*heatIntegrand 0 (z+(c*x : ℝ)) u) =
        (Real.sqrt Real.pi : ℂ)*heatIntegrand (-c^2/4) z u := by
    have heq (x : ℝ) : (Real.exp (-x^2) : ℂ)*heatIntegrand 0 (z+(c*x : ℝ)) u =
        (Phi u : ℂ)*((Real.exp (-x^2) : ℂ)*Complex.cos (z*(u : ℂ)+(c*u*x : ℝ))) := by
      simp only [heatIntegrand, zero_mul, Real.exp_zero, one_mul]
      have harg : (z+(c*x : ℝ))*(u : ℂ) = z*(u : ℂ)+(c*u*x : ℝ) := by
        push_cast
        ring
      rw [harg]
      ring
    simp only [heq, integral_const_mul]
    rw [show (fun x : ℝ => (Real.exp (-x^2) : ℂ)*Complex.cos (z*(u : ℂ)+(c*u*x : ℝ))) =
        (fun x : ℝ => (Real.exp (-x^2) : ℂ)*Complex.cos (z*(u : ℂ)+((c*u)*x : ℝ))) from rfl,
      gaussian_cos_integral]
    unfold heatIntegrand
    have hex : -(c*u)^2/4 = (-c^2/4)*u^2 := by ring
    rw [hex]
    push_cast
    ring
  unfold H
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hj]
  simp_rw [he]

/-- Absolute integrability of the Gaussian representation, not a totalized integral identity. -/
theorem gaussian_average_H_zero_integrable (z : ℂ) (c : ℝ) :
    Integrable (fun x : ℝ => (Real.exp (-x^2) : ℂ)*H 0 (z+(c*x : ℝ))) := by
  have h := (gaussian_heat_joint_integrable z c).integral_prod_left
  simpa only [H, integral_const_mul] using h

/-- Gaussian with a complex center, used to obtain any fixed vertical contour. -/
noncomputable def gaussianShift (q : ℂ) (x : ℝ) : ℂ := Complex.exp (-((x : ℂ)-q)^2)

theorem gaussianShift_integrable (q : ℂ) : Integrable (gaussianShift q) := by
  have he : gaussianShift q = fun x : ℝ => Complex.exp (-(x : ℂ)^2+(2*q)*x+(-q^2)) := by
    funext x
    unfold gaussianShift
    congr 1
    ring
  rw [he]
  exact gaussian_exp_integrable _ _

private theorem gaussianShift_cos_eq (q z : ℂ) (c x : ℝ) :
    gaussianShift q x * Complex.cos (z+(c*x : ℝ)) =
      (Complex.exp (-(x : ℂ)^2 + (2*q+(c : ℂ)*I)*x + (-q^2+z*I)) +
       Complex.exp (-(x : ℂ)^2 + (2*q-(c : ℂ)*I)*x + (-q^2-z*I)))/2 := by
  unfold gaussianShift Complex.cos
  push_cast
  rw [← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> congr 1 <;> ring

theorem gaussianShift_cos_integral (q z : ℂ) (c : ℝ) :
    (∫ x : ℝ, gaussianShift q x * Complex.cos (z+(c*x : ℝ))) =
      (Real.sqrt Real.pi * Real.exp (-c^2/4) : ℝ) * Complex.cos (z+(c : ℂ)*q) := by
  simp only [gaussianShift_cos_eq, integral_div]
  rw [integral_add (gaussian_exp_integrable _ _) (gaussian_exp_integrable _ _),
    gaussian_exp_integral, gaussian_exp_integral]
  have h1 : -q^2+z*I+(2*q+(c : ℂ)*I)^2/4 = -(c : ℂ)^2/4+(z+(c : ℂ)*q)*I := by
    linear_combination (c : ℂ)^2/4 * I_sq
  have h2 : -q^2-z*I+(2*q-(c : ℂ)*I)^2/4 = -(c : ℂ)^2/4-(z+(c : ℂ)*q)*I := by
    linear_combination (c : ℂ)^2/4 * I_sq
  rw [h1, h2, sub_eq_add_neg, Complex.exp_add, Complex.exp_add]
  simp only [Complex.cos, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [neg_mul]
  ring

theorem gaussianShift_heat_joint_integrable (q z : ℂ) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => gaussianShift q p.1 *
      heatIntegrand 0 (z+(c*p.1 : ℝ)) p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-u^2)) := by
    simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
  have hm := (gaussianShift_integrable q).norm.mul_prod
    ((hg.integrableOn (s := Ioi (0 : ℝ))).const_mul (heatMajorant 0 z))
  have hp := continuous_Phi
  have hc : Continuous (fun p : ℝ × ℝ => gaussianShift q p.1 *
      heatIntegrand 0 (z+(c*p.1 : ℝ)) p.2) := by
    unfold gaussianShift heatIntegrand
    fun_prop
  apply hm.mono' hc.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (by
    apply measurableSet_le hc.norm.measurable
    unfold gaussianShift
    fun_prop)).mpr
  apply Filter.Eventually.of_forall
  intro x
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  apply Filter.Eventually.of_forall
  intro u hu
  rw [norm_mul]
  have h := heatIntegrand_bound 0 (z+(c*x : ℝ)) hu.le
  have he : heatMajorant 0 (z+(c*x : ℝ)) = heatMajorant 0 z := by simp [heatMajorant]
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- Complex-centered Gaussian averaging gives the actual backward heat value. -/
theorem gaussianShift_average_H_zero (q z : ℂ) (c : ℝ) :
    (∫ x : ℝ, gaussianShift q x * H 0 (z+(c*x : ℝ))) =
      (Real.sqrt Real.pi : ℂ)*H (-c^2/4) (z+(c : ℂ)*q) := by
  have hj := gaussianShift_heat_joint_integrable q z c
  have he (u : ℝ) :
      (∫ x : ℝ, gaussianShift q x * heatIntegrand 0 (z+(c*x : ℝ)) u) =
        (Real.sqrt Real.pi : ℂ)*heatIntegrand (-c^2/4) (z+(c : ℂ)*q) u := by
    have heq (x : ℝ) : gaussianShift q x * heatIntegrand 0 (z+(c*x : ℝ)) u =
        (Phi u : ℂ)*(gaussianShift q x * Complex.cos (z*(u : ℂ)+(c*u*x : ℝ))) := by
      simp only [heatIntegrand, zero_mul, Real.exp_zero, one_mul]
      have harg : (z+(c*x : ℝ))*(u : ℂ) = z*(u : ℂ)+(c*u*x : ℝ) := by push_cast; ring
      rw [harg]
      ring
    simp only [heq, integral_const_mul]
    rw [gaussianShift_cos_integral]
    unfold heatIntegrand
    have hex : -(c*u)^2/4 = (-c^2/4)*u^2 := by ring
    have harg : z*(u : ℂ)+(c*u : ℝ)*q = (z+(c : ℂ)*q)*(u : ℂ) := by push_cast; ring
    rw [hex, harg]
    push_cast
    ring
  unfold H
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hj]
  simp_rw [he]

theorem gaussianShift_average_H_zero_integrable (q z : ℂ) (c : ℝ) :
    Integrable (fun x : ℝ => gaussianShift q x * H 0 (z+(c*x : ℝ))) := by
  have h := (gaussianShift_heat_joint_integrable q z c).integral_prod_left
  simpa only [H, integral_const_mul] using h

/-- A real-parameter vertical Gaussian integral. Its contour has real part σ. -/
noncomputable def verticalGaussianIntegrand (b σ : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((s-((σ : ℂ)+(Real.sqrt b*x : ℝ)*I))^2/(b : ℂ)) *
    riemannXi ((σ : ℂ)+(Real.sqrt b*x : ℝ)*I)

private theorem verticalGaussianIntegrand_eq (b : ℝ) (hb : 0 < b) (σ : ℝ) (s : ℂ) :
    let c : ℝ := 2*Real.sqrt b
    let z := heatCoordinate (σ : ℂ)
    let q := (heatCoordinate s-z)/(c : ℂ)
    ∀ x : ℝ, verticalGaussianIntegrand b σ s x =
      8*(gaussianShift q x * H 0 (z+(c*x : ℝ))) := by
  let c : ℝ := 2*Real.sqrt b
  let z := heatCoordinate (σ : ℂ)
  let q := (heatCoordinate s-z)/(c : ℂ)
  have hsq : (Real.sqrt b : ℂ)^2 = (b : ℂ) := by
    exact_mod_cast Real.sq_sqrt hb.le
  have harg (x : ℝ) : (1/2 : ℂ)+I*(z+(c*x : ℝ))/2 =
      (σ : ℂ)+(Real.sqrt b*x : ℝ)*I := by
    dsimp [z, c, heatCoordinate]
    push_cast
    field_simp
    ring
  have hkernel (x : ℝ) : gaussianShift q x =
      Complex.exp ((s-((σ : ℂ)+(Real.sqrt b*x : ℝ)*I))^2/(b : ℂ)) := by
    unfold gaussianShift
    congr 1
    dsimp [q, z, c, heatCoordinate]
    push_cast
    rw [← hsq]
    field_simp [show (Real.sqrt b : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr hb).ne']
    ring_nf
    simp only [I_sq, I_pow_three, I_pow_four]
    ring

  change ∀ x : ℝ, verticalGaussianIntegrand b σ s x =
    8*(gaussianShift q x * H 0 (z+(c*x : ℝ)))
  intro x
  rw [H_zero_eq_riemannXi, harg, hkernel]
  unfold verticalGaussianIntegrand
  ring

/-- Absolute integrability on every fixed vertical line. -/
theorem verticalGaussianIntegral_integrable (b : ℝ) (hb : 0 < b) (σ : ℝ) (s : ℂ) :
    Integrable (verticalGaussianIntegrand b σ s) := by
  change Integrable (fun x => verticalGaussianIntegrand b σ s x)
  simp only [verticalGaussianIntegrand_eq b hb σ s]
  exact (gaussianShift_average_H_zero_integrable _ _ _).const_mul 8

/-- Exact representation on ANY fixed vertical line, including σ=2.
Derived directly by Gaussian/Fubini calculus, avoiding a separate contour
shift and its horizontal-edge limits. The parameter is scaled by sqrt(b). -/
theorem verticalGaussianIntegral (b : ℝ) (hb : 0 < b) (σ : ℝ) (s : ℂ) :
    (∫ x : ℝ, verticalGaussianIntegrand b σ s x) =
      (Real.sqrt Real.pi : ℂ)*xiHeat (-b) s := by
  let c : ℝ := 2*Real.sqrt b
  let z := heatCoordinate (σ : ℂ)
  let q := (heatCoordinate s-z)/(c : ℂ)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have htime : -c^2/4 = -b := by dsimp [c]; nlinarith [Real.sq_sqrt hb.le]
  have hcenter : z+(c : ℂ)*q = heatCoordinate s := by
    dsimp [q]
    field_simp [show (c : ℂ) ≠ 0 by exact_mod_cast hc]
    ring
  have he : ∀ x : ℝ, verticalGaussianIntegrand b σ s x =
      8*(gaussianShift q x * H 0 (z+(c*x : ℝ))) := verticalGaussianIntegrand_eq b hb σ s
  simp only [he, integral_const_mul]
  rw [gaussianShift_average_H_zero, htime, hcenter]
  unfold xiHeat
  ring

end LeanCert.Analysis.DBN
