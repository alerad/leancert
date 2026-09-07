import LeanCert.Analysis.DBN.HeatKernel
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The theta primitive for the DBN integral

This connects the positive-index exponential series to Mathlib's theta kernel.
The symmetrized lift is even, which fixes the nonzero endpoint derivative
of the primitive. No xi integral identity or zero-strip theorem is assumed.
-/

namespace LeanCert.Analysis.DBN
open HurwitzZeta

/-- A summand of the theta primitive, with the same positive-index convention as `Phi`. -/
noncomputable def thetaTerm (u : ℝ) (n : ℕ) : ℝ :=
  Real.exp u * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * Real.exp (4*u))

/-- The theta primitive `exp u * sum (exp (-pi*n^2*exp(4*u)))`. -/
noncomputable def thetaPrimitive (u : ℝ) : ℝ :=
  Real.exp u * (cosKernel 0 (Real.exp (4*u)) - 1) / 2

/-- The full symmetrized theta lift, including the constant theta term. -/
noncomputable def thetaLift (u : ℝ) : ℝ :=
  Real.exp u * cosKernel 0 (Real.exp (4*u))

theorem hasSum_thetaTerm (u : ℝ) : HasSum (thetaTerm u) (thetaPrimitive u) := by
  have h := (hasSum_nat_cosKernel₀ 0 (Real.exp_pos (4*u))).div_const 2
  have h' : HasSum (fun n : ℕ => Real.exp
      (-Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u)))
      ((cosKernel 0 (Real.exp (4*u)) - 1)/2) := by
    simpa using h
  change HasSum (fun n => thetaTerm u n) (thetaPrimitive u)
  simpa [thetaTerm, thetaPrimitive, mul_div_assoc] using h'.mul_left (Real.exp u)

theorem thetaPrimitive_eq_tsum (u : ℝ) : thetaPrimitive u = ∑' n, thetaTerm u n :=
  (hasSum_thetaTerm u).tsum_eq.symm

theorem thetaLift_eq (u : ℝ) : thetaLift u = Real.exp u + 2 * thetaPrimitive u := by
  unfold thetaLift thetaPrimitive
  ring

/-- Theta inversion becomes reflection after the logarithmic change of variables. -/
theorem thetaLift_even (u : ℝ) : thetaLift (-u) = thetaLift u := by
  have h := evenKernel_functional_equation 0 (Real.exp (4*u))
  rw [evenKernel_eq_cosKernel_of_zero] at h
  have hp : Real.exp (4*u) ^ (1/2 : ℝ) = Real.exp (2*u) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hp, one_div, ← Real.exp_neg, one_div, ← Real.exp_neg] at h
  unfold thetaLift
  rw [h]
  have he : Real.exp u * Real.exp (-(2*u)) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, he]
  rw [mul_neg]

private theorem differentiableAt_cosKernel_zero {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (cosKernel 0) x := by
  have h : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ 0 (Complex.I * w))
      (x : ℂ) :=
    (differentiableAt_jacobiTheta₂_snd 0 (by simpa using hx)).comp _
      (differentiableAt_const _ |>.mul differentiableAt_id)
  have he : (fun y : ℝ => (jacobiTheta₂ 0 (Complex.I * (y : ℂ))).re) =
      cosKernel 0 := by
    funext y
    have hh := cosKernel_def 0 y
    simpa using congrArg Complex.re hh.symm
  rw [← he]
  exact h.hasDerivAt.real_of_complex.differentiableAt

theorem differentiable_thetaLift : Differentiable ℝ thetaLift := by
  intro u
  apply Real.differentiableAt_exp.mul
  exact (differentiableAt_cosKernel_zero (Real.exp_pos (4*u))).comp u (by fun_prop)

theorem differentiable_thetaPrimitive : Differentiable ℝ thetaPrimitive := by
  have he : thetaPrimitive = fun u => (thetaLift u - Real.exp u) / 2 := by
    funext u
    rw [thetaLift_eq]
    ring
  rw [he]
  exact (differentiable_thetaLift.sub Real.differentiable_exp).div_const 2

/-- Evenness forces the full lift to have zero derivative at the origin. -/
theorem hasDerivAt_thetaLift_zero : HasDerivAt thetaLift 0 0 := by
  have h := (differentiable_thetaLift 0).hasDerivAt
  have h0 : HasDerivAt thetaLift (deriv thetaLift 0) (-0) := by simpa using h
  have hn := h0.comp 0 (hasDerivAt_neg (0 : ℝ))
  have he : (fun x => thetaLift (-x)) = thetaLift := funext thetaLift_even
  change HasDerivAt (fun x => thetaLift (-x)) (deriv thetaLift 0 * -1) 0 at hn
  rw [he, mul_neg_one] at hn
  have hd := h.unique hn
  have hz : deriv thetaLift 0 = 0 := by linarith
  simpa [hz] using h

/-- The endpoint term needed in the twice-integrated DBN cosine transform. -/
theorem hasDerivAt_thetaPrimitive_zero : HasDerivAt thetaPrimitive (-1/2) 0 := by
  have he : thetaPrimitive = fun u => (thetaLift u - Real.exp u) / 2 := by
    funext u
    rw [thetaLift_eq]
    ring
  rw [he]
  simpa using (hasDerivAt_thetaLift_zero.sub (Real.hasDerivAt_exp 0)).div_const 2

end LeanCert.Analysis.DBN
