import LeanCert.Analysis.DBN.HeatKernel

/-!
# A four-point obstruction in the DBN kernel

The weights at squared arguments 0, 1, 4, 9 cancel constants, quadratics,
and quartics. This strict inequality is incompatible with the corresponding
four-point inequality for Gaussian-regularized real-root products.
All estimates here concern the actual defining series.
-/
namespace LeanCert.Analysis.DBN

/-- A deliberately coarse lower bound from the first positive summand. -/
theorem Phi_lower_exp {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-4 * Real.exp (4*u)) ≤ Phi u := by
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  have he : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by positivity)
  have he5 : 1 ≤ Real.exp (5*u) := Real.one_le_exp (by positivity)
  have h9 : Real.exp (9*u) = Real.exp (4*u) * Real.exp (5*u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc : 1 ≤ 2 * Real.pi^2 * Real.exp (9*u) -
      3 * Real.pi * Real.exp (5*u) := by
    rw [h9]
    have hcoef : 1 ≤ 2 * Real.pi^2 * Real.exp (4*u) - 3 * Real.pi := by
      nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg Real.pi)]
    nlinarith [mul_le_mul_of_nonneg_left hcoef (Real.exp_pos (5*u)).le]
  have hterm : Real.exp (-4*Real.exp (4*u)) ≤ kernelTerm u 0 := by
    unfold kernelTerm
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one]
    calc
      Real.exp (-4 * Real.exp (4*u)) ≤ Real.exp (-Real.pi * Real.exp (4*u)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.exp_pos (4*u)])
      _ ≤ (2 * Real.pi^2 * Real.exp (9*u) - 3 * Real.pi * Real.exp (5*u)) *
          Real.exp (-Real.pi * Real.exp (4*u)) := by
        nlinarith [Real.exp_pos (-Real.pi * Real.exp (4*u))]
  exact hterm.trans ((kernel_summable u).le_tsum 0 (fun n _ => (kernelTerm_pos hu n).le))

theorem Phi_upper_exp {u : ℝ} (hu : 0 ≤ u) :
    Phi u ≤ Real.exp (44 + u - Real.exp (4*u)) := by
  have h := Phi_bound_nonneg hu
  rw [Real.norm_eq_abs, abs_of_pos (Phi_pos hu)] at h
  apply h.trans
  calc
    44 * Real.exp (u-kernelScale u) ≤
        Real.exp 44 * Real.exp (u-Real.exp (4*u)) := by
      apply mul_le_mul
      · linarith [Real.add_one_le_exp 44]
      · exact Real.exp_le_exp.mpr (by linarith [kernelScale_ge_exp (u := u)])
      · exact (Real.exp_pos _).le
      · exact (Real.exp_pos _).le
    _ = Real.exp (44+u-Real.exp (4*u)) := by rw [← Real.exp_add]; congr 1; ring

/-- The kernel violates the real-root four-point inequality strictly.
No numerical quadrature or native evaluation is used. -/
theorem Phi_four_point_obstruction :
    Phi 3 * (Phi 1)^15 < (Phi 0)^10 * (Phi 2)^6 := by
  have h4 : 32 ≤ Real.exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  have h8 : 100 ≤ Real.exp 8 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have h12 : Real.exp 12 = Real.exp 4 * Real.exp 8 := by
    rw [← Real.exp_add]; norm_num
  have hex : (44+3-Real.exp 12) + 15*(44+1-Real.exp 4) <
      10*(-4) + 6*(-4*Real.exp 8) := by
    rw [h12]
    nlinarith [mul_nonneg (show 0 ≤ Real.exp 4-32 by linarith)
      (show 0 ≤ Real.exp 8 by positivity)]
  calc
    Phi 3 * (Phi 1)^15 ≤
        Real.exp (44+3-Real.exp (4*3)) * (Real.exp (44+1-Real.exp (4*1)))^15 := by
      exact mul_le_mul (Phi_upper_exp (by norm_num))
        (pow_le_pow_left₀ (Phi_pos (by norm_num)).le (Phi_upper_exp (by norm_num)) _)
        (pow_nonneg (Phi_pos (by norm_num)).le _) (Real.exp_pos _).le
    _ = Real.exp ((44+3-Real.exp 12) + 15*(44+1-Real.exp 4)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ < Real.exp (10*(-4) + 6*(-4*Real.exp 8)) := Real.exp_lt_exp.mpr hex
    _ = (Real.exp (-4*Real.exp (4*0)))^10 *
        (Real.exp (-4*Real.exp (4*2)))^6 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ ≤ (Phi 0)^10 * (Phi 2)^6 := by
      exact mul_le_mul
        (pow_le_pow_left₀ (Real.exp_pos _).le (Phi_lower_exp (by norm_num)) _)
        (pow_le_pow_left₀ (Real.exp_pos _).le (Phi_lower_exp (by norm_num)) _)
        (by positivity) (pow_nonneg (Phi_pos (by norm_num)).le _)

end LeanCert.Analysis.DBN
