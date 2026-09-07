import LeanCert.Analysis.PolynomialDecay
import LeanCert.Analysis.GaussianTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The de Bruijn–Newman kernel, with the n+1 indexing and normalization
used by the downstream definition. No downstream analytic assertions are imported. -/
namespace LeanCert.Analysis.DBN

noncomputable def kernelTerm (u : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi^2 * ((n : ℝ)+1)^4 * Real.exp (9*u) -
    3 * Real.pi * ((n : ℝ)+1)^2 * Real.exp (5*u)) *
    Real.exp (-Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u))

noncomputable def Phi (u : ℝ) : ℝ := ∑' n, kernelTerm u n

/-- Dimensionless Gaussian variable for an individual kernel summand. -/
noncomputable def kernelScale (u : ℝ) : ℝ := Real.pi * Real.exp (4*u) / 2

theorem kernelScale_pos (u : ℝ) : 0 < kernelScale u := by
  unfold kernelScale
  positivity

private theorem term_rewrite (u : ℝ) (n : ℕ) :
    kernelTerm u n =
      (2*(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))^2 -
        3*(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))) * Real.exp u *
        Real.exp (-(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))) := by
  have h9 : Real.exp (9*u) = Real.exp (4*u)^2 * Real.exp u := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have h5 : Real.exp (5*u) = Real.exp (4*u) * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold kernelTerm
  rw [h9, h5]
  simp only [neg_mul]
  ring

/-- The actual signed summand is bounded by a Gaussian, for every real u. -/
theorem kernelTerm_bound (u : ℝ) (n : ℕ) :
    ‖kernelTerm u n‖ ≤ 22 * Real.exp u *
      Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
  let x := Real.pi*((n : ℝ)+1)^2*Real.exp (4*u)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h1 := pow_mul_exp_neg_le x hx 1
  have h2 := pow_mul_exp_neg_le x hx 2
  norm_num at h1 h2
  have hab : |2*x^2-3*x| ≤ 2*x^2+3*x := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x]
  have hh : |2*x^2-3*x| * Real.exp (-x) ≤ 22*Real.exp (-x/2) := by
    have h := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-x)).le
    nlinarith
  rw [term_rewrite]
  change ‖(2*x^2-3*x)*Real.exp u*Real.exp (-x)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos u),
    abs_of_pos (Real.exp_pos (-x))]
  have he : -x/2 = -kernelScale u * ((n : ℝ)+1)^2 := by dsimp [x, kernelScale]; ring
  have h := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [he] at h
  nlinarith

/-- Summability and a cutoff-explicit remainder for the actual Phi series.
The first omitted summand has positive index N+1. -/
theorem kernel_tail (u : ℝ) (N : ℕ) :
    Summable (kernelTerm u) ∧
      ‖Phi u - ∑ n ∈ Finset.range N, kernelTerm u n‖ ≤
        22 * Real.exp u * Real.exp (-kernelScale u * ((N : ℝ)+1)^2) /
          (1 - Real.exp (-kernelScale u * (2*((N : ℝ)+1)+1))) := by
  apply SeriesTail.of_geometric
  · exact (Real.exp_pos _).le
  · rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (kernelScale_pos u)) (by positivity)
  · intro k
    have h := kernelTerm_bound u (k+N)
    have hg := SeriesTail.gaussian_le_geometric (kernelScale u) (kernelScale_pos u).le (N+1) k
    push_cast at h hg ⊢
    have he : (k : ℝ)+(N : ℝ)+1 = (k : ℝ)+((N : ℝ)+1) := by ring
    rw [he] at h
    exact h.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg
        (show 0 ≤ 22*Real.exp u by positivity))

theorem kernel_summable (u : ℝ) : Summable (kernelTerm u) := (kernel_tail u 0).1

theorem kernel_norm_summable (u : ℝ) : Summable (fun n => ‖kernelTerm u n‖) :=
  (kernel_summable u).norm

/-- Explicit envelope of Phi on the whole real line, decaying
super-exponentially as u tends to positive infinity. -/
theorem Phi_bound (u : ℝ) :
    ‖Phi u‖ ≤ 22 * Real.exp u * Real.exp (-kernelScale u) /
      (1 - Real.exp (-3*kernelScale u)) := by
  have h := (kernel_tail u 0).2
  norm_num at h
  simpa only [Real.norm_eq_abs, neg_mul, mul_comm] using h

theorem kernelScale_ge_exp {u : ℝ} : Real.exp (4*u) ≤ kernelScale u := by
  have hp := Real.pi_gt_three
  have he := Real.exp_pos (4*u)
  unfold kernelScale
  nlinarith

theorem kernelScale_ge_one {u : ℝ} (hu : 0 ≤ u) : 1 ≤ kernelScale u :=
  (Real.one_le_exp (by positivity)).trans kernelScale_ge_exp

/-- On the integration half-line the denominator in the series envelope is
uniformly bounded away from zero. -/
theorem Phi_bound_nonneg {u : ℝ} (hu : 0 ≤ u) :
    ‖Phi u‖ ≤ 44 * Real.exp (u - kernelScale u) := by
  have ha := kernelScale_ge_one hu
  have hr : Real.exp (-3*kernelScale u) ≤ 1/2 := by
    rw [neg_mul, Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Real.add_one_le_exp (3*kernelScale u)]
  have hd : 0 < 1 - Real.exp (-3*kernelScale u) := by linarith
  apply (Phi_bound u).trans
  apply (div_le_iff₀ hd).mpr
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
  have hn : 0 ≤ Real.exp u * Real.exp (-kernelScale u) := by positivity
  nlinarith [mul_nonneg hn (show 0 ≤ 1/2 - Real.exp (-3*kernelScale u) by linarith)]

/-- Measurability of the actual series, not an assumed kernel regularity fact. -/
theorem measurable_Phi : Measurable Phi := by
  apply Measurable.tsum
  intro n
  unfold kernelTerm
  fun_prop

/-- Every summand of the actual kernel is positive on the integration domain. -/
theorem kernelTerm_pos {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 < kernelTerm u n := by
  rw [term_rewrite]
  have hn : 1 ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by positivity)
  have hx : 3 < Real.pi*((n : ℝ)+1)^2*Real.exp (4*u) := by
    have h := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
    have h' := mul_le_mul_of_nonneg_left he
      (show 0 ≤ Real.pi*((n : ℝ)+1)^2 by positivity)
    nlinarith [Real.pi_gt_three]
  apply mul_pos (mul_pos ?_ (Real.exp_pos _)) (Real.exp_pos _)
  nlinarith

/-- In particular, the defining series cannot cancel on the positive half-line. -/
theorem Phi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < Phi u := by
  exact (kernel_summable u).tsum_pos (fun n => (kernelTerm_pos hu n).le) 0 (kernelTerm_pos hu 0)

end LeanCert.Analysis.DBN
