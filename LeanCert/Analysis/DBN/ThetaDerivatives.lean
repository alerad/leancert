import LeanCert.Analysis.DBN.Theta
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Twice differentiating the actual theta series, with local summable bounds. -/
namespace LeanCert.Analysis.DBN
open Set

noncomputable def thetaTermDeriv (u : ℝ) (n : ℕ) : ℝ :=
  (1 - 4 * (Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u))) * thetaTerm u n

theorem hasDerivAt_thetaTerm (u : ℝ) (n : ℕ) :
    HasDerivAt (fun v => thetaTerm v n) (thetaTermDeriv u n) u := by
  have he := (((hasDerivAt_id u).const_mul 4).exp.const_mul
    (-Real.pi * ((n : ℝ)+1)^2)).exp
  convert! (Real.hasDerivAt_exp u).mul he using 1
  simp only [thetaTerm, thetaTermDeriv, id_eq]
  ring

theorem hasDerivAt_thetaTermDeriv (u : ℝ) (n : ℕ) :
    HasDerivAt (fun v => thetaTermDeriv v n)
      (8 * kernelTerm u n + thetaTerm u n) u := by
  have he := (((hasDerivAt_id u).const_mul 4).exp.const_mul
    (4 * (Real.pi * ((n : ℝ)+1)^2))).const_sub 1
  have h9 : Real.exp (9*u) = Real.exp u * Real.exp (4*u)^2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (5*u) = Real.exp u * Real.exp (4*u) := by
    rw [← Real.exp_add]; congr 1; ring
  convert! he.mul (hasDerivAt_thetaTerm u n) using 1
  · funext v
    simp only [thetaTermDeriv, thetaTerm, Pi.mul_apply, id_eq]
    ring
  · simp only [thetaTermDeriv, thetaTerm, kernelTerm, id_eq, h9, h5]
    ring

theorem thetaTerm_bound (u : ℝ) (n : ℕ) :
    ‖thetaTerm u n‖ ≤ Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
  rw [thetaTerm, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos u).le
  apply Real.exp_le_exp.mpr
  dsimp [kernelScale]
  have h : 0 ≤ Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u) := by positivity
  nlinarith

theorem thetaTermDeriv_bound (u : ℝ) (n : ℕ) :
    ‖thetaTermDeriv u n‖ ≤ 9 * Real.exp u *
      Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
  let x := Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h1 := pow_mul_exp_neg_le x hx 1
  norm_num at h1
  have h0 : Real.exp (-x) ≤ Real.exp (-x/2) := by gcongr; linarith
  have hab : |1-4*x| ≤ 1+4*x := by rw [abs_le]; constructor <;> linarith
  have hh := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-x)).le
  have he : -x/2 = -kernelScale u * ((n : ℝ)+1)^2 := by dsimp [x, kernelScale]; ring
  have hb : |1-4*x| * Real.exp (-x) ≤ 9 * Real.exp (-x/2) := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (Real.exp_pos u).le
  rw [he] at hb'
  have hex : -Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u) = -x := by
    dsimp [x]; ring
  simp only [thetaTermDeriv, thetaTerm, hex]
  change ‖(1-4*x) * (Real.exp u * Real.exp (-x))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  nlinarith

/-- A common envelope on a bounded real interval; the lower endpoint controls Gaussian decay. -/
noncomputable def thetaEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  Real.exp b * Real.exp (-kernelScale a * ((n : ℝ)+1)^2)

theorem summable_thetaEnvelope (a b : ℝ) : Summable (thetaEnvelope a b) := by
  apply (SeriesTail.of_gaussian (thetaEnvelope a b) 0 (Real.exp b) (kernelScale a)
    (Real.exp_pos _).le (kernelScale_pos a) ?_).1
  intro n
  simp only [Nat.add_zero, thetaEnvelope]
  rw [Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos b).le
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (n : ℝ) := by positivity
  nlinarith [kernelScale_pos a]

theorem thetaEnvelope_mono {a b u : ℝ} (ha : a ≤ u) (hb : u ≤ b) (n : ℕ) :
    Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2) ≤ thetaEnvelope a b n := by
  unfold thetaEnvelope kernelScale
  gcongr

private theorem second_bound (u : ℝ) (n : ℕ) :
    ‖8 * kernelTerm u n + thetaTerm u n‖ ≤
      177 * (Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2)) := by
  calc
    _ ≤ ‖8 * kernelTerm u n‖ + ‖thetaTerm u n‖ := norm_add_le _ _
    _ ≤ 8 * (22 * Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2)) +
        Real.exp u * Real.exp (-kernelScale u * ((n : ℝ)+1)^2) := by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
      gcongr
      · exact kernelTerm_bound u n
      · exact thetaTerm_bound u n
    _ = _ := by ring

theorem summable_thetaTermDeriv (u : ℝ) : Summable (thetaTermDeriv u) := by
  apply ((summable_thetaEnvelope u u).mul_left 9).of_norm_bounded
  intro n
  simpa [thetaEnvelope, mul_assoc] using thetaTermDeriv_bound u n

theorem hasDerivAt_thetaPrimitive (u : ℝ) :
    HasDerivAt thetaPrimitive (∑' n, thetaTermDeriv u n) u := by
  have hm : u ∈ Ioo (u-1) (u+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_thetaEnvelope (u-1) (u+1)).mul_left 9) isOpen_Ioo
    (convex_Ioo (u-1) (u+1)).isPreconnected
    (fun n v (_ : v ∈ Ioo (u-1) (u+1)) => hasDerivAt_thetaTerm v n)
    (fun n v (hv : v ∈ Ioo (u-1) (u+1)) =>
      (thetaTermDeriv_bound v n).trans (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (thetaEnvelope_mono hv.1.le hv.2.le n) (by norm_num : (0 : ℝ) ≤ 9)))
    hm (hasSum_thetaTerm u).summable hm
  simpa only [← thetaPrimitive_eq_tsum] using h

theorem deriv_thetaPrimitive (u : ℝ) : deriv thetaPrimitive u = ∑' n, thetaTermDeriv u n :=
  (hasDerivAt_thetaPrimitive u).deriv

/-- The second derivative is the actual, convergent DBN kernel series plus the primitive. -/
theorem hasDerivAt_deriv_thetaPrimitive (u : ℝ) :
    HasDerivAt (deriv thetaPrimitive) (8 * Phi u + thetaPrimitive u) u := by
  have hm : u ∈ Ioo (u-1) (u+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_thetaEnvelope (u-1) (u+1)).mul_left 177) isOpen_Ioo
    (convex_Ioo (u-1) (u+1)).isPreconnected
    (fun n v (_ : v ∈ Ioo (u-1) (u+1)) => hasDerivAt_thetaTermDeriv v n)
    (fun n v (hv : v ∈ Ioo (u-1) (u+1)) =>
      (second_bound v n).trans (mul_le_mul_of_nonneg_left
        (thetaEnvelope_mono hv.1.le hv.2.le n) (by norm_num)))
    hm (summable_thetaTermDeriv u) hm
  have he : deriv thetaPrimitive = fun v => ∑' n, thetaTermDeriv v n :=
    funext deriv_thetaPrimitive
  rw [he]
  convert! h using 1
  rw [((kernel_summable u).mul_left 8).tsum_add (hasSum_thetaTerm u).summable,
    tsum_mul_left, (hasSum_thetaTerm u).tsum_eq]
  rfl

/-- Exact differential identity needed for the twice-integrated cosine transform. -/
theorem Phi_eq_thetaPrimitive_deriv2 (u : ℝ) :
    Phi u = (deriv (deriv thetaPrimitive) u - thetaPrimitive u) / 8 := by
  rw [(hasDerivAt_deriv_thetaPrimitive u).deriv]
  ring

end LeanCert.Analysis.DBN
