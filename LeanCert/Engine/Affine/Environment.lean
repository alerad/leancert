/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalAffine

/-!
# Affine environments for rational boxes

This module supplies the semantic bridge from a rational box to the correlated
affine environment built by `toAffineEnv`.  It belongs to interval evaluation,
not global optimization: every real point represented by the box has a valid
noise assignment for the generated affine forms.
-/

namespace LeanCert.Engine

open LeanCert.Core
open LeanCert.Engine.Affine

private theorem linearSum_ofFn_zero {n : Nat} (eps : Fin n → ℝ) :
    AffineForm.linearSum (List.ofFn (fun _ : Fin n => (0 : ℚ))) (List.ofFn eps) = 0 := by
  unfold AffineForm.linearSum
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.zipWith_cons_cons, Rat.cast_zero, zero_mul, List.sum_cons,
      zero_add]
    exact ih (fun i => eps i.succ)

private theorem linearSum_ofFn_basis {n : Nat} (idx : Nat) (rad : ℚ) (eps : Fin n → ℝ) :
    AffineForm.linearSum
      (List.ofFn (fun i : Fin n => if i.val = idx then rad else 0))
      (List.ofFn eps)
      = (rad : ℝ) * (if h : idx < n then eps ⟨idx, h⟩ else 0) := by
  unfold AffineForm.linearSum
  induction n generalizing idx with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.zipWith_cons_cons, List.sum_cons, Fin.val_zero]
    cases idx with
    | zero =>
      simp only [↓reduceDIte, Nat.zero_lt_succ, Fin.mk_zero]
      have hcoeffs : (List.ofFn (fun i : Fin n => if i.succ.val = 0 then rad else 0)) =
          (List.ofFn (fun _ : Fin n => (0 : ℚ))) := by
        apply List.ext_getElem <;> simp
      have htail : (List.zipWith (fun (c : ℚ) e => (c : ℝ) * e)
          (List.ofFn (fun i : Fin n => if i.succ.val = 0 then rad else 0))
          (List.ofFn (fun i => eps i.succ))).sum = 0 := by
        simp only [hcoeffs]
        exact linearSum_ofFn_zero (fun i => eps i.succ)
      simp only [htail, add_zero, ↓reduceIte]
    | succ idx' =>
      have hne : ¬(0 = idx' + 1) := Nat.zero_ne_add_one idx'
      simp only [hne, ↓reduceIte, Rat.cast_zero, zero_mul, zero_add, Nat.succ_lt_succ_iff]
      have hcoeffs :
          (List.ofFn (fun i : Fin n => if i.succ.val = Nat.succ idx' then rad else 0)) =
            (List.ofFn (fun i : Fin n => if i.val = idx' then rad else 0)) := by
        apply List.ext_getElem
        · simp
        · intro k h1 h2
          simp only [List.getElem_ofFn, Fin.val_succ, Nat.succ_eq_add_one,
            Nat.add_right_cancel_iff]
      simp only [hcoeffs]
      have hrec := ih idx' (fun i => eps i.succ)
      rw [hrec]
      by_cases hidx : idx' < n
      · simp only [hidx, ↓reduceDIte, Fin.succ_mk]
      · simp only [hidx, ↓reduceDIte]

private theorem validNoise_ofFn {n : Nat} (f : Fin n → ℝ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) :
    AffineForm.validNoise (List.ofFn f) := by
  intro e he
  simp only [List.mem_ofFn] at he
  obtain ⟨i, rfl⟩ := he
  exact hf i

private lemma abs_sub_mid_le_rad {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    |x - ((I.lo + I.hi) / 2 : ℚ)| ≤ ((I.hi - I.lo) / 2 : ℚ) := by
  have hx' : (I.lo : ℝ) ≤ x ∧ x ≤ I.hi := by
    simpa [IntervalRat.mem_def] using hx
  rw [abs_le]
  constructor
  · calc -((((I.hi : ℚ) - I.lo) / 2 : ℚ) : ℝ)
        = (I.lo : ℝ) - ((I.lo : ℝ) + I.hi) / 2 := by push_cast; ring
      _ ≤ x - ((I.lo : ℝ) + I.hi) / 2 := by linarith [hx'.1]
      _ = x - ((((I.lo : ℚ) + I.hi) / 2 : ℚ) : ℝ) := by push_cast; ring
  · calc x - ((((I.lo : ℚ) + I.hi) / 2 : ℚ) : ℝ)
        = x - ((I.lo : ℝ) + I.hi) / 2 := by push_cast; ring
      _ ≤ (I.hi : ℝ) - ((I.lo : ℝ) + I.hi) / 2 := by linarith [hx'.2]
      _ = ((((I.hi : ℚ) - I.lo) / 2 : ℚ) : ℝ) := by push_cast; ring

/-- Every real point of a rational box has the standard affine-noise
representation used by `toAffineEnv`. -/
theorem exists_noise_toAffineEnv (box : List IntervalRat) (rho : Nat → ℝ)
    (hrho : ∀ i (hi : i < box.length), rho i ∈ box[i]'hi)
    (hzero : ∀ i, i ≥ box.length → rho i = 0) :
    ∃ eps : AffineForm.NoiseAssignment,
      AffineForm.validNoise eps ∧ envMemAffine rho (toAffineEnv box) eps := by
  let eps : AffineForm.NoiseAssignment := List.ofFn (fun i : Fin box.length =>
    let I := box.getD i.val (IntervalRat.singleton 0)
    let mid := ((I.lo + I.hi) / 2 : ℚ)
    let rad := ((I.hi - I.lo) / 2 : ℚ)
    if hr : (rad : ℝ) = 0 then 0 else (rho i.val - mid) / rad)
  have hvalid : AffineForm.validNoise eps := by
    apply validNoise_ofFn
    intro ⟨i, hi⟩
    simp only
    set I := box.getD i (IntervalRat.singleton 0)
    set mid := ((I.lo + I.hi) / 2 : ℚ)
    set rad := ((I.hi - I.lo) / 2 : ℚ)
    split_ifs with hrad
    · exact ⟨by linarith, by linarith⟩
    · have hrhoi : rho i ∈ I := by
        have h := hrho i hi
        simpa [I, List.getD, List.getElem?_eq_getElem hi, Option.getD] using h
      have habs := abs_sub_mid_le_rad hrhoi
      have hrad_nonneg : (0 : ℝ) ≤ rad := by
        have hI := I.le
        have hq : (0 : ℚ) ≤ (I.hi - I.lo) / 2 := by linarith
        exact_mod_cast hq
      have hrad_pos : (0 : ℝ) < rad := lt_of_le_of_ne hrad_nonneg (Ne.symm hrad)
      rw [abs_le] at habs
      constructor
      · calc
          -1 = -(rad : ℝ) / rad := by field_simp
          _ ≤ (rho i - mid) / rad :=
            div_le_div_of_nonneg_right habs.1 (le_of_lt hrad_pos)
      · calc
          (rho i - mid) / rad ≤ (rad : ℝ) / rad :=
            div_le_div_of_nonneg_right habs.2 (le_of_lt hrad_pos)
          _ = 1 := by field_simp
  have henv : envMemAffine rho (toAffineEnv box) eps := by
    intro i
    simp only [AffineForm.mem_affine, toAffineEnv]
    set I := box.getD i (IntervalRat.singleton 0)
    set mid := ((I.lo + I.hi) / 2 : ℚ)
    set rad := ((I.hi - I.lo) / 2 : ℚ)
    simp only [AffineForm.ofInterval, AffineForm.evalLinear]
    use 0
    constructor
    · norm_num
    · simp only [add_zero]
      rw [linearSum_ofFn_basis]
      by_cases hi : i < box.length
      · have hI_eq : box.getD i (IntervalRat.singleton 0) = I := rfl
        have hrad_eq : ((I.hi - I.lo) / 2 : ℚ) = rad := rfl
        by_cases hrad : (rad : ℝ) = 0
        · simp only [hI_eq, hrad_eq]
          rw [dif_pos hrad]
          simp only [hrad]
          have hrhoi : rho i ∈ I := by
            have h := hrho i hi
            simpa [I, List.getD, List.getElem?_eq_getElem hi, Option.getD] using h
          have habs := abs_sub_mid_le_rad hrhoi
          rw [abs_le] at habs
          have hle : rho i - mid ≤ 0 := by linarith [habs.2, hrad]
          have hge : 0 ≤ rho i - mid := by linarith [habs.1, hrad]
          linarith
        · simp only [hI_eq, hrad_eq]
          rw [dif_neg hrad, dif_pos hi]
          field_simp [hrad]
          ring
      · have hzeroi : rho i = 0 := hzero i (not_lt.mp hi)
        have hI : I = IntervalRat.singleton 0 := by
          simp [I, List.getElem?_eq_none (not_lt.mp hi), Option.getD]
        simp only [hI, IntervalRat.singleton, hzeroi]
        ring
  exact ⟨eps, hvalid, henv⟩

end LeanCert.Engine
