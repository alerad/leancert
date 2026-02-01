/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.AD
import LeanCert.Engine.RootFinding.Main

/-!
# Root Finding Certificates

These checkers and theorems provide certificate-driven verification for
root existence and uniqueness.

## Main definitions

### Configuration
* `RootConfig` - Configuration for root finding checks
* `NewtonConfig` - Configuration for Newton uniqueness checks

### Boolean Checkers
* `checkSignChange` - Check if expression has a sign change on interval
* `checkNoRoot` - Check if interval definitely has no root
* `checkNewtonContracts` - Check if Newton iteration contracts (noncomputable)
* `checkNewtonContractsCore` - Computable Newton contraction check
* `checkHasRoot` - Check if bisection finds a root (noncomputable)

### Golden Theorems
* `verify_no_root` - Converts boolean check to proof of no root
* `verify_unique_root_newton` - Newton contraction proves unique root
* `verify_unique_root_computable` - Fully computable unique root verification
* `verify_sign_change` - Sign change implies root existence
* `verify_has_root` - Bisection root existence verification
-/

namespace LeanCert.Validity.RootFinding

open LeanCert.Core
open LeanCert.Engine

/-! ### Configuration for root finding certificates -/

/-- Configuration for root-finding checks -/
structure RootConfig where
  /-- Maximum bisection depth -/
  maxDepth : Nat := 20
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr, Inhabited

/-- Configuration for Newton uniqueness checks -/
structure NewtonConfig where
  /-- Number of Newton iterations -/
  iterations : Nat := 5
  /-- Taylor model degree -/
  tmDegree : Nat := 1
  deriving Repr, Inhabited

/-! ### Boolean Checkers for Root Finding -/

/-- Check if expression has a sign change on interval (indicating a root).
    Uses interval arithmetic to check if f(lo) and f(hi) have opposite signs. -/
def checkSignChange (e : Expr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  -- Check domain validity at endpoints
  checkDomainValid1 e (IntervalRat.singleton I.lo) cfg &&
  checkDomainValid1 e (IntervalRat.singleton I.hi) cfg &&
  -- Evaluate f at endpoints
  let f_lo := evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg
  let f_hi := evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg
  -- Opposite signs: f_lo.hi < 0 and f_hi.lo > 0, or f_lo.lo > 0 and f_hi.hi < 0
  ((f_lo.hi < 0 && 0 < f_hi.lo) || (f_hi.hi < 0 && 0 < f_lo.lo))

/-- Check if interval definitely has no root (function has constant sign).
    Returns `true` if the function's interval evaluation doesn't contain 0. -/
def checkNoRoot (e : Expr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && (let fI := evalIntervalCore1 e I cfg; fI.hi < 0 || 0 < fI.lo)

/-! ### Computable Newton Step for Unique Root Verification -/

/-- Computable Newton step using `evalIntervalCore1` and `derivIntervalCore`.

    This is the computable equivalent of `newtonStepSimple`. It performs one
    interval Newton iteration: N(I) = c - f(c)/f'(I) where c = midpoint(I).

    Returns `none` if the derivative interval contains 0 (can't safely divide).
    Returns `some (I ∩ N)` otherwise. -/
def newtonStepCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : Option IntervalRat :=
  let c := I.midpoint
  -- Evaluate f(c) using singleton interval
  let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
  -- Get derivative interval on I
  let dI := derivIntervalCore e I cfg
  -- If derivative interval contains zero, we can't safely divide
  if hzero : IntervalRat.containsZero dI then
    none
  else
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hzero }
    let dInv := IntervalRat.invNonzero dNonzero
    let Q := IntervalRat.mul fc dInv
    let N : IntervalRat :=
      { lo := c - Q.hi
        hi := c - Q.lo
        le := by linarith [Q.le] }
    IntervalRat.intersect I N

/-- Extract structure from newtonStepCore. -/
lemma newtonStepCore_extract (e : Expr) (I N : IntervalRat) (cfg : EvalConfig)
    (hCore : newtonStepCore e I cfg = some N) :
    let c := I.midpoint
    let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
    let dI := derivIntervalCore e I cfg
    ∃ (hdI_nonzero : ¬dI.containsZero),
      let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
      let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
      N.lo = max I.lo (c - Q.hi) ∧ N.hi = min I.hi (c - Q.lo) := by
  -- Unfold the definition of newtonStepCore
  unfold newtonStepCore at hCore
  -- The dite splits on containsZero
  by_cases hzero : (derivIntervalCore e I cfg).containsZero
  · -- If dI contains zero, newtonStepCore returns none, contradiction
    simp only [hzero, ↓reduceDIte, reduceCtorEq] at hCore
  · -- If dI doesn't contain zero, we get an intersection
    simp only [hzero, dite_false] at hCore
    use hzero
    -- hCore : IntervalRat.intersect I ⟨c - Q.hi, c - Q.lo, _⟩ = some N
    simp only [IntervalRat.intersect] at hCore
    split at hCore
    · -- The intersection succeeded
      rename_i hintersect
      simp only [Option.some.injEq] at hCore
      constructor
      · exact congrArg IntervalRat.lo hCore.symm
      · exact congrArg IntervalRat.hi hCore.symm
    · -- The intersection failed, contradiction
      simp only [reduceCtorEq] at hCore

/-- Computable check if Newton iteration contracts.
    Returns `true` if `newtonStepCore` produces N with I.lo < N.lo and N.hi < I.hi.

    This can be used with `native_decide` for unique root verification. -/
def checkNewtonContractsCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : Bool :=
  match newtonStepCore e I cfg with
  | none => false
  | some N => decide (I.lo < N.lo && N.hi < I.hi)

/-- Check if Newton iteration contracts, indicating unique root existence.
    Returns `true` if the Newton step from I gives N ⊂ interior(I).

    Note: This is noncomputable because newtonStepSimple uses derivInterval
    which uses evalInterval (noncomputable). For native_decide, we would need
    a fully computable version using evalIntervalCore. -/
noncomputable def checkNewtonContracts (e : Expr) (I : IntervalRat) (_cfg : NewtonConfig) : Bool :=
  match newtonStepSimple e I 0 with
  | none => false  -- Newton step failed (derivative interval contains 0)
  | some N =>
    -- Check strict contraction: N.lo > I.lo and N.hi < I.hi
    decide (I.lo < N.lo && N.hi < I.hi)

/-! ### Golden Theorems for Root Finding -/

/-- **Golden Theorem for No Root**

    If `checkNoRoot e I cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0`. -/
theorem verify_no_root (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_cert : checkNoRoot e I cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0 := by
  simp only [checkNoRoot, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h_cert
  intro x hx hcontra
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have heval := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at heval
  cases h_cert.2 with
  | inl hhi =>
    -- f's interval hi < 0, so f(x) ≤ hi < 0, contradiction with f(x) = 0
    have hhi_real : ((evalIntervalCore1 e I cfg).hi : ℝ) < 0 := by exact_mod_cast hhi
    have hf_neg : Expr.eval (fun _ => x) e < 0 := lt_of_le_of_lt heval.2 hhi_real
    rw [hcontra] at hf_neg
    exact absurd hf_neg (lt_irrefl 0)
  | inr hlo =>
    -- 0 < f's interval lo, so 0 < lo ≤ f(x), contradiction with f(x) = 0
    have hlo_real : (0 : ℝ) < (evalIntervalCore1 e I cfg).lo := by exact_mod_cast hlo
    have hf_pos : 0 < Expr.eval (fun _ => x) e := lt_of_lt_of_le hlo_real heval.1
    rw [hcontra] at hf_pos
    exact absurd hf_pos (lt_irrefl 0)

/-- **Golden Theorem for Newton Contraction (Unique Root Existence)**

    If `checkNewtonContracts e I cfg = true`, then there exists a unique root in I.

    This theorem requires additional hypotheses that the external checker must verify:
    - The expression is supported
    - The expression uses only variable 0
    - The function is continuous on I -/
theorem verify_unique_root_newton (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkNewtonContracts e I cfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  simp only [checkNewtonContracts] at h_cert
  -- Extract the Newton step result
  split at h_cert
  · -- Newton step returned none
    exact absurd h_cert Bool.false_ne_true
  · -- Newton step returned some N
    rename_i N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
    -- We have contraction: I.lo < N.lo and N.hi < I.hi
    have hContract : N.lo > I.lo ∧ N.hi < I.hi := ⟨h_cert.1, h_cert.2⟩
    -- Apply newton_contraction_unique_root directly
    -- This theorem already proves ∃! x, x ∈ I ∧ ... (uniqueness in I, not just N)
    exact newton_contraction_unique_root e hsupp hvar0 I N (Or.inr hN) hContract hCont

/-! ### Core MVT Lemmas for Newton Contraction Contradiction

These lemmas prove that if Newton contraction holds but f has constant sign at both
endpoints, we get a contradiction via MVT bounds.

Key insight: If f doesn't change sign on I (both endpoints positive or both negative),
then by monotonicity (from nonzero derivative), f has constant sign throughout I.
But Newton contraction requires specific quotient bounds that MVT proves are violated. -/

/-- MVT lower bound using derivIntervalCore: if f'(ξ) ∈ [dI.lo, dI.hi] for all ξ ∈ I,
    then f(y) - f(x) ≥ dI.lo * (y - x) for x ≤ y in I. -/
lemma mvt_lower_bound_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      ((derivIntervalCore e I cfg).lo : ℝ) * (y - x) ≤ evalFunc1 e y - evalFunc1 e x := by
  intro x y hx hy hxy
  set dI := derivIntervalCore e I cfg
  have hderiv_bound : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  -- Use Mathlib's MVT
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := by
    intro ξ hξ
    apply hderiv_bound
    exact @interior_subset ℝ _ (Set.Icc I.lo I.hi) ξ hξ
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hx; exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hy; exact hy
  exact hConvex.mul_sub_le_image_sub_of_le_deriv hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- MVT upper bound using derivIntervalCore: if f'(ξ) ∈ [dI.lo, dI.hi] for all ξ ∈ I,
    then f(y) - f(x) ≤ dI.hi * (y - x) for x ≤ y in I. -/
lemma mvt_upper_bound_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      evalFunc1 e y - evalFunc1 e x ≤ ((derivIntervalCore e I cfg).hi : ℝ) * (y - x) := by
  intro x y hx hy hxy
  set dI := derivIntervalCore e I cfg
  have hderiv_bound : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := by
    intro ξ hξ
    apply hderiv_bound
    exact @interior_subset ℝ _ (Set.Icc I.lo I.hi) ξ hξ
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hx; exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hy; exact hy
  exact hConvex.image_sub_le_mul_sub_of_deriv_le hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- **Golden Theorem for Computable Newton Contraction (Unique Root Existence)**

    This version assumes *both*:
    1. Core contraction check (computable, used by search/external tools)
    2. Non-core contraction check (used for the formal proof, via
       `verify_unique_root_newton`).

    The formal proof only relies on the non-core checker; the core checker
    can be used by the external agent for optimization but is not needed
    logically. This avoids the need to prove complex MVT-based contradiction
    lemmas for the Core interval functions.

    Note: The `h_cert_core` hypothesis is not used in the proof but is kept
    in the signature so the certificate format can include it for external
    tooling purposes. -/
theorem verify_unique_root_core (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat)
    (evalCfg : EvalConfig) (newtonCfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (_h_cert_core : checkNewtonContractsCore e I evalCfg = true)
    (h_cert_newton : checkNewtonContracts e I newtonCfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  -- We only *use* `h_cert_newton`. The core certificate is present for external tooling.
  exact verify_unique_root_newton e hsupp hvar0 I newtonCfg hCont h_cert_newton

/-! ### Fully Computable Unique Root Verification

The following theorems provide a **fully computable** path to proving unique root existence
using only `checkNewtonContractsCore`. This allows `native_decide` to work without requiring
noncomputable functions like `Real.exp` or `Real.log`. -/

/-- Newton step preserves roots when using Core evaluation functions.
    If x is a root in I and newtonStepCore produces N, then x ∈ N. -/
theorem newton_preserves_root_core (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I N : IntervalRat) (cfg : EvalConfig)
    (hStep : newtonStepCore e I cfg = some N)
    (x : ℝ) (hx : x ∈ I) (hroot : Expr.eval (fun _ => x) e = 0) :
    x ∈ N := by
  -- Extract structure from newtonStepCore
  obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepCore_extract e I N cfg hStep

  -- Define components matching abstract theorem
  let c := I.midpoint
  let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
  let dI := derivIntervalCore e I cfg

  -- Verify premises for abstract theorem
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I

  -- 1. f(c) ∈ fc via evalIntervalCore1_correct
  have hfc_correct : evalFunc1 e c ∈ fc := by
    simp only [evalFunc1]
    exact evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg)

  -- 2. f'(ξ) ∈ dI for all ξ ∈ I via derivIntervalCore_correct
  have hdI_correct : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ∈ dI := fun ξ hξ =>
    derivIntervalCore_correct e hsupp I ξ hξ cfg

  -- Apply abstract preservation lemma
  have hroot' : evalFunc1 e x = 0 := hroot
  have h_in_Newton := newton_operator_preserves_root e hsupp hvar0
    I c fc dI hc_in_I hfc_correct hdI_correct hdI_nonzero x hx hroot'

  -- Now we need to show x ∈ N where N = I ∩ Newton
  -- h_in_Newton shows x is in the Newton interval [c - Q.hi, c - Q.lo]
  -- Combined with hx : x ∈ I, we get x ∈ I ∩ Newton = N
  have hx_in_intersect := IntervalRat.mem_intersect hx h_in_Newton
  obtain ⟨K, hK_eq, hx_in_K⟩ := hx_in_intersect

  -- Show x ∈ N by using the intersection logic
  -- Both hStep and hK_eq refer to the same intersect
  unfold newtonStepCore at hStep
  simp only [hdI_nonzero, dite_false] at hStep
  -- Now hStep : IntervalRat.intersect I (I.newtonInterval fc dI) = some N
  -- And hK_eq : IntervalRat.intersect I (I.newtonInterval fc dI) = some K
  have hN_eq_K : N = K := by
    rw [hStep] at hK_eq
    simp only [Option.some.injEq] at hK_eq
    exact hK_eq
  rw [hN_eq_K]
  exact hx_in_K

/-- If Newton step succeeds, there's at most one root in I (via Rolle's theorem).
    This uses the fact that if dI doesn't contain zero, the derivative is nonzero
    everywhere on I, so f is strictly monotonic. -/
theorem newton_step_core_at_most_one_root (e : Expr) (hsupp : ExprSupported e) (_hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hStep : ∃ N, newtonStepCore e I cfg = some N)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I)
    (hx_root : Expr.eval (fun _ => x) e = 0) (hy_root : Expr.eval (fun _ => y) e = 0) :
    x = y := by
  obtain ⟨N, hN⟩ := hStep
  -- If step succeeds, dI doesn't contain zero
  set dI := derivIntervalCore e I cfg with hdI_def
  by_cases hzero : dI.containsZero
  · -- If dI contains zero, newtonStepCore returns none, but hN says it's some N
    unfold newtonStepCore at hN
    simp only [← hdI_def, dif_pos hzero, reduceCtorEq] at hN
  · -- dI doesn't contain zero, so derivative is nonzero everywhere on I
    simp only [IntervalRat.containsZero, not_and_or, not_le] at hzero

    by_contra hne
    -- If x ≠ y, Rolle's theorem gives ξ between them with f'(ξ) = 0
    simp only [IntervalRat.mem_def] at hx hy
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- x < y case
      have hIcc_sub : Set.Icc x y ⊆ Set.Icc (I.lo : ℝ) I.hi := by
        intro z ⟨hzlo, hzhi⟩
        exact ⟨le_trans hx.1 hzlo, le_trans hzhi hy.2⟩
      have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc x y) := hCont.mono hIcc_sub
      have hf_eq : evalFunc1 e x = evalFunc1 e y := by
        simp only [evalFunc1]; rw [hx_root, hy_root]
      obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) x y hlt hCont' hf_eq
      -- ξ ∈ (x, y) ⊆ I
      have hξ_in_I : ξ ∈ I := by
        simp only [IntervalRat.mem_def]
        exact ⟨le_trans hx.1 (le_of_lt hξ_mem.1), le_trans (le_of_lt hξ_mem.2) hy.2⟩
      -- f'(ξ) ∈ dI but f'(ξ) = 0
      have hderiv_in := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
      rw [hξ_deriv] at hderiv_in
      simp only [IntervalRat.mem_def] at hderiv_in
      rcases hzero with hlo_pos | hhi_neg
      · have hcast : (0 : ℝ) < dI.lo := by exact_mod_cast hlo_pos
        linarith [hderiv_in.1]
      · have hcast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
        linarith [hderiv_in.2]
    · -- y < x case (symmetric)
      have hIcc_sub : Set.Icc y x ⊆ Set.Icc (I.lo : ℝ) I.hi := by
        intro z ⟨hzlo, hzhi⟩
        exact ⟨le_trans hy.1 hzlo, le_trans hzhi hx.2⟩
      have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc y x) := hCont.mono hIcc_sub
      have hf_eq : evalFunc1 e y = evalFunc1 e x := by
        simp only [evalFunc1]; rw [hy_root, hx_root]
      obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) y x hlt hCont' hf_eq
      have hξ_in_I : ξ ∈ I := by
        simp only [IntervalRat.mem_def]
        exact ⟨le_trans hy.1 (le_of_lt hξ_mem.1), le_trans (le_of_lt hξ_mem.2) hx.2⟩
      have hderiv_in := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
      rw [hξ_deriv] at hderiv_in
      simp only [IntervalRat.mem_def] at hderiv_in
      rcases hzero with hlo_pos | hhi_neg
      · have hcast : (0 : ℝ) < dI.lo := by exact_mod_cast hlo_pos
        linarith [hderiv_in.1]
      · have hcast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
        linarith [hderiv_in.2]

/-- MVT bound using Core functions: If f' ≥ dI.lo > 0 (increasing) and f(I.lo) > 0,
    then f(c) > dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_lower_bound_pos_increasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_lo_pos : 0 < (derivIntervalCore e I cfg).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_pos : 0 < evalFunc1 e I.lo) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c > (dI.lo : ℝ) * hw := by
  intro c hw dI
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_lower_bound_core e hsupp I cfg hCont I.lo c hIlo_in_I hc_in_I hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.lo + dI.lo * hw := by linarith
    _ > 0 + dI.lo * hw := by linarith
    _ = dI.lo * hw := by ring

/-- MVT bound using Core functions: If f' ≥ dI.lo > 0 (increasing) and f(I.hi) < 0,
    then f(c) < -dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_upper_bound_pos_increasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_lo_pos : 0 < (derivIntervalCore e I cfg).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_neg : evalFunc1 e I.hi < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c < -((dI.lo : ℝ) * hw) := by
  intro c hw dI
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_lower_bound_core e hsupp I cfg hCont c I.hi hc_in_I hIhi_in_I hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.hi - dI.lo * hw := by linarith
    _ < 0 - dI.lo * hw := by linarith
    _ = -(dI.lo * hw) := by ring

/-- MVT bound using Core functions: If f' ≤ dI.hi < 0 (decreasing) and f(I.lo) < 0,
    then f(c) < 0 and more specifically, fc.lo / dI.hi ≥ hw. -/
lemma mvt_fc_upper_bound_neg_decreasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivIntervalCore e I cfg).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_neg : evalFunc1 e I.lo < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c < (dI.hi : ℝ) * hw := by
  intro c hw dI
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_upper_bound_core e hsupp I cfg hCont I.lo c hIlo_in_I hc_in_I hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.lo + dI.hi * hw := by linarith
    _ < 0 + dI.hi * hw := by linarith
    _ = dI.hi * hw := by ring

/-- MVT bound using Core functions: If f' ≤ dI.hi < 0 (decreasing) and f(I.hi) > 0,
    then f(c) > 0 and more specifically, fc.hi / dI.hi ≤ -hw. -/
lemma mvt_fc_lower_bound_neg_decreasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivIntervalCore e I cfg).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_pos : 0 < evalFunc1 e I.hi) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c > -((dI.hi : ℝ) * hw) := by
  intro c hw dI
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_upper_bound_core e hsupp I cfg hCont c I.hi hc_in_I hIhi_in_I hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.hi - dI.hi * hw := by linarith
    _ > 0 - dI.hi * hw := by linarith
    _ = -(dI.hi * hw) := by ring

/-- **Golden Theorem for Computable Unique Root (Fully Computable)**

    If `checkNewtonContractsCore e I cfg = true`, then there exists a unique root in I.

    This theorem uses ONLY computable functions (no Real.exp, Real.log, etc.),
    making it suitable for `native_decide` verification. -/
theorem verify_unique_root_computable (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkNewtonContractsCore e I cfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  simp only [checkNewtonContractsCore] at h_cert
  split at h_cert
  · exact absurd h_cert Bool.false_ne_true
  · rename_i N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
    have hContract : N.lo > I.lo ∧ N.hi < I.hi := ⟨h_cert.1, h_cert.2⟩

    -- Extract structure
    obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepCore_extract e I N cfg hN
    let c := I.midpoint
    let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
    let dI := derivIntervalCore e I cfg
    let hw : ℚ := (I.hi - I.lo) / 2

    -- From contraction bounds, extract Q bounds
    -- N.lo = max I.lo (c - Q.hi), N.hi = min I.hi (c - Q.lo)
    -- Contraction means: N.lo > I.lo and N.hi < I.hi
    -- So N.lo = c - Q.hi (not I.lo) and N.hi = c - Q.lo (not I.hi)
    have hbounds := contraction_newton_bounds hContract hN_lo hN_hi

    -- Q.hi < c - I.lo = hw and Q.lo > c - I.hi = -hw
    have hQ_hi_lt : (c : ℚ) - N.lo < hw := by
      rw [hbounds.1]
      have hc_minus_Ilo : c - I.lo = hw := by
        show I.midpoint - I.lo = (I.hi - I.lo) / 2
        simp only [IntervalRat.midpoint]; ring
      linarith [hContract.1]
    have hQ_lo_gt : (c : ℚ) - N.hi > -hw := by
      rw [hbounds.2]
      have hc_minus_Ihi : c - I.hi = -hw := by
        show I.midpoint - I.hi = -((I.hi - I.lo) / 2)
        simp only [IntervalRat.midpoint]; ring
      linarith [hContract.2]

    -- Use sign analysis to prove existence
    simp only [IntervalRat.containsZero, not_and_or, not_le] at hdI_nonzero

    -- Contraction + MVT logic mirrors newton_contraction_has_root
    -- Key: if f doesn't change sign, MVT bounds on the quotient contradict contraction
    have hI_nonsingleton : I.lo < I.hi := by
      have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
      have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
      have h3 : (N.lo : ℝ) ≤ N.hi := by exact_mod_cast N.le
      have h4 : I.lo < I.hi := by
        have : (I.lo : ℝ) < I.hi := by linarith
        exact_mod_cast this
      exact h4

    set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf_def

    -- Case split on derivative sign
    rcases hdI_nonzero with hdI_pos | hdI_neg
    · -- Case: dI.lo > 0 (strictly increasing)
      by_cases hlo : f I.lo ≥ 0
      · by_cases hhi : f I.hi ≤ 0
        · -- f(lo) ≥ 0 and f(hi) ≤ 0 with f increasing is a contradiction
          -- Because f' ≥ dI.lo > 0 implies f(hi) - f(lo) > 0, so f(hi) > f(lo)
          -- Combined with f(lo) ≥ 0 ≥ f(hi), this is impossible
          exfalso
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          -- MVT: f(hi) - f(lo) ≥ dI.lo * (hi - lo) > 0
          have hmvt := mvt_lower_bound_core e hsupp I cfg hCont I.lo I.hi hIlo_in_I hIhi_in_I hle
          have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_pos
          have hwidth_pos : (I.hi : ℝ) - I.lo > 0 := by
            have h : (I.lo : ℝ) < I.hi := by exact_mod_cast hI_nonsingleton
            linarith
          have hdiff_pos : (dI.lo : ℝ) * ((I.hi : ℝ) - I.lo) > 0 := mul_pos hdI_lo_pos_real hwidth_pos
          -- hmvt : evalFunc1 e ↑I.hi - evalFunc1 e ↑I.lo ≥ ↑dI.lo * (↑I.hi - ↑I.lo)
          -- hdiff_pos : (dI.lo : ℝ) * ((I.hi : ℝ) - I.lo) > 0
          -- So evalFunc1 e I.hi > evalFunc1 e I.lo
          -- hlo : 0 ≤ f I.lo = evalFunc1 e I.lo
          -- hhi : f I.hi ≤ 0 = evalFunc1 e I.hi ≤ 0
          -- This gives: 0 ≤ evalFunc1 e I.lo < evalFunc1 e I.hi ≤ 0, contradiction
          have hstrictly_increasing : evalFunc1 e I.hi > evalFunc1 e I.lo := by linarith
          linarith
        · -- f(lo) ≥ 0 and f(hi) > 0 with f increasing → f > 0 on I
          push_neg at hhi
          by_cases hlo_eq : f I.lo = 0
          · use I.lo
            have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            constructor
            · exact ⟨hIlo_in_I, hlo_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.lo hy_in_I hIlo_in_I hy_root hlo_eq
          · -- f(lo) > 0, get contradiction via MVT
            have hlo_pos : 0 < f I.lo := lt_of_le_of_ne hlo (Ne.symm hlo_eq)
            exfalso
            -- MVT: fc.hi / dI.lo ≥ hw (half-width)
            have hMVT := mvt_fc_lower_bound_pos_increasing_core e hsupp I cfg hI_nonsingleton hdI_pos hCont hlo_pos
            -- Apply generic contraction contradiction
            exact generic_contraction_absurd_hi I c fc dI N rfl hdI_nonzero hdI_pos
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_lo hContract.1 hMVT
      · push_neg at hlo
        by_cases hhi : f I.hi ≤ 0
        · by_cases hhi_eq : f I.hi = 0
          · use I.hi
            have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            constructor
            · exact ⟨hIhi_in_I, hhi_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.hi hy_in_I hIhi_in_I hy_root hhi_eq
          · -- f(hi) < 0, get contradiction via MVT
            have hhi_neg : f I.hi < 0 := lt_of_le_of_ne hhi hhi_eq
            exfalso
            have hMVT := mvt_fc_upper_bound_pos_increasing_core e hsupp I cfg hI_nonsingleton hdI_pos hCont hhi_neg
            exact generic_contraction_absurd_lo I c fc dI N rfl hdI_nonzero hdI_pos
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_hi hContract.2 hMVT
        · -- f(lo) < 0 and f(hi) > 0: SIGN CHANGE! Apply IVT.
          push_neg at hhi
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hlo, le_of_lt hhi⟩
          have hivt := intermediate_value_Icc hle hCont h0_in_range
          obtain ⟨x, hx_mem, hx_root⟩ := hivt
          use x
          constructor
          · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact ⟨hx_in_I, hx_root⟩
          · intro y ⟨hy_in_I, hy_root⟩
            have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y x hy_in_I hx_in_I hy_root hx_root
    · -- Case: dI.hi < 0 (strictly decreasing) - symmetric logic
      by_cases hlo : f I.lo ≤ 0
      · by_cases hhi : f I.hi ≥ 0
        · -- f(lo) ≤ 0 ≤ f(hi) with f decreasing is a contradiction
          -- Because f' ≤ dI.hi < 0 implies f(hi) - f(lo) < 0, so f(hi) < f(lo)
          -- Combined with f(lo) ≤ 0 ≤ f(hi), this is impossible
          exfalso
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          -- MVT: f(hi) - f(lo) ≤ dI.hi * (hi - lo) < 0
          have hmvt := mvt_upper_bound_core e hsupp I cfg hCont I.lo I.hi hIlo_in_I hIhi_in_I hle
          have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_neg
          have hwidth_pos : (I.hi : ℝ) - I.lo > 0 := by
            have h : (I.lo : ℝ) < I.hi := by exact_mod_cast hI_nonsingleton
            linarith
          have hdiff_neg : (dI.hi : ℝ) * ((I.hi : ℝ) - I.lo) < 0 := mul_neg_of_neg_of_pos hdI_hi_neg_real hwidth_pos
          -- hmvt : evalFunc1 e ↑I.hi - evalFunc1 e ↑I.lo ≤ ↑dI.hi * (↑I.hi - ↑I.lo)
          -- hdiff_neg : (dI.hi : ℝ) * ((I.hi : ℝ) - I.lo) < 0
          -- So evalFunc1 e I.hi < evalFunc1 e I.lo
          -- hlo : f I.lo ≤ 0 = evalFunc1 e I.lo ≤ 0
          -- hhi : f I.hi ≥ 0 = evalFunc1 e I.hi ≥ 0
          -- This gives: 0 ≤ evalFunc1 e I.hi < evalFunc1 e I.lo ≤ 0, contradiction
          have hstrictly_decreasing : evalFunc1 e I.hi < evalFunc1 e I.lo := by linarith
          linarith
        · push_neg at hhi
          by_cases hlo_eq : f I.lo = 0
          · use I.lo
            have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            constructor
            · exact ⟨hIlo_in_I, hlo_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.lo hy_in_I hIlo_in_I hy_root hlo_eq
          · -- f(lo) < 0 and f(hi) < 0 with f decreasing → contradiction via MVT
            have hlo_neg : f I.lo < 0 := lt_of_le_of_ne hlo hlo_eq
            exfalso
            have hMVT := mvt_fc_upper_bound_neg_decreasing_core e hsupp I cfg hI_nonsingleton hdI_neg hCont hlo_neg
            exact generic_contraction_absurd_hi_neg I c fc dI N rfl hdI_nonzero hdI_neg
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_lo hContract.1 hMVT
      · push_neg at hlo
        by_cases hhi : f I.hi ≥ 0
        · by_cases hhi_eq : f I.hi = 0
          · use I.hi
            have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            constructor
            · exact ⟨hIhi_in_I, hhi_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.hi hy_in_I hIhi_in_I hy_root hhi_eq
          · -- f(hi) > 0 and f(lo) > 0 with f decreasing → contradiction via MVT
            have hhi_pos : 0 < f I.hi := lt_of_le_of_ne hhi (Ne.symm hhi_eq)
            exfalso
            have hMVT := mvt_fc_lower_bound_neg_decreasing_core e hsupp I cfg hI_nonsingleton hdI_neg hCont hhi_pos
            exact generic_contraction_absurd_lo_neg I c fc dI N rfl hdI_nonzero hdI_neg
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_hi hContract.2 hMVT
        · -- f(lo) > 0 and f(hi) < 0: SIGN CHANGE for decreasing function!
          push_neg at hhi
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hhi, le_of_lt hlo⟩
          have hivt := intermediate_value_Icc' hle hCont h0_in_range
          obtain ⟨x, hx_mem, hx_root⟩ := hivt
          use x
          constructor
          · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact ⟨hx_in_I, hx_root⟩
          · intro y ⟨hy_in_I, hy_root⟩
            have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y x hy_in_I hx_in_I hy_root hx_root

/-! ### Sign Change Root Existence -/

/-- **Golden Theorem for Sign Change Root Existence**

    If `checkSignChange e I cfg = true`, then there exists a root in I.

    This uses the Intermediate Value Theorem: if f(lo) and f(hi) have opposite signs,
    and f is continuous on I, then f has a root in I. -/
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  simp only [checkSignChange, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h_cert
  -- Extract domain validity from certificate
  have hdom_lo := checkDomainValid1_correct e (IntervalRat.singleton I.lo) cfg h_cert.1.1
  have hdom_hi := checkDomainValid1_correct e (IntervalRat.singleton I.hi) cfg h_cert.1.2
  -- Define f for convenience
  set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf
  -- Get singleton memberships
  have hlo_sing : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
  have hhi_sing : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
  -- Apply evalIntervalCore1_correct to get bounds on f(lo) and f(hi)
  have hflo := evalIntervalCore1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_sing cfg hdom_lo
  have hfhi := evalIntervalCore1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_sing cfg hdom_hi
  simp only [IntervalRat.mem_def] at hflo hfhi
  -- Get the interval bound
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  -- Extract sign change condition
  have h_sign := h_cert.2
  -- Handle the two cases of signChange
  cases h_sign with
  | inl hcase =>
    -- Case: f(lo).hi < 0 ∧ 0 < f(hi).lo, meaning f(lo) < 0 < f(hi)
    have hflo_neg : f I.lo < 0 := by
      have hbound : f I.lo ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi := hflo.2
      have hcast : ((evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hfhi_pos : 0 < f I.hi := by
      have hbound : (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo ≤ f I.hi := hfhi.1
      have hcast : (0 : ℝ) < (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by
        exact_mod_cast hcase.2
      linarith
    -- Apply IVT: since f(lo) < 0 < f(hi), 0 ∈ Icc (f lo) (f hi) ⊆ f '' Icc lo hi
    have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hflo_neg, le_of_lt hfhi_pos⟩
    have hivt := intermediate_value_Icc (α := ℝ) (δ := ℝ) hle hCont
    have h0_in_image := hivt h0_in_range
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_image
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem
  | inr hcase =>
    -- Case: f(hi).hi < 0 ∧ 0 < f(lo).lo, meaning f(hi) < 0 < f(lo)
    have hfhi_neg : f I.hi < 0 := by
      have hbound : f I.hi ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi := hfhi.2
      have hcast : ((evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hflo_pos : 0 < f I.lo := by
      have hbound : (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo ≤ f I.lo := hflo.1
      have hcast : (0 : ℝ) < (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo := by
        exact_mod_cast hcase.2
      linarith
    -- f '' [lo, hi] is an interval containing both f(lo) and f(hi)
    have hflo_in_image : f I.lo ∈ f '' Set.Icc (↑I.lo) (↑I.hi) :=
      Set.mem_image_of_mem f (Set.left_mem_Icc.mpr hle)
    have hfhi_in_image : f I.hi ∈ f '' Set.Icc (↑I.lo) (↑I.hi) :=
      Set.mem_image_of_mem f (Set.right_mem_Icc.mpr hle)
    -- The image is connected (as continuous image of connected set)
    have hconn : IsConnected (f '' Set.Icc (↑I.lo) (↑I.hi)) :=
      (isConnected_Icc hle).image f hCont
    -- Use IsConnected.Icc_subset: the image contains [f(hi), f(lo)] since it's connected
    have hsub := hconn.Icc_subset hfhi_in_image hflo_in_image
    have h0_mem : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hfhi_neg, le_of_lt hflo_pos⟩
    have h0_in_img := hsub h0_mem
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_img
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem

/-! ### Bisection-Based Root Existence -/

/-- Check if bisection finds a root (returns hasRoot for some sub-interval).
    This runs the bisection algorithm and checks if any interval has hasRoot status.

    Note: This is noncomputable because bisectRoot uses evalInterval1. -/
noncomputable def checkHasRoot (e : Expr) (I : IntervalRat) (cfg : RootConfig) : Bool :=
  let tol : ℚ := (1 : ℚ) / (2 ^ cfg.maxDepth)
  let htol : 0 < tol := by positivity
  let result := bisectRoot e I cfg.maxDepth tol htol
  result.intervals.any fun (_, s) => s == RootStatus.hasRoot

/-- **Golden Theorem for Bisection Root Existence**

    If `checkHasRoot e I cfg = true`, then there exists a root in I.

    This uses bisectRoot_hasRoot_correct which proves that if bisection returns
    hasRoot for a sub-interval J ⊆ I, then there exists a root in J (hence in I). -/
theorem verify_has_root (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : RootConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkHasRoot e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  simp only [checkHasRoot] at h_cert
  -- Extract the interval with hasRoot status
  have htol : (0 : ℚ) < 1 / 2 ^ cfg.maxDepth := by positivity
  set result := bisectRoot e I cfg.maxDepth (1 / 2 ^ cfg.maxDepth) htol with hresult
  -- h_cert says some interval has hasRoot status
  simp only [List.any_eq_true, beq_iff_eq] at h_cert
  obtain ⟨⟨J, s⟩, hmem, hs⟩ := h_cert
  -- Apply bisectRoot_hasRoot_correct
  have hroot := bisectRoot_hasRoot_correct e hsupp I cfg.maxDepth (1 / 2 ^ cfg.maxDepth) htol hCont
  have hroot_J := hroot J s hmem hs
  -- hroot_J : ∃ x ∈ J, f(x) = 0
  -- We need to show x ∈ I
  obtain ⟨x, hxJ, hx_root⟩ := hroot_J
  -- Show J ⊆ I using go_subinterval (implicitly used in bisectRoot_hasRoot_correct)
  -- Actually, bisectRoot_hasRoot_correct proves x ∈ J, and we need x ∈ I
  -- The proof in bisectRoot_hasRoot_correct shows J is a sub-interval of I
  -- and applies signChange_correct with continuity on J
  -- So x ∈ J ⊆ I
  refine ⟨x, ?_, hx_root⟩
  -- Need to show x ∈ I given x ∈ J and J is a sub-interval of I
  -- From go_subinterval in the bisectRoot_hasRoot_correct proof
  have hJsub : I.lo ≤ J.lo ∧ J.hi ≤ I.hi := by
    -- This follows from go_subinterval applied in the bisectRoot_hasRoot_correct proof
    -- We need to extract this lemma
    have hSub := go_subinterval e (1 / 2 ^ cfg.maxDepth) cfg.maxDepth I
      [(I, RootStatus.unknown)] cfg.maxDepth []
      (subinterval_inv_initial I)
      (fun _ _ h => by simp only [List.mem_nil_iff] at h)
    exact hSub J s hmem
  simp only [IntervalRat.mem_def] at hxJ ⊢
  constructor
  · calc (I.lo : ℝ) ≤ J.lo := by exact_mod_cast hJsub.1
      _ ≤ x := hxJ.1
  · calc x ≤ J.hi := hxJ.2
      _ ≤ I.hi := by exact_mod_cast hJsub.2

end LeanCert.Validity.RootFinding
