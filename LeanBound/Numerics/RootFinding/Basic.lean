/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.IntervalEval
import Mathlib.Topology.Order.IntermediateValue

/-!
# Root Finding: Basic Definitions

This file provides the core definitions and basic correctness lemmas for root finding.

## Main definitions

* `RootStatus` - Result of checking an interval for roots
* `excludesZero` - Check if an interval excludes zero
* `signChange` - Check if function has opposite signs at endpoints
* `checkRootStatus` - Determine initial root status

## Main theorems

* `excludesZero_correct` - If interval excludes zero, no roots exist
* `signChange_correct` - If sign change exists, a root exists (IVT)
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-! ### Root status -/

/-- Result of checking an interval for roots -/
inductive RootStatus where
  /-- No root in this interval (interval evaluation doesn't contain 0) -/
  | noRoot
  /-- At least one root exists (by intermediate value theorem) -/
  | hasRoot
  /-- Exactly one root exists (Newton contraction) -/
  | uniqueRoot
  /-- Cannot determine -/
  | unknown
  deriving Repr, DecidableEq

/-! ### Basic root checks -/

/-- Check if interval evaluation excludes zero -/
def excludesZero (I : IntervalRat) : Bool :=
  I.hi < 0 ∨ 0 < I.lo

/-- Check if function values have opposite signs at endpoints (IVT applicable) -/
noncomputable def signChange (e : Expr) (I : IntervalRat) : Bool :=
  let flo := evalInterval1 e (IntervalRat.singleton I.lo)
  let fhi := evalInterval1 e (IntervalRat.singleton I.hi)
  (flo.hi < 0 ∧ 0 < fhi.lo) ∨ (fhi.hi < 0 ∧ 0 < flo.lo)

/-- Initial root status check -/
noncomputable def checkRootStatus (e : Expr) (I : IntervalRat) : RootStatus :=
  let fI := evalInterval1 e I
  if excludesZero fI then
    RootStatus.noRoot
  else if signChange e I then
    RootStatus.hasRoot
  else
    RootStatus.unknown

/-! ### Core correctness lemmas -/

/-- If interval evaluation excludes zero, then f(x) ≠ 0 for all x in I.
    This is the key lemma for proving noRoot correctness. -/
theorem excludesZero_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (hexcl : excludesZero (evalInterval1 e I) = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0 := by
  intro x hx hcontra
  -- From evalInterval1_correct: f(x) ∈ [lo, hi]
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  -- excludesZero means hi < 0 ∨ 0 < lo
  simp only [excludesZero, decide_eq_true_eq] at hexcl
  cases hexcl with
  | inl hhi_neg =>
    -- hi < 0, so f(x) ≤ hi < 0, contradicting f(x) = 0
    have : (Expr.eval (fun _ => x) e : ℝ) ≤ (evalInterval1 e I).hi := hmem.2
    have hcast : ((evalInterval1 e I).hi : ℝ) < 0 := by exact_mod_cast hhi_neg
    linarith [hcontra]
  | inr hlo_pos =>
    -- 0 < lo, so 0 < lo ≤ f(x), contradicting f(x) = 0
    have : ((evalInterval1 e I).lo : ℝ) ≤ Expr.eval (fun _ => x) e := hmem.1
    have hcast : (0 : ℝ) < (evalInterval1 e I).lo := by exact_mod_cast hlo_pos
    linarith [hcontra]

/-- If there is a sign change, then by IVT there exists a root.
    This uses Mathlib's intermediate_value_Icc theorem.

    **Proof strategy**:
    1. signChange means f(lo) < 0 < f(hi) or f(hi) < 0 < f(lo)
    2. Use evalInterval1_correct on singletons to get actual values at endpoints
    3. Apply intermediate_value_Icc to conclude 0 is in the image -/
theorem signChange_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (hsign : signChange e I = true)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  -- Unpack signChange
  simp only [signChange, decide_eq_true_eq] at hsign
  -- Define f for convenience
  set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf
  -- Get singleton memberships
  have hlo_sing : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
  have hhi_sing : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
  -- Apply evalInterval1_correct to get bounds on f(lo) and f(hi)
  have hflo := evalInterval1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_sing
  have hfhi := evalInterval1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_sing
  simp only [IntervalRat.mem_def] at hflo hfhi
  -- Get the interval bound
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  -- Now handle the two cases of signChange
  cases hsign with
  | inl hcase =>
    -- Case: f(lo).hi < 0 ∧ 0 < f(hi).lo, meaning f(lo) < 0 < f(hi)
    have hflo_neg : f I.lo < 0 := by
      have hbound : f I.lo ≤ (evalInterval1 e (IntervalRat.singleton I.lo)).hi := hflo.2
      have hcast : ((evalInterval1 e (IntervalRat.singleton I.lo)).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hfhi_pos : 0 < f I.hi := by
      have hbound : (evalInterval1 e (IntervalRat.singleton I.hi)).lo ≤ f I.hi := hfhi.1
      have hcast : (0 : ℝ) < (evalInterval1 e (IntervalRat.singleton I.hi)).lo := by
        exact_mod_cast hcase.2
      linarith
    -- Now apply IVT: since f(lo) < 0 < f(hi), 0 ∈ Icc (f lo) (f hi) ⊆ f '' Icc lo hi
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
      have hbound : f I.hi ≤ (evalInterval1 e (IntervalRat.singleton I.hi)).hi := hfhi.2
      have hcast : ((evalInterval1 e (IntervalRat.singleton I.hi)).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hflo_pos : 0 < f I.lo := by
      have hbound : (evalInterval1 e (IntervalRat.singleton I.lo)).lo ≤ f I.lo := hflo.1
      have hcast : (0 : ℝ) < (evalInterval1 e (IntervalRat.singleton I.lo)).lo := by
        exact_mod_cast hcase.2
      linarith
    -- Apply IVT' variant: since f(hi) < 0 < f(lo), use intermediate_value_Icc'
    have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hfhi_neg, le_of_lt hflo_pos⟩
    have hivt := intermediate_value_Icc' (α := ℝ) (δ := ℝ) hle hCont
    have h0_in_image := hivt h0_in_range
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_image
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem

/-! ## N-Variable Root Finding Infrastructure

The following section provides infrastructure for root finding in multi-variable
expressions. The key idea is that we search for roots along a specific coordinate
while holding other variables fixed.

For a multi-variable expression `e` with environment `ρ`, we can find roots of
`evalAlong e ρ idx` - the function obtained by varying coordinate `idx` while
keeping all other coordinates fixed according to `ρ`.
-/

/-! ### N-variable root checks -/

/-- Check if interval evaluation along coordinate `idx` excludes zero.
    Note: `idx` is kept for API consistency though the full box is checked. -/
noncomputable def excludesZero_idx (e : Expr) (ρ_int : IntervalEnv) (_idx : Nat) : Bool :=
  let fI := evalInterval e ρ_int
  excludesZero fI

/-- Check if function has opposite signs at endpoints along coordinate `idx` -/
noncomputable def signChange_idx (e : Expr) (ρ_int : IntervalEnv) (idx : Nat) : Bool :=
  -- Evaluate at left endpoint of idx
  let ρ_lo := fun i => if i = idx then IntervalRat.singleton (ρ_int idx).lo else ρ_int i
  -- Evaluate at right endpoint of idx
  let ρ_hi := fun i => if i = idx then IntervalRat.singleton (ρ_int idx).hi else ρ_int i
  let flo := evalInterval e ρ_lo
  let fhi := evalInterval e ρ_hi
  (flo.hi < 0 ∧ 0 < fhi.lo) ∨ (fhi.hi < 0 ∧ 0 < flo.lo)

/-- Initial root status check along coordinate `idx` -/
noncomputable def checkRootStatus_idx (e : Expr) (ρ_int : IntervalEnv) (idx : Nat) : RootStatus :=
  let fI := evalInterval e ρ_int
  if excludesZero fI then
    RootStatus.noRoot
  else if signChange_idx e ρ_int idx then
    RootStatus.hasRoot
  else
    RootStatus.unknown

/-! ### N-variable correctness lemmas -/

/-- If interval evaluation excludes zero, then f(x) ≠ 0 for all x in the box.
    N-variable version: the function has no zeros in the entire box. -/
theorem excludesZero_correct_idx (e : Expr) (hsupp : ExprSupported e)
    (ρ_int : IntervalEnv)
    (hexcl : excludesZero (evalInterval e ρ_int) = true) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) → Expr.eval ρ_real e ≠ 0 := by
  intro ρ_real hρ hcontra
  -- From evalInterval_correct: f(ρ) ∈ [lo, hi]
  have hmem := evalInterval_correct e hsupp ρ_real ρ_int hρ
  simp only [IntervalRat.mem_def] at hmem
  -- excludesZero means hi < 0 ∨ 0 < lo
  simp only [excludesZero, decide_eq_true_eq] at hexcl
  cases hexcl with
  | inl hhi_neg =>
    have : (Expr.eval ρ_real e : ℝ) ≤ (evalInterval e ρ_int).hi := hmem.2
    have hcast : ((evalInterval e ρ_int).hi : ℝ) < 0 := by exact_mod_cast hhi_neg
    linarith [hcontra]
  | inr hlo_pos =>
    have : ((evalInterval e ρ_int).lo : ℝ) ≤ Expr.eval ρ_real e := hmem.1
    have hcast : (0 : ℝ) < (evalInterval e ρ_int).lo := by exact_mod_cast hlo_pos
    linarith [hcontra]

/-- If there is a sign change along coordinate `idx`, then by IVT there exists a root
    along that coordinate.
    N-variable version: for any fixed values of other coordinates satisfying `ρ_int`,
    there exists a value of coordinate `idx` where the function is zero. -/
theorem signChange_correct_idx (e : Expr) (hsupp : ExprSupported e)
    (ρ_int : IntervalEnv) (idx : Nat)
    (ρ_real : Nat → ℝ) (hρ : ∀ i, i ≠ idx → ρ_real i ∈ ρ_int i)
    (hsign : signChange_idx e ρ_int idx = true)
    (hCont : ContinuousOn (Expr.evalAlong e ρ_real idx)
              (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ))) :
    ∃ x ∈ ρ_int idx, Expr.evalAlong e ρ_real idx x = 0 := by
  -- Unpack signChange_idx
  simp only [signChange_idx, decide_eq_true_eq] at hsign
  -- Define f for convenience
  set f := Expr.evalAlong e ρ_real idx with hf
  -- Define endpoint environments
  let ρ_lo : IntervalEnv := fun i => if i = idx then IntervalRat.singleton (ρ_int idx).lo else ρ_int i
  let ρ_hi : IntervalEnv := fun i => if i = idx then IntervalRat.singleton (ρ_int idx).hi else ρ_int i
  -- Show ρ_real with lo at idx is in ρ_lo
  have hρ_lo : ∀ i, Expr.updateVar ρ_real idx (ρ_int idx).lo i ∈ ρ_lo i := by
    intro i
    by_cases hi : i = idx
    · subst hi
      simp only [Expr.updateVar_same, ρ_lo, ↓reduceIte]
      exact IntervalRat.mem_singleton _
    · simp only [Expr.updateVar_other _ _ _ _ hi, ρ_lo, if_neg hi]
      exact hρ i hi
  -- Show ρ_real with hi at idx is in ρ_hi
  have hρ_hi : ∀ i, Expr.updateVar ρ_real idx (ρ_int idx).hi i ∈ ρ_hi i := by
    intro i
    by_cases hi : i = idx
    · subst hi
      simp only [Expr.updateVar_same, ρ_hi, ↓reduceIte]
      exact IntervalRat.mem_singleton _
    · simp only [Expr.updateVar_other _ _ _ _ hi, ρ_hi, if_neg hi]
      exact hρ i hi
  -- Get bounds from interval evaluation
  have hflo := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx (ρ_int idx).lo) ρ_lo hρ_lo
  have hfhi := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx (ρ_int idx).hi) ρ_hi hρ_hi
  simp only [IntervalRat.mem_def] at hflo hfhi
  -- f(lo) and f(hi) match Expr.eval with updated environments
  have hf_lo : f (ρ_int idx).lo = Expr.eval (Expr.updateVar ρ_real idx (ρ_int idx).lo) e := rfl
  have hf_hi : f (ρ_int idx).hi = Expr.eval (Expr.updateVar ρ_real idx (ρ_int idx).hi) e := rfl
  -- Get the interval bound
  have hle : ((ρ_int idx).lo : ℝ) ≤ (ρ_int idx).hi := by exact_mod_cast (ρ_int idx).le
  -- Now handle the two cases of signChange
  cases hsign with
  | inl hcase =>
    -- Case: f(lo).hi < 0 ∧ 0 < f(hi).lo
    have hflo_neg : f (ρ_int idx).lo < 0 := by
      rw [hf_lo]
      have hbound := hflo.2
      have hcast : ((evalInterval e ρ_lo).hi : ℝ) < 0 := by exact_mod_cast hcase.1
      linarith
    have hfhi_pos : 0 < f (ρ_int idx).hi := by
      rw [hf_hi]
      have hbound := hfhi.1
      have hcast : (0 : ℝ) < (evalInterval e ρ_hi).lo := by exact_mod_cast hcase.2
      linarith
    have h0_in_range : (0 : ℝ) ∈ Set.Icc (f (ρ_int idx).lo) (f (ρ_int idx).hi) :=
      ⟨le_of_lt hflo_neg, le_of_lt hfhi_pos⟩
    have hivt := intermediate_value_Icc (α := ℝ) (δ := ℝ) hle hCont
    have h0_in_image := hivt h0_in_range
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_image
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem
  | inr hcase =>
    -- Case: f(hi).hi < 0 ∧ 0 < f(lo).lo
    have hfhi_neg : f (ρ_int idx).hi < 0 := by
      rw [hf_hi]
      have hbound := hfhi.2
      have hcast : ((evalInterval e ρ_hi).hi : ℝ) < 0 := by exact_mod_cast hcase.1
      linarith
    have hflo_pos : 0 < f (ρ_int idx).lo := by
      rw [hf_lo]
      have hbound := hflo.1
      have hcast : (0 : ℝ) < (evalInterval e ρ_lo).lo := by exact_mod_cast hcase.2
      linarith
    have h0_in_range : (0 : ℝ) ∈ Set.Icc (f (ρ_int idx).hi) (f (ρ_int idx).lo) :=
      ⟨le_of_lt hfhi_neg, le_of_lt hflo_pos⟩
    have hivt := intermediate_value_Icc' (α := ℝ) (δ := ℝ) hle hCont
    have h0_in_image := hivt h0_in_range
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_image
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem

/-! ### N-variable bisection root finding -/

/-- Result of bisection root finding -/
inductive BisectResult where
  /-- Found interval containing root with a sign change -/
  | found (I : IntervalRat) (depth : ℕ)
  /-- No root in this interval -/
  | noRoot
  /-- Could not determine (no sign change detected) -/
  | uncertain (I : IntervalRat) (depth : ℕ)
  deriving Repr

/-- Update an interval environment at a specific index -/
def updateIntervalEnv' (ρ : IntervalEnv) (idx : Nat) (J : IntervalRat) : IntervalEnv :=
  fun i => if i = idx then J else ρ i

/-- Helper: membership in bisected intervals -/
theorem mem_bisect_cases (J : IntervalRat) (t : ℝ) (ht : t ∈ J) :
    t ∈ (J.bisect).1 ∨ t ∈ (J.bisect).2 := by
  by_cases hm : t ≤ J.midpoint
  · left; exact IntervalRat.mem_bisect_left ht hm
  · right
    push_neg at hm
    exact IntervalRat.mem_bisect_right ht (le_of_lt hm)

/-- N-variable bisection root finding along coordinate `idx`.

    This searches for a root of `e` by bisecting the interval `ρ idx` while
    keeping other coordinates fixed. It uses interval arithmetic to:
    1. Exclude intervals where the function cannot be zero
    2. Detect sign changes indicating a root exists (by IVT)
    3. Bisect when neither condition is met

    Returns a `BisectResult` indicating whether a root was found, excluded, or uncertain. -/
noncomputable def bisectRootIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (maxDepth : ℕ) : BisectResult :=
  go (ρ idx) maxDepth
where
  go (J : IntervalRat) (depth : ℕ) : BisectResult :=
    let ρ' := updateIntervalEnv' ρ idx J
    -- Check if we can exclude this interval
    if excludesZero (evalInterval e ρ') then
      BisectResult.noRoot
    -- Check for sign change
    else if signChange_idx e ρ' idx then
      BisectResult.found J (maxDepth - depth)
    -- Reached max depth without determination
    else if depth = 0 then
      BisectResult.uncertain J maxDepth
    -- Bisect and search recursively
    else
      let (J₁, J₂) := J.bisect
      let r₁ := go J₁ (depth - 1)
      -- If first half found a root, return it
      match r₁ with
      | BisectResult.found I d => BisectResult.found I d
      | _ =>
        let r₂ := go J₂ (depth - 1)
        -- If second half found a root, return it
        match r₂ with
        | BisectResult.found I d => BisectResult.found I d
        -- If both are noRoot, the whole interval is noRoot
        | BisectResult.noRoot =>
          match r₁ with
          | BisectResult.noRoot => BisectResult.noRoot
          | BisectResult.uncertain I d => BisectResult.uncertain I d
          | BisectResult.found I d => BisectResult.found I d  -- unreachable
        -- Otherwise uncertain
        | BisectResult.uncertain I d =>
          match r₁ with
          | BisectResult.noRoot => BisectResult.uncertain I d
          | BisectResult.uncertain I₁ d₁ =>
            -- Return the one with smaller interval or less depth
            if I₁.width ≤ I.width then BisectResult.uncertain I₁ d₁
            else BisectResult.uncertain I d
          | BisectResult.found I d => BisectResult.found I d  -- unreachable

/-- Helper: when go returns found, signChange_idx was true for that interval -/
theorem bisectRootIdx_go_found_signChange (e : Expr) (ρ_int : IntervalEnv) (idx : Nat)
    (maxDepth depth : ℕ) (J I : IntervalRat) (d : ℕ)
    (hJ_sub : ∀ t, t ∈ J → t ∈ ρ_int idx)
    (hfound : bisectRootIdx.go e ρ_int idx maxDepth J depth = BisectResult.found I d) :
    signChange_idx e (updateIntervalEnv' ρ_int idx I) idx = true ∧
    (∀ t, t ∈ I → t ∈ ρ_int idx) := by
  induction depth generalizing J I d with
  | zero =>
    unfold bisectRootIdx.go at hfound
    by_cases hexcl : excludesZero (evalInterval e (updateIntervalEnv' ρ_int idx J)) = true
    · simp only [hexcl, ↓reduceIte] at hfound; exact (BisectResult.noConfusion hfound)
    · simp only [hexcl, ↓reduceIte, Bool.false_eq_true] at hfound
      by_cases hsign : signChange_idx e (updateIntervalEnv' ρ_int idx J) idx = true
      · simp only [hsign] at hfound
        obtain ⟨rfl, _⟩ := hfound
        exact ⟨hsign, hJ_sub⟩
      · simp only [hsign] at hfound; exact (BisectResult.noConfusion hfound)
  | succ n ih =>
    unfold bisectRootIdx.go at hfound
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hfound
    by_cases hexcl : excludesZero (evalInterval e (updateIntervalEnv' ρ_int idx J)) = true
    · simp only [hexcl, ↓reduceIte] at hfound; exact (BisectResult.noConfusion hfound)
    · simp only [hexcl, ↓reduceIte, Bool.false_eq_true] at hfound
      by_cases hsign : signChange_idx e (updateIntervalEnv' ρ_int idx J) idx = true
      · simp only [hsign] at hfound
        obtain ⟨rfl, _⟩ := hfound
        exact ⟨hsign, hJ_sub⟩
      · simp only [hsign] at hfound
        -- Bisection case
        have hsub1 : ∀ t, t ∈ J.bisect.1 → t ∈ ρ_int idx := fun t ht =>
          hJ_sub t (IntervalRat.mem_of_mem_bisect_left ht)
        have hsub2 : ∀ t, t ∈ J.bisect.2 → t ∈ ρ_int idx := fun t ht =>
          hJ_sub t (IntervalRat.mem_of_mem_bisect_right ht)
        match hr1 : bisectRootIdx.go e ρ_int idx maxDepth J.bisect.1 n with
        | BisectResult.found Ix dx =>
          rw [hr1] at hfound
          obtain ⟨rfl, rfl⟩ := hfound
          exact ih J.bisect.1 _ _ hsub1 hr1
        | BisectResult.noRoot =>
          rw [hr1] at hfound
          match hr2 : bisectRootIdx.go e ρ_int idx maxDepth J.bisect.2 n with
          | BisectResult.found Iy dy =>
            rw [hr2] at hfound
            obtain ⟨rfl, rfl⟩ := hfound
            exact ih J.bisect.2 _ _ hsub2 hr2
          | BisectResult.noRoot =>
            rw [hr2] at hfound; exact (BisectResult.noConfusion hfound)
          | BisectResult.uncertain _ _ =>
            rw [hr2] at hfound; exact (BisectResult.noConfusion hfound)
        | BisectResult.uncertain Iu du =>
          rw [hr1] at hfound
          match hr2 : bisectRootIdx.go e ρ_int idx maxDepth J.bisect.2 n with
          | BisectResult.found Iy dy =>
            rw [hr2] at hfound
            obtain ⟨rfl, rfl⟩ := hfound
            exact ih J.bisect.2 _ _ hsub2 hr2
          | BisectResult.noRoot =>
            rw [hr2] at hfound; exact (BisectResult.noConfusion hfound)
          | BisectResult.uncertain Iv dv =>
            -- uncertain/uncertain: result is always uncertain (width comparison)
            rw [hr2] at hfound
            -- Simplify: both branches of the if give uncertain, never found
            simp only [Bool.false_eq_true, ↓reduceIte] at hfound
            split_ifs at hfound

/-- Correctness theorem for bisectRootIdx when it finds a root.
    If bisectRootIdx returns `found I d`, then for any ρ_real satisfying ρ_int,
    there exists a root of `evalAlong e ρ_real idx` in the returned interval I. -/
theorem bisectRootIdx_found_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth : ℕ)
    (I : IntervalRat) (d : ℕ)
    (hfound : bisectRootIdx e ρ_int idx maxDepth = BisectResult.found I d)
    (ρ_real : Nat → ℝ) (hρ : ∀ i, i ≠ idx → ρ_real i ∈ ρ_int i)
    (hCont : ContinuousOn (Expr.evalAlong e ρ_real idx)
              (Set.Icc (I.lo : ℝ) (I.hi : ℝ))) :
    ∃ x ∈ I, Expr.evalAlong e ρ_real idx x = 0 := by
  -- First extract that signChange_idx is true for the found interval
  simp only [bisectRootIdx] at hfound
  have ⟨hsign, _⟩ := bisectRootIdx_go_found_signChange e ρ_int idx maxDepth maxDepth
    (ρ_int idx) I d (fun s hs => hs) hfound
  -- The interval in updateIntervalEnv' ρ_int idx I at idx is I
  have henv_eq : (updateIntervalEnv' ρ_int idx I) idx = I := by simp [updateIntervalEnv']
  -- Now use signChange_correct_idx with converted continuity
  have hCont' : ContinuousOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((updateIntervalEnv' ρ_int idx I idx).lo : ℝ)
        ((updateIntervalEnv' ρ_int idx I idx).hi : ℝ)) := by
    simp only [henv_eq]; exact hCont
  have hroot := signChange_correct_idx e hsupp (updateIntervalEnv' ρ_int idx I) idx ρ_real
    (fun i hi => by simp only [updateIntervalEnv']; rw [if_neg hi]; exact hρ i hi)
    hsign hCont'
  -- Convert from updateIntervalEnv' membership to I membership
  simp only [henv_eq] at hroot
  exact hroot

/-- Helper: noRoot is preserved through bisection.
    The proof is complex due to the match structure in bisectRootIdx.go.
    The key insight is that noRoot can only be returned if excludesZero is true
    at some level of the recursion, and excludesZero implies the function is nonzero. -/
theorem bisectRootIdx_go_noRoot_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth depth : ℕ) (J : IntervalRat)
    (hJ_sub : ∀ t, t ∈ J → t ∈ ρ_int idx)
    (hnoRoot : bisectRootIdx.go e ρ_int idx maxDepth J depth = BisectResult.noRoot) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ J, Expr.evalAlong e ρ_real idx t ≠ 0 := by
  induction depth generalizing J with
  | zero =>
    unfold bisectRootIdx.go at hnoRoot
    by_cases hexcl : excludesZero (evalInterval e (updateIntervalEnv' ρ_int idx J)) = true
    · -- excludesZero case: use excludesZero_correct_idx
      intro ρ_real hρ t ht
      simp only [Expr.evalAlong]
      -- Build the updated env that matches the excludesZero check
      have hρ' : ∀ i, Expr.updateVar ρ_real idx t i ∈ updateIntervalEnv' ρ_int idx J i := by
        intro i
        simp only [Expr.updateVar, updateIntervalEnv']
        split_ifs with hi
        · exact ht
        · exact hρ i
      exact excludesZero_correct_idx e hsupp (updateIntervalEnv' ρ_int idx J) hexcl
        (Expr.updateVar ρ_real idx t) hρ'
    · -- Not excludesZero at depth=0: contradiction cases
      simp only [hexcl, Bool.false_eq_true, ↓reduceIte] at hnoRoot
      by_cases hsign : signChange_idx e (updateIntervalEnv' ρ_int idx J) idx = true
      · simp only [hsign] at hnoRoot
        exact (BisectResult.noConfusion hnoRoot)
      · simp only [hsign] at hnoRoot
        exact (BisectResult.noConfusion hnoRoot)
  | succ n ih =>
    unfold bisectRootIdx.go at hnoRoot
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hnoRoot
    by_cases hexcl : excludesZero (evalInterval e (updateIntervalEnv' ρ_int idx J)) = true
    · -- excludesZero case
      intro ρ_real hρ t ht
      simp only [Expr.evalAlong]
      have hρ' : ∀ i, Expr.updateVar ρ_real idx t i ∈ updateIntervalEnv' ρ_int idx J i := by
        intro i
        simp only [Expr.updateVar, updateIntervalEnv']
        split_ifs with hi
        · exact ht
        · exact hρ i
      exact excludesZero_correct_idx e hsupp (updateIntervalEnv' ρ_int idx J) hexcl
        (Expr.updateVar ρ_real idx t) hρ'
    · -- Bisection case
      simp only [hexcl, Bool.false_eq_true, ↓reduceIte] at hnoRoot
      by_cases hsign : signChange_idx e (updateIntervalEnv' ρ_int idx J) idx = true
      · simp only [hsign] at hnoRoot
        exact (BisectResult.noConfusion hnoRoot)
      · simp only [hsign] at hnoRoot
        -- Analyze the match structure for noRoot
        have hsub1 : ∀ t, t ∈ J.bisect.1 → t ∈ ρ_int idx := fun t ht =>
          hJ_sub t (IntervalRat.mem_of_mem_bisect_left ht)
        have hsub2 : ∀ t, t ∈ J.bisect.2 → t ∈ ρ_int idx := fun t ht =>
          hJ_sub t (IntervalRat.mem_of_mem_bisect_right ht)
        -- noRoot is returned only when both halves return noRoot
        match hr1 : bisectRootIdx.go e ρ_int idx maxDepth J.bisect.1 n with
        | BisectResult.found _ _ =>
          rw [hr1] at hnoRoot
          simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
          exact (BisectResult.noConfusion hnoRoot)
        | BisectResult.noRoot =>
          rw [hr1] at hnoRoot
          match hr2 : bisectRootIdx.go e ρ_int idx maxDepth J.bisect.2 n with
          | BisectResult.found _ _ =>
            rw [hr2] at hnoRoot
            simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
            exact (BisectResult.noConfusion hnoRoot)
          | BisectResult.noRoot =>
            rw [hr2] at hnoRoot
            simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
            -- Both halves return noRoot, so use IH on both
            intro ρ_real hρ t ht
            -- t is in either left or right half
            rcases mem_bisect_cases J t ht with ht1 | ht2
            · exact ih J.bisect.1 hsub1 hr1 ρ_real hρ t ht1
            · exact ih J.bisect.2 hsub2 hr2 ρ_real hρ t ht2
          | BisectResult.uncertain _ _ =>
            rw [hr2] at hnoRoot
            simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
            exact (BisectResult.noConfusion hnoRoot)
        | BisectResult.uncertain _ _ =>
          rw [hr1] at hnoRoot
          match hr2 : bisectRootIdx.go e ρ_int idx maxDepth J.bisect.2 n with
          | BisectResult.found _ _ =>
            rw [hr2] at hnoRoot
            simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
            exact (BisectResult.noConfusion hnoRoot)
          | BisectResult.noRoot =>
            rw [hr2] at hnoRoot
            simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
            exact (BisectResult.noConfusion hnoRoot)
          | BisectResult.uncertain _ _ =>
            rw [hr2] at hnoRoot
            simp only [Bool.false_eq_true, ↓reduceIte] at hnoRoot
            split_ifs at hnoRoot

/-- Correctness theorem for bisectRootIdx when it reports no root.
    If bisectRootIdx returns `noRoot`, then for any ρ_real satisfying ρ_int,
    the function `evalAlong e ρ_real idx` has no zeros in `ρ_int idx`. -/
theorem bisectRootIdx_noRoot_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth : ℕ)
    (hnoRoot : bisectRootIdx e ρ_int idx maxDepth = BisectResult.noRoot) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ ρ_int idx, Expr.evalAlong e ρ_real idx t ≠ 0 := by
  intro ρ_real hρ t ht
  simp only [bisectRootIdx] at hnoRoot
  exact bisectRootIdx_go_noRoot_correct e hsupp ρ_int idx maxDepth maxDepth (ρ_int idx)
    (fun s hs => hs) hnoRoot ρ_real hρ t ht

end LeanBound.Numerics
