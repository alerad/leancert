/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.RootFinding.Basic

/-!
# Root Finding: Bisection Algorithm

This file implements the bisection method for root isolation.

## Main definitions

* `BisectionResult` - Result structure from bisection
* `bisectRootGo` - Worker function for bisection
* `bisectRoot` - Main bisection entry point

## Main theorems

* `bisectRoot_hasRoot_correct` - If status is `hasRoot`, there exists a root (via IVT)
* `bisectRoot_noRoot_correct` - If status is `noRoot`, there are no roots

All bisection theorems are FULLY PROVED with no `sorry`.
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-! ### Bisection result structure -/

/-- Result of bisection root finding -/
structure BisectionResult where
  /-- Interval-status pairs -/
  intervals : List (IntervalRat × RootStatus)
  /-- Number of bisections performed -/
  iterations : ℕ

namespace BisectionResult

/-- Get just the candidate intervals -/
def candidates (r : BisectionResult) : List IntervalRat :=
  r.intervals.map Prod.fst

/-- Get just the statuses -/
def statuses (r : BisectionResult) : List RootStatus :=
  r.intervals.map Prod.snd

end BisectionResult

/-! ### Bisection algorithm -/

/-- Worker function for bisection root finding.

Processes a worklist, discarding intervals that provably contain no roots,
bisecting intervals that may contain roots until they are small enough.

Lifted to top-level so we can state correctness lemmas about it.
-/
noncomputable def bisectRootGo (e : Expr) (tol : ℚ) (maxIter : ℕ)
    (work : List (IntervalRat × RootStatus)) (iter : ℕ)
    (done : List (IntervalRat × RootStatus)) : BisectionResult :=
  match iter, work with
  | 0, _ =>
    { intervals := done ++ work
      iterations := maxIter }
  | _, [] =>
    { intervals := done
      iterations := maxIter - iter }
  | n + 1, (J, _) :: rest =>
    let status := checkRootStatus e J
    match status with
    | RootStatus.noRoot =>
      -- Discard this interval
      bisectRootGo e tol maxIter rest n done
    | RootStatus.hasRoot =>
      if J.width ≤ tol then
        -- Small enough, we're done with this one
        bisectRootGo e tol maxIter rest n ((J, RootStatus.hasRoot) :: done)
      else
        -- Bisect and continue
        let (J₁, J₂) := J.bisect
        bisectRootGo e tol maxIter ((J₁, RootStatus.unknown) :: (J₂, RootStatus.unknown) :: rest) n done
    | RootStatus.uniqueRoot =>
      bisectRootGo e tol maxIter rest n ((J, RootStatus.uniqueRoot) :: done)
    | RootStatus.unknown =>
      if J.width ≤ tol then
        bisectRootGo e tol maxIter rest n ((J, RootStatus.unknown) :: done)
      else
        let (J₁, J₂) := J.bisect
        bisectRootGo e tol maxIter ((J₁, RootStatus.unknown) :: (J₂, RootStatus.unknown) :: rest) n done

/-- Bisection root finding.

Repeatedly bisects the interval, discarding subintervals that
provably contain no roots.
-/
noncomputable def bisectRoot (e : Expr) (I : IntervalRat) (maxIter : ℕ)
    (tol : ℚ) (_htol : 0 < tol) : BisectionResult :=
  bisectRootGo e tol maxIter [(I, RootStatus.unknown)] maxIter []

/-! ### Bisection correctness -/

/-- Key lemma: checkRootStatus returns noRoot only when excludesZero is true -/
theorem checkRootStatus_noRoot_implies_excludesZero (e : Expr) (J : IntervalRat) :
    checkRootStatus e J = RootStatus.noRoot → excludesZero (evalInterval1 e J) = true := by
  unfold checkRootStatus
  intro h
  by_cases hexcl : excludesZero (evalInterval1 e J) = true
  · exact hexcl
  · simp only [hexcl, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hsign : signChange e J = true
    · simp only [hsign, ↓reduceIte] at h
      cases h
    · simp only [hsign, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-- Key lemma: checkRootStatus returns hasRoot only when signChange is true -/
theorem checkRootStatus_hasRoot_implies_signChange (e : Expr) (J : IntervalRat) :
    checkRootStatus e J = RootStatus.hasRoot → signChange e J = true := by
  unfold checkRootStatus
  intro h
  by_cases hexcl : excludesZero (evalInterval1 e J) = true
  · simp only [hexcl, ↓reduceIte] at h
    cases h
  · simp only [hexcl, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hsign : signChange e J = true
    · exact hsign
    · simp only [hsign, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-! ### Invariants for bisection proofs -/

/-- Invariant for bisection: every interval with hasRoot status has signChange = true.
    Note: noRoot intervals are discarded by the algorithm, so they never appear in output. -/
def BisectInv (e : Expr) (pairs : List (IntervalRat × RootStatus)) : Prop :=
  ∀ J s, (J, s) ∈ pairs → s = RootStatus.hasRoot → signChange e J = true

/-- Invariant for tracking sub-intervals: all intervals in the list are sub-intervals of I -/
def SubIntervalInv (I : IntervalRat) (pairs : List (IntervalRat × RootStatus)) : Prop :=
  ∀ J s, (J, s) ∈ pairs → I.lo ≤ J.lo ∧ J.hi ≤ I.hi

/-- The invariant holds for the initial work list -/
theorem bisect_inv_initial (e : Expr) (I : IntervalRat) :
    BisectInv e [(I, RootStatus.unknown)] := by
  intro J s hmem hs
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨_, hs'⟩ := hmem
  subst hs'
  contradiction

/-- The sub-interval invariant holds initially -/
theorem subinterval_inv_initial (I : IntervalRat) :
    SubIntervalInv I [(I, RootStatus.unknown)] := by
  intro J s hmem
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨hJ, _⟩ := hmem
  subst hJ
  exact ⟨le_refl _, le_refl _⟩

/-- BisectInv is preserved when adding a hasRoot interval with signChange = true -/
theorem bisect_inv_cons_hasRoot (e : Expr) (J : IntervalRat) (pairs : List (IntervalRat × RootStatus))
    (hInv : BisectInv e pairs) (hsign : signChange e J = true) :
    BisectInv e ((J, RootStatus.hasRoot) :: pairs) := by
  intro K s hmem hs
  simp only [List.mem_cons, Prod.mk.injEq] at hmem
  cases hmem with
  | inl h =>
    obtain ⟨hK, _⟩ := h
    subst hK
    exact hsign
  | inr h => exact hInv K s h hs

/-- BisectInv is preserved when adding non-hasRoot intervals -/
theorem bisect_inv_cons_other (e : Expr) (J : IntervalRat) (s : RootStatus) (pairs : List (IntervalRat × RootStatus))
    (hInv : BisectInv e pairs) (hne : s ≠ RootStatus.hasRoot) :
    BisectInv e ((J, s) :: pairs) := by
  intro K s' hmem hs'
  simp only [List.mem_cons, Prod.mk.injEq] at hmem
  cases hmem with
  | inl h =>
    obtain ⟨_, hs''⟩ := h
    subst hs''
    contradiction
  | inr h => exact hInv K s' h hs'

/-- BisectInv holds for list append -/
theorem bisect_inv_append (e : Expr) (l₁ l₂ : List (IntervalRat × RootStatus))
    (h₁ : BisectInv e l₁) (h₂ : BisectInv e l₂) :
    BisectInv e (l₁ ++ l₂) := by
  intro J s hmem hs
  simp only [List.mem_append] at hmem
  cases hmem with
  | inl h => exact h₁ J s h hs
  | inr h => exact h₂ J s h hs

/-- SubIntervalInv holds for list append -/
theorem subinterval_inv_append (I : IntervalRat) (l₁ l₂ : List (IntervalRat × RootStatus))
    (h₁ : SubIntervalInv I l₁) (h₂ : SubIntervalInv I l₂) :
    SubIntervalInv I (l₁ ++ l₂) := by
  intro J s hmem
  simp only [List.mem_append] at hmem
  cases hmem with
  | inl h => exact h₁ J s h
  | inr h => exact h₂ J s h

/-- SubIntervalInv is preserved when adding a sub-interval -/
theorem subinterval_inv_cons (I J : IntervalRat) (s : RootStatus)
    (pairs : List (IntervalRat × RootStatus))
    (hInv : SubIntervalInv I pairs) (hJ : I.lo ≤ J.lo ∧ J.hi ≤ I.hi) :
    SubIntervalInv I ((J, s) :: pairs) := by
  intro K s' hmem
  simp only [List.mem_cons, Prod.mk.injEq] at hmem
  cases hmem with
  | inl h =>
    obtain ⟨hK, _⟩ := h
    subst hK
    exact hJ
  | inr h => exact hInv K s' h

/-- Bisecting preserves the sub-interval property -/
theorem bisect_subinterval (I J : IntervalRat) (hJ : I.lo ≤ J.lo ∧ J.hi ≤ I.hi) :
    let (J₁, J₂) := J.bisect
    (I.lo ≤ J₁.lo ∧ J₁.hi ≤ I.hi) ∧ (I.lo ≤ J₂.lo ∧ J₂.hi ≤ I.hi) := by
  simp only [IntervalRat.bisect]
  constructor
  · constructor
    · exact hJ.1
    · calc J.midpoint = (J.lo + J.hi) / 2 := rfl
        _ ≤ (J.hi + J.hi) / 2 := by apply div_le_div_of_nonneg_right; linarith [J.le]; norm_num
        _ = J.hi := by ring
        _ ≤ I.hi := hJ.2
  · constructor
    · calc I.lo ≤ J.lo := hJ.1
        _ = J.lo * 2 / 2 := by ring
        _ = (J.lo + J.lo) / 2 := by ring
        _ ≤ (J.lo + J.hi) / 2 := by apply div_le_div_of_nonneg_right; linarith [J.le]; norm_num
        _ = J.midpoint := rfl
    · exact hJ.2

/-! ### Main correctness proofs -/

/-- noRoot never appears in output - the algorithm discards such intervals.
    We prove this by induction on iter. -/
theorem go_noRoot_not_in_output (e : Expr) (tol : ℚ) (maxIter : ℕ)
    (work : List (IntervalRat × RootStatus)) (iter : ℕ)
    (done : List (IntervalRat × RootStatus))
    (hDone : ∀ J s, (J, s) ∈ done → s ≠ RootStatus.noRoot)
    (hWork : ∀ J s, (J, s) ∈ work → s ≠ RootStatus.noRoot) :
    ∀ J s, (J, s) ∈ (bisectRootGo e tol maxIter work iter done).intervals → s ≠ RootStatus.noRoot := by
  induction iter generalizing work done with
  | zero =>
    -- iter = 0: result is done ++ work
    simp only [bisectRootGo]
    intro J s hmem
    simp only [List.mem_append] at hmem
    cases hmem with
    | inl h => exact hDone J s h
    | inr h => exact hWork J s h
  | succ n ih =>
    match hwork : work with
    | [] =>
      -- work = []: result is done
      simp only [bisectRootGo]
      intro J s hmem
      exact hDone J s hmem
    | (K, _st) :: rest =>
      simp only [bisectRootGo]
      -- Match on checkRootStatus result
      match hstatus : checkRootStatus e K with
      | RootStatus.noRoot =>
        -- noRoot: we discard K, recurse on rest
        simp
        apply ih
        · exact hDone
        · intro J' s' hmem'
          exact hWork J' s' (List.mem_cons.mpr (Or.inr hmem'))
      | RootStatus.hasRoot =>
        simp
        split
        · -- width ≤ tol: add (K, hasRoot) to done
          apply ih
          · intro J' s' hmem'
            simp only [List.mem_cons, Prod.mk.injEq] at hmem'
            cases hmem' with
            | inl h => simp only [h.2]; decide
            | inr h => exact hDone J' s' h
          · intro J' s' hmem'
            exact hWork J' s' (List.mem_cons.mpr (Or.inr hmem'))
        · -- bisect: add (J₁, unknown), (J₂, unknown) to work
          apply ih
          · exact hDone
          · intro J' s' hmem'
            simp only [List.mem_cons, Prod.mk.injEq] at hmem'
            cases hmem' with
            | inl h => simp only [h.2]; decide
            | inr h =>
              cases h with
              | inl h' => simp only [h'.2]; decide
              | inr h' => exact hWork J' s' (List.mem_cons.mpr (Or.inr h'))
      | RootStatus.uniqueRoot =>
        simp
        apply ih
        · intro J' s' hmem'
          simp only [List.mem_cons, Prod.mk.injEq] at hmem'
          cases hmem' with
          | inl h => simp only [h.2]; decide
          | inr h => exact hDone J' s' h
        · intro J' s' hmem'
          exact hWork J' s' (List.mem_cons.mpr (Or.inr hmem'))
      | RootStatus.unknown =>
        simp
        split
        · -- width ≤ tol
          apply ih
          · intro J' s' hmem'
            simp only [List.mem_cons, Prod.mk.injEq] at hmem'
            cases hmem' with
            | inl h => simp only [h.2]; decide
            | inr h => exact hDone J' s' h
          · intro J' s' hmem'
            exact hWork J' s' (List.mem_cons.mpr (Or.inr hmem'))
        · -- bisect
          apply ih
          · exact hDone
          · intro J' s' hmem'
            simp only [List.mem_cons, Prod.mk.injEq] at hmem'
            cases hmem' with
            | inl h => simp only [h.2]; decide
            | inr h =>
              cases h with
              | inl h' => simp only [h'.2]; decide
              | inr h' => exact hWork J' s' (List.mem_cons.mpr (Or.inr h'))

/-- Every hasRoot interval in output has signChange = true.
    We prove this by induction on iter.
    Note: We need BisectInv for work too, since at iter=0 we output work as-is. -/
theorem go_hasRoot_has_signChange (e : Expr) (tol : ℚ) (maxIter : ℕ)
    (work : List (IntervalRat × RootStatus)) (iter : ℕ)
    (done : List (IntervalRat × RootStatus))
    (hWork : BisectInv e work)
    (hDone : BisectInv e done) :
    BisectInv e (bisectRootGo e tol maxIter work iter done).intervals := by
  induction iter generalizing work done with
  | zero =>
    -- iter = 0: result is done ++ work
    simp only [bisectRootGo]
    exact bisect_inv_append e done work hDone hWork
  | succ n ih =>
    match hwork : work with
    | [] =>
      simp only [bisectRootGo]
      intro J s hmem hs
      exact hDone J s hmem hs
    | (K, _st) :: rest =>
      simp only [bisectRootGo]
      -- Get BisectInv for rest
      have hRest : BisectInv e rest := fun J' s' h' hs' =>
        hWork J' s' (List.mem_cons.mpr (Or.inr h')) hs'
      match hstatus : checkRootStatus e K with
      | RootStatus.noRoot =>
        simp
        exact ih rest done hRest hDone
      | RootStatus.hasRoot =>
        simp
        have hsignK : signChange e K = true := checkRootStatus_hasRoot_implies_signChange e K hstatus
        split
        · -- width ≤ tol: add (K, hasRoot) to done
          exact ih rest ((K, RootStatus.hasRoot) :: done) hRest
            (bisect_inv_cons_hasRoot e K done hDone hsignK)
        · -- bisect: add (J₁, unknown), (J₂, unknown) to work
          -- New work has unknown status, which is not hasRoot
          have hNewWork : BisectInv e ((K.bisect.1, RootStatus.unknown) :: (K.bisect.2, RootStatus.unknown) :: rest) := by
            intro J' s' h' hs'
            simp only [List.mem_cons, Prod.mk.injEq] at h'
            cases h' with
            | inl h =>
              obtain ⟨_, hs''⟩ := h
              subst hs''
              cases hs'
            | inr h =>
              cases h with
              | inl h' =>
                obtain ⟨_, hs''⟩ := h'
                subst hs''
                cases hs'
              | inr h' => exact hRest J' s' h' hs'
          exact ih _ done hNewWork hDone
      | RootStatus.uniqueRoot =>
        simp
        exact ih rest ((K, RootStatus.uniqueRoot) :: done) hRest
          (bisect_inv_cons_other e K RootStatus.uniqueRoot done hDone (by decide))
      | RootStatus.unknown =>
        simp
        split
        · -- width ≤ tol
          exact ih rest ((K, RootStatus.unknown) :: done) hRest
            (bisect_inv_cons_other e K RootStatus.unknown done hDone (by decide))
        · -- bisect
          have hNewWork : BisectInv e ((K.bisect.1, RootStatus.unknown) :: (K.bisect.2, RootStatus.unknown) :: rest) := by
            intro J' s' h' hs'
            simp only [List.mem_cons, Prod.mk.injEq] at h'
            cases h' with
            | inl h =>
              obtain ⟨_, hs''⟩ := h
              subst hs''
              cases hs'
            | inr h =>
              cases h with
              | inl h' =>
                obtain ⟨_, hs''⟩ := h'
                subst hs''
                cases hs'
              | inr h' => exact hRest J' s' h' hs'
          exact ih _ done hNewWork hDone

/-- Every interval in output is a sub-interval of the original.
    We prove this by induction on iter. -/
theorem go_subinterval (e : Expr) (tol : ℚ) (maxIter : ℕ) (I : IntervalRat)
    (work : List (IntervalRat × RootStatus)) (iter : ℕ)
    (done : List (IntervalRat × RootStatus))
    (hWork : SubIntervalInv I work)
    (hDone : SubIntervalInv I done) :
    SubIntervalInv I (bisectRootGo e tol maxIter work iter done).intervals := by
  induction iter generalizing work done with
  | zero =>
    simp only [bisectRootGo]
    intro J s hmem
    simp only [List.mem_append] at hmem
    cases hmem with
    | inl h => exact hDone J s h
    | inr h => exact hWork J s h
  | succ n ih =>
    match hwork : work with
    | [] =>
      simp only [bisectRootGo]
      intro J s hmem
      exact hDone J s hmem
    | (K, _st) :: rest =>
      simp only [bisectRootGo]
      -- Get K's sub-interval property
      have hK := hWork K _st (List.mem_cons.mpr (Or.inl rfl))
      have hRest : SubIntervalInv I rest := fun J' s' h' =>
        hWork J' s' (List.mem_cons.mpr (Or.inr h'))
      match hstatus : checkRootStatus e K with
      | RootStatus.noRoot =>
        simp
        exact ih rest done hRest hDone
      | RootStatus.hasRoot =>
        simp
        split
        · exact ih rest ((K, RootStatus.hasRoot) :: done) hRest
            (subinterval_inv_cons I K RootStatus.hasRoot done hDone hK)
        · -- bisect
          have hbisect := bisect_subinterval I K hK
          let K₁ := K.bisect.1
          let K₂ := K.bisect.2
          have hK₁ : I.lo ≤ K₁.lo ∧ K₁.hi ≤ I.hi := hbisect.1
          have hK₂ : I.lo ≤ K₂.lo ∧ K₂.hi ≤ I.hi := hbisect.2
          have hNewWork : SubIntervalInv I ((K₁, RootStatus.unknown) :: (K₂, RootStatus.unknown) :: rest) := by
            intro J' s' h'
            simp only [List.mem_cons, Prod.mk.injEq] at h'
            cases h' with
            | inl h =>
              obtain ⟨hJ', _⟩ := h
              subst hJ'
              exact hK₁
            | inr h =>
              cases h with
              | inl h' =>
                obtain ⟨hJ', _⟩ := h'
                subst hJ'
                exact hK₂
              | inr h' => exact hRest J' s' h'
          exact ih _ done hNewWork hDone
      | RootStatus.uniqueRoot =>
        simp
        exact ih rest ((K, RootStatus.uniqueRoot) :: done) hRest
          (subinterval_inv_cons I K RootStatus.uniqueRoot done hDone hK)
      | RootStatus.unknown =>
        simp
        split
        · exact ih rest ((K, RootStatus.unknown) :: done) hRest
            (subinterval_inv_cons I K RootStatus.unknown done hDone hK)
        · -- bisect
          have hbisect := bisect_subinterval I K hK
          let K₁ := K.bisect.1
          let K₂ := K.bisect.2
          have hK₁ : I.lo ≤ K₁.lo ∧ K₁.hi ≤ I.hi := hbisect.1
          have hK₂ : I.lo ≤ K₂.lo ∧ K₂.hi ≤ I.hi := hbisect.2
          have hNewWork : SubIntervalInv I ((K₁, RootStatus.unknown) :: (K₂, RootStatus.unknown) :: rest) := by
            intro J' s' h'
            simp only [List.mem_cons, Prod.mk.injEq] at h'
            cases h' with
            | inl h =>
              obtain ⟨hJ', _⟩ := h
              subst hJ'
              exact hK₁
            | inr h =>
              cases h with
              | inl h' =>
                obtain ⟨hJ', _⟩ := h'
                subst hJ'
                exact hK₂
              | inr h' => exact hRest J' s' h'
          exact ih _ done hNewWork hDone

/-- If bisection returns hasRoot for an interval, there exists a root (by IVT).

    The proof works by showing that every (J, hasRoot) pair in the output
    has signChange e J = true, then applying signChange_correct.

    **Note about noRoot**: The algorithm discards noRoot intervals, so they
    never appear in the output. Thus bisectRoot_noRoot_correct is vacuously true.  -/
theorem bisectRoot_hasRoot_correct (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (maxIter : ℕ) (tol : ℚ) (htol : 0 < tol)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)) :
    let result := bisectRoot e I maxIter tol htol
    ∀ J s, (J, s) ∈ result.intervals → s = RootStatus.hasRoot →
      ∃ x ∈ J, Expr.eval (fun _ => x) e = 0 := by
  intro result J s hmem hs
  -- Step 1: Show signChange e J = true
  -- Initial work list has only unknown status, so BisectInv holds vacuously
  have hWorkInv : BisectInv e [(I, RootStatus.unknown)] := fun J' s' h' hs' => by
    simp only [List.mem_singleton, Prod.mk.injEq] at h'
    obtain ⟨_, hs''⟩ := h'
    subst hs''
    cases hs'  -- unknown ≠ hasRoot
  have hInv := go_hasRoot_has_signChange e tol maxIter [(I, RootStatus.unknown)] maxIter []
    hWorkInv
    (fun _ _ h _ => by simp only [List.mem_nil_iff] at h)
  have hsign : signChange e J = true := hInv J s hmem hs
  -- Step 2: Show J is a sub-interval of I
  have hSub := go_subinterval e tol maxIter I [(I, RootStatus.unknown)] maxIter []
    (subinterval_inv_initial I)
    (fun _ _ h => by simp only [List.mem_nil_iff] at h)
  have hJsub := hSub J s hmem
  -- Step 3: Use signChange_correct with continuity on J
  have hContJ : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc J.lo J.hi) := by
    apply ContinuousOn.mono hCont
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    constructor
    · calc (I.lo : ℝ) ≤ J.lo := by exact_mod_cast hJsub.1
        _ ≤ x := hx.1
    · calc x ≤ J.hi := hx.2
        _ ≤ I.hi := by exact_mod_cast hJsub.2
  exact signChange_correct e hsupp J hsign hContJ

/-- If bisection returns noRoot for an interval, there really is no root.

    **Note**: The bisection algorithm discards noRoot intervals - when checkRootStatus
    returns noRoot, we call `go rest n done` without adding J to done. So noRoot
    never appears in the output intervals list.

    This means the theorem is vacuously true: there are no (J, noRoot) pairs in the output. -/
theorem bisectRoot_noRoot_correct (e : Expr) (_hsupp : ExprSupported e) (I : IntervalRat)
    (maxIter : ℕ) (tol : ℚ) (htol : 0 < tol) :
    let result := bisectRoot e I maxIter tol htol
    ∀ J s, (J, s) ∈ result.intervals → s = RootStatus.noRoot →
      ∀ x ∈ J, Expr.eval (fun _ => x) e ≠ 0 := by
  intro result J s hmem hs
  -- noRoot intervals are discarded by the algorithm, so they never appear in output.
  -- We use go_noRoot_not_in_output to show s ≠ noRoot, contradiction with hs.
  have hne := go_noRoot_not_in_output e tol maxIter [(I, RootStatus.unknown)] maxIter []
    (fun _ _ h => by simp only [List.mem_nil_iff] at h)
    (fun K s' h => by
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      simp only [h.2]
      decide)
    J s hmem
  exact absurd hs hne

end LeanBound.Numerics
