/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalRefined
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine
import LeanCert.Engine.Affine.Basic
import LeanCert.Engine.Affine.Environment
import LeanCert.Engine.Optimization.Box
import LeanCert.Engine.Optimization.Gradient

-- Suppress linter warnings for redundant tactics in all_goals first blocks
-- These proofs use first to handle multiple cases robustly, but some branches
-- may be redundant depending on which goals split_ifs generates
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Global Optimization via Branch-and-Bound

This file implements a branch-and-bound algorithm for rigorous global optimization
of expressions over n-dimensional boxes.

## Main definitions

* `GlobalBound` - Result of global optimization (lower bound and optional upper bound)
* `globalMinimize` - Branch-and-bound minimization over a box
* `globalMaximize` - Branch-and-bound maximization over a box

## Algorithm

The branch-and-bound algorithm works by:
1. Evaluating the expression over the current box using interval arithmetic
2. Using the interval lower bound to prune boxes that can't contain the minimum
3. Splitting the widest dimension when bounds aren't tight enough
4. Optionally pruning using monotonicity (gradient sign information)

## Correctness

The algorithm maintains the invariant that the returned lower bound is ≤ f(x)
for all x in the original box. When the interval upper bound equals the lower
bound (or is close enough), we have found the global minimum.
-/

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Affine

/-! ### Configuration -/

/-- Configuration for global optimization -/
structure GlobalOptConfig where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 1000
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning (requires gradient computation) -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr

instance : Inhabited GlobalOptConfig := ⟨{}⟩

/-! ### Result types -/

/-- Result of global optimization -/
structure GlobalBound where
  /-- Lower bound: f(x) ≥ lo for all x in the box -/
  lo : ℚ
  /-- Upper bound: there exists x in box with f(x) ≤ hi -/
  hi : ℚ
  /-- Best box found (smallest interval containing minimum) -/
  bestBox : Box
  /-- Number of iterations used -/
  iterations : Nat
  deriving Repr

/-- Result of optimization with certificate data -/
structure GlobalResult where
  /-- The computed bound -/
  bound : GlobalBound
  /-- Priority queue of remaining boxes (for resumption) -/
  remainingBoxes : List (ℚ × Box)  -- (lower bound, box)
  deriving Repr

/-! ### Priority queue operations -/

/-- Insert a box with its lower bound into a sorted list (ascending by bound) -/
def insertByBound (queue : List (ℚ × Box)) (lb : ℚ) (B : Box) : List (ℚ × Box) :=
  match queue with
  | [] => [(lb, B)]
  | (lb', B') :: rest =>
    if lb ≤ lb' then (lb, B) :: queue
    else (lb', B') :: insertByBound rest lb B

theorem mem_insertByBound_iff (queue : List (ℚ × Box)) (lb : ℚ) (B : Box)
    (entry : ℚ × Box) :
    entry ∈ insertByBound queue lb B ↔ entry = (lb, B) ∨ entry ∈ queue := by
  induction queue with
  | nil => simp [insertByBound]
  | cons head tail ih =>
      simp only [insertByBound]
      split <;> simp [ih, or_left_comm]

/-- Pop the box with smallest lower bound -/
def popBest (queue : List (ℚ × Box)) : Option ((ℚ × Box) × List (ℚ × Box)) :=
  match queue with
  | [] => none
  | best :: rest => some (best, rest)

/-! ### Core algorithm -/

/-- Evaluate expression on a box and get interval bounds -/
noncomputable def evalOnBox (e : Expr) (hsupp : ADSupported e)
    (B : Box) (_cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalRefined e hsupp (Box.toEnv B)

/-- One step of branch-and-bound for minimization with explicit global-safe lower bound tracking.
    When `cfg.useMonotonicity` is true, applies gradient-based pruning before evaluation. -/
noncomputable def minimizeStep (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  match popBest queue with
  | none => none
  | some ((lb, B), rest) =>
    -- If this box's lower bound is already worse than best, skip it
    if lb > bestUB then
      -- Prune this box; bounds unchanged
      some (rest, bestLB, bestUB, bestBox)
    else
      -- Step 1: Optionally apply monotonicity-based pruning
      let B_curr :=
        if cfg.useMonotonicity then
          let grad := gradientIntervalN e B B.length
          (pruneBoxForMin B grad).1
        else B
      -- Step 2: Evaluate on (potentially pruned) box
      let I := evalOnBox e hsupp B_curr cfg
      -- Update the global-safe lower bound. This value is intentionally monotone
      -- downward, preserving the simple invariant `bestLB ≤ f(ρ)` on the original
      -- box. It is not the tightest lower bound over the active queue.
      let newBestLB := min bestLB I.lo
      -- Update best upper bound if we found a better one
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      -- Check if box is small enough
      if Box.maxWidth B_curr ≤ cfg.tolerance then
        -- Accept this box, continue with rest
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        -- Step 3: Split and add children
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := evalOnBox e hsupp B1 cfg
        let I2 := evalOnBox e hsupp B2 cfg
        -- Only add boxes that can potentially improve
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound for a fixed number of iterations with explicit global-safe
lower bound tracking. -/
noncomputable def minimizeLoop (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStep e hsupp cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoop e hsupp cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization over a box -/
noncomputable def globalMinimize (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBox e hsupp B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  let initialBestLB : ℚ := I.lo
  let initialBestUB : ℚ := I.hi
  let initialBestBox : Box := B
  minimizeLoop e hsupp cfg initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/-- Global maximization over a box (minimize -e) -/
noncomputable def globalMaximize (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimize (Expr.neg e) (.neg hsupp) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Computable versions for execution -/

/-- Evaluate expression on a box (computable version for ExprSupportedCore) -/
def evalOnBoxCore (e : Expr) (B : Box) (cfg : GlobalOptConfig) : IntervalRat :=
  LeanCert.Internal.Rational.evalTotalCore e (Box.toEnv B) { taylorDepth := cfg.taylorDepth }


/-- One step of branch-and-bound (computable version) with explicit bestLB tracking.
    When `cfg.useMonotonicity` is true, applies gradient-based pruning before evaluation. -/
def minimizeStepCore (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  match popBest queue with
  | none => none
  | some ((lb, B), rest) =>
    if lb > bestUB then
      -- Prune this box; bounds unchanged
      some (rest, bestLB, bestUB, bestBox)
    else
      -- Step 1: Optionally apply monotonicity-based pruning
      let B_curr :=
        if cfg.useMonotonicity then
          let grad := gradientIntervalCore e B { taylorDepth := cfg.taylorDepth }
          (pruneBoxForMin B grad).1
        else B
      -- Step 2: Evaluate on (potentially pruned) box
      let I := evalOnBoxCore e B_curr cfg
      -- Update global lower bound: min of old and this box's local lower bound
      let newBestLB := min bestLB I.lo
      -- Possibly improve upper bound
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      if Box.maxWidth B_curr ≤ cfg.tolerance then
        -- Box is small enough: don't split further
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        -- Step 3: Split and add children
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := evalOnBoxCore e B1 cfg
        let I2 := evalOnBoxCore e B2 cfg
        -- Insert children if they might improve the minimum
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound (computable version) with explicit bestLB tracking -/
def minimizeLoopCore (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepCore e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopCore e cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization (computable version) -/
def globalMinimizeCore (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBoxCore e B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  let initialBestLB : ℚ := I.lo
  let initialBestUB : ℚ := I.hi
  let initialBestBox : Box := B
  minimizeLoopCore e cfg initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/-- Global maximization (computable version) -/
def globalMaximizeCore (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimizeCore (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Correctness theorems -/

/-- The lower bound from interval evaluation is correct. -/
theorem evalOnBox_lo_correct (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    (evalOnBox e hsupp B cfg).lo ≤ Expr.eval ρ e := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalRefined_correct e hsupp ρ (Box.toEnv B) henv
  simp only [evalOnBox]
  exact hmem.1

/-- The upper bound from interval evaluation is correct (∃ point achieving it). -/
theorem evalOnBox_hi_correct (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    Expr.eval ρ e ≤ (evalOnBox e hsupp B cfg).hi := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalRefined_correct e hsupp ρ (Box.toEnv B) henv
  simp only [evalOnBox]
  exact hmem.2

/-- Helper: construct a midpoint environment for a box -/
noncomputable def Box.midpointEnv (B : Box) : Nat → ℝ :=
  fun i => if h : i < B.length then (B[i].midpoint : ℝ) else 0

/-- The midpoint environment is in the box -/
theorem Box.midpointEnv_mem (B : Box) : Box.envMem (Box.midpointEnv B) B := by
  intro ⟨i, hi⟩
  simp only [midpointEnv, hi, ↓reduceDIte]
  exact IntervalRat.midpoint_mem _

/-- The midpoint environment is zero outside the box -/
theorem Box.midpointEnv_zero (B : Box) : ∀ i, i ≥ B.length → Box.midpointEnv B i = 0 := by
  intro i hi
  simp only [midpointEnv]
  split_ifs with h
  · exact absurd h (not_lt.mpr hi)
  · rfl

/-- Helper lemma: split preserves box length -/
theorem Box.split_length_eq (B : Box) (d : Nat) :
    (Box.split B d).1.length = B.length ∧ (Box.split B d).2.length = B.length := by
  simp only [Box.split]
  split_ifs with h
  · constructor <;> simp only [List.length_set]
  · exact ⟨rfl, rfl⟩

/-- Helper lemma: splitWidest preserves box length -/
theorem Box.splitWidest_length_eq (B : Box) :
    (Box.splitWidest B).1.length = B.length ∧ (Box.splitWidest B).2.length = B.length :=
  Box.split_length_eq B (Box.widestDim B)

/-! ### Simplified correctness architecture with explicit global-safe lower bound tracking

The key idea: track both `bestLB` (a global-safe lower bound, not necessarily the
tightest active-queue lower bound) and `bestUB` (a global upper-bound witness)
explicitly.
This makes the invariants much simpler:
- (Global LB) For all ρ in the original box, bestLB ≤ f(ρ)
- (Global UB witness) There exists ρ* in bestBox such that f(ρ*) ≤ bestUB
- (Queue boxes are sub-boxes) Every B' in queue is a sub-box of the original box
-/

/-- Membership in insertByBound: element is either the inserted one or was in original -/
theorem mem_insertByBound (queue : List (ℚ × Box)) (lb : ℚ) (B : Box) (lb' : ℚ) (B' : Box) :
    (lb', B') ∈ insertByBound queue lb B ↔ (lb', B') = (lb, B) ∨ (lb', B') ∈ queue := by
  induction queue with
  | nil => simp only [insertByBound, List.mem_singleton]; tauto
  | cons hd tl ih =>
    simp only [insertByBound]
    split_ifs with h_le
    all_goals simp [List.mem_cons, *]
    all_goals tauto

/-- minimizeStep always returns some for non-empty queue -/
theorem minimizeStep_nonempty (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    ∃ result, minimizeStep e hsupp cfg (hd :: tl) bestLB bestUB bestBox = some result := by
  simp only [minimizeStep, popBest]
  split_ifs <;> exact ⟨_, rfl⟩

/-- Helper: bestUB only decreases during minimizeStep -/
theorem minimizeStep_bestUB_le (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestUB' ≤ bestUB := by
  cases queue with
  | nil => simp [minimizeStep, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStep, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, _, hUB, _⟩
    all_goals rw [← hUB]
    all_goals exact le_of_lt ‹_›

/-- Helper: bestLB only decreases during minimizeStep -/
theorem minimizeStep_bestLB_le (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestLB' ≤ bestLB := by
  cases queue with
  | nil => simp [minimizeStep, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStep, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, hLB, _, _⟩
    all_goals rw [← hLB]
    all_goals exact min_le_left _ _

/-- Helper: new queue entries either come from original tail or have lb ≤ newBestUB -/
theorem minimizeStep_queue_entries (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (lb : ℚ) (B' : Box) (hmem : (lb, B') ∈ queue') :
    (lb, B') ∈ tl ∨ lb ≤ bestUB' := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals rcases hStep with ⟨hQ, _, hUB, _⟩
  all_goals rw [← hQ] at hmem
  all_goals rw [← hUB]
  all_goals first
    | (rw [mem_insertByBound] at hmem
       rcases hmem with ⟨rfl, _⟩ | hmem
       · right; assumption
       · rw [mem_insertByBound] at hmem
         rcases hmem with ⟨rfl, _⟩ | hmem
         · right; assumption
         · left; exact hmem)
    | (rw [mem_insertByBound] at hmem
       rcases hmem with ⟨rfl, _⟩ | hmem
       · right; assumption
       · left; exact hmem)
    | (left; exact hmem)

/-- Helper: bestBox' is either bestBox or a subset of hd.2 (the pruned box B_curr).
    When monotonicity pruning is enabled, bestBox' may be the pruned version of hd.2. -/
theorem minimizeStep_bestBox_cases (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestBox' = bestBox ∨
    bestBox' = (if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2) := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals rcases hStep with ⟨_, _, _, hBox⟩
  all_goals rw [← hBox]
  all_goals first | left; rfl | right; simp_all

/-- Helper: queue entries in result are either from tl or splits of B_curr (the possibly pruned hd.2) -/
theorem minimizeStep_queue_boxes (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (lb : ℚ) (B' : Box) (hmem : (lb, B') ∈ queue') :
    let B_curr := if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2
    (lb, B') ∈ tl ∨ B' = (Box.splitWidest B_curr).1 ∨ B' = (Box.splitWidest B_curr).2 := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals first
    | (cases hStep; left; assumption)  -- prune case and small case
    | (rcases hStep with ⟨hQ, _, _, _⟩
       subst hQ  -- substitute queue' directly
       -- Simplify the goal using all hypotheses about the conditions
       simp_all only [ite_true, true_or]
       -- Now hmem can be in insertByBound forms or just tl
       -- The structure is insertByBound(insertByBound(tl, I1.lo, B1), I2.lo, B2)
       -- So first unpack gives B2 (splitWidest.2), second gives B1 (splitWidest.1)
       first
         | done  -- simp_all closed the goal
         | (-- Both children added: unwrap B2 first, then B1
            rw [mem_insertByBound] at hmem
            rcases hmem with ⟨rfl, _⟩ | hmem
            · right; right; rfl  -- B' = splitWidest.2
            · rw [mem_insertByBound] at hmem
              rcases hmem with ⟨rfl, _⟩ | hmem
              · right; left; rfl  -- B' = splitWidest.1
              · left; exact hmem)  -- B' ∈ tl
         | (-- Only B2 added
            rw [mem_insertByBound] at hmem
            rcases hmem with ⟨rfl, _⟩ | hmem
            · right; right; rfl
            · left; exact hmem)
         | (-- Only B1 added
            rw [mem_insertByBound] at hmem
            rcases hmem with ⟨rfl, _⟩ | hmem
            · right; left; rfl
            · left; exact hmem))

/-- Helper: bestUB' is achievable if bestUB is achievable -/
theorem minimizeStep_bestUB_achievable (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hBestUB : ∃ ρ, Box.envMem ρ bestBox ∧ (∀ i, i ≥ bestBox.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ bestUB) :
    ∃ ρ, Box.envMem ρ bestBox' ∧ (∀ i, i ≥ bestBox'.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ bestUB' := by
  simp only [minimizeStep, popBest] at hStep
  -- Handle all cases by explicit branching
  by_cases h_prune : hd.1 > bestUB
  · simp only [h_prune, ↓reduceIte] at hStep
    cases hStep; exact hBestUB
  · simp only [h_prune, ↓reduceIte] at hStep
    -- Define B_curr based on useMonotonicity
    set B_curr := if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2 with hB_curr
    -- Continue splitting the conditionals
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals first
      | (-- No improvement: (bestUB, bestBox) was kept
         rcases hStep with ⟨_, _, hUB, hBox⟩
         rw [← hBox, ← hUB]
         exact hBestUB)
      | (-- Improvement case: bestBox' = B_curr, bestUB' = (evalOnBox e B_curr cfg).hi
         rcases hStep with ⟨_, _, hUB, hBox⟩
         rw [← hBox, ← hUB]
         -- Use B_curr's midpoint
         use Box.midpointEnv B_curr
         refine ⟨Box.midpointEnv_mem B_curr, Box.midpointEnv_zero B_curr, ?_⟩
         exact evalOnBox_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
           (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr))

/-- Helper: if ρ is in a split of B, then ρ is in B -/
theorem Box.envMem_of_envMem_split (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    Box.envMem ρ (Box.split B d).1 → Box.envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.1)).length := by simp only [List.length_set]; exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · -- heq : d = i, so B[d] = B[i]
      subst heq
      exact IntervalRat.mem_of_mem_bisect_left hmem
    · exact hmem
  · exact h

theorem Box.envMem_of_envMem_split_right (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    Box.envMem ρ (Box.split B d).2 → Box.envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.2)).length := by simp only [List.length_set]; exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · subst heq
      exact IntervalRat.mem_of_mem_bisect_right hmem
    · exact hmem
  · exact h

/-- Helper: if ρ is in a split of B, then ρ is in B -/
theorem Box.envMem_of_envMem_splitWidest (B : Box) (ρ : Nat → ℝ) :
    (Box.envMem ρ (Box.splitWidest B).1 ∨ Box.envMem ρ (Box.splitWidest B).2) →
    Box.envMem ρ B := by
  unfold splitWidest
  intro h
  rcases h with h1 | h2
  · exact Box.envMem_of_envMem_split B (Box.widestDim B) ρ h1
  · exact Box.envMem_of_envMem_split_right B (Box.widestDim B) ρ h2

/-- Helper: splits preserve length -/
theorem Box.splitWidest_length (B : Box) :
    (Box.splitWidest B).1.length = B.length ∧ (Box.splitWidest B).2.length = B.length :=
  Box.split_length_eq B (Box.widestDim B)

/-! ### Key correctness theorem: minimizeStep preserves lower bound invariant -/

/-- Pruning returns a sub-box: any point in the pruned box is also in the original.
    This is a direct consequence of `pruneBoxForMin_subset` from Gradient.lean. -/
theorem pruneBoxForMin_sub_aux (B : Box) (grad : List IntervalRat) (ρ : Nat → ℝ)
    (h : Box.envMem ρ (pruneBoxForMin B grad).1) : Box.envMem ρ B :=
  pruneBoxForMin_subset B grad ρ h


/-- minimizeStep preserves the lower bound invariant.
    If bestLB ≤ f(ρ) for all ρ in origB before the step, then bestLB' ≤ f(ρ) for all ρ after. -/
theorem minimizeStep_preserves_LB (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e hsupp cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB' ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB') ∧
    (∀ lb B', (lb, B') ∈ queue' →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) := by
  cases hq : queue with
  | nil => simp [minimizeStep, popBest, hq] at hStep
  | cons hd tl =>
    simp only [hq, minimizeStep, popBest] at hStep
    by_cases h_prune : hd.1 > bestUB
    · -- Prune case: bounds unchanged
      simp only [h_prune, ↓reduceIte] at hStep
      cases hStep
      refine ⟨hLB, hUB, ?_⟩
      intro lb B' hmem ρ' hρ'
      have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
      exact hQueueSub lb B' h ρ' hρ'
    · -- Evaluate case
      simp only [h_prune, ↓reduceIte] at hStep
      -- Define B_curr for this branch
      set B_curr := if cfg.useMonotonicity then
          (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2 with hB_curr
      -- Split on remaining conditionals
      split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
      all_goals first
        | (-- Small box or split case, no split children: queue' = tl
           cases hStep
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound: min bestLB I.lo ≤ f(ρ) for all ρ in origB
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             have hmin_le : bestLB ⊓ (evalOnBox e hsupp B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBox e hsupp B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound: witness exists
             first
               | exact hUB
               | (-- Better UB found: use midpoint of B_curr
                  have hmem_hd : (hd.1, hd.2) ∈ queue := by simp only [hq]; exact List.mem_cons_self
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv hd.2)
                    (Box.midpointEnv_mem hd.2)
                  use Box.midpointEnv hd.2
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi; exact Box.midpointEnv_zero hd.2 i (hLen ▸ hi)
                  · exact evalOnBox_hi_correct e hsupp hd.2 cfg (Box.midpointEnv hd.2)
                      (Box.midpointEnv_mem hd.2) (Box.midpointEnv_zero hd.2))
           · -- Queue entries
             intro lb B' hmem ρ' hρ'
             have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
             exact hQueueSub lb B' h ρ' hρ')
        | (-- Split case with children
           rcases hStep with ⟨hQ, hLB', hUB', hBox'⟩
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound preserved
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             rw [← hLB']
             have hmin_le : bestLB ⊓ (evalOnBox e hsupp B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBox e hsupp B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound witness: two cases based on whether UB improved
             first
               | (-- No improvement: bestUB' = bestUB, use existing witness
                  rw [← hUB']
                  exact hUB)
               | (-- Improvement case: use pruneBoxForMin_sub_aux
                  -- Proof requires showing midpoint of B_curr is in origB
                  -- via B_curr ⊆ hd.2 ⊆ origB, and eval at midpoint ≤ bestUB'
                  -- All of this follows from pruneBoxForMin_sub_aux and pruneBoxForMin_subset
                  have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
                  rw [← hq] at hmem_hd
                  have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
                    intro ρ' hρ'
                    simp only [hB_curr] at hρ'
                    split_ifs at hρ' with h_mono
                    · exact pruneBoxForMin_sub_aux hd.2 _ ρ' hρ'
                    · exact hρ'
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv B_curr)
                    (hB_curr_sub (Box.midpointEnv B_curr) (Box.midpointEnv_mem B_curr))
                  use Box.midpointEnv B_curr
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi
                    have hlen_B_curr : B_curr.length = hd.2.length := by
                      simp only [hB_curr]
                      split_ifs with h_mono
                      · exact pruneBoxForMin_length hd.2 _
                      · rfl
                    exact Box.midpointEnv_zero B_curr i (hlen_B_curr.trans hLen ▸ hi)
                  · -- eval ≤ I.hi = bestUB' (in improvement case)
                    have heval := evalOnBox_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
                      (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr)
                    -- hUB' : (evalOnBox e B_curr cfg).hi = bestUB' in this branch
                    simp only [← hUB']
                    exact heval)
           · -- Queue entries: come from tail or splits of B_curr
             -- Uses pruneBoxForMin_sub_aux to show split children ⊆ B_curr ⊆ hd.2 ⊆ origB
             intro lb B' hmem ρ' hρ'
             rw [← hQ] at hmem
             have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
             rw [← hq] at hmem_hd
             have hhdSub := hQueueSub hd.1 hd.2 hmem_hd
             have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
               intro ρ'' hρ''
               simp only [hB_curr] at hρ''
               split_ifs at hρ'' with h_mono
               · exact pruneBoxForMin_sub_aux hd.2 _ ρ'' hρ''
               · exact hρ''
             have hlen_B_curr : B_curr.length = hd.2.length := by
               simp only [hB_curr]; split_ifs; exact pruneBoxForMin_length hd.2 _; rfl
             -- Queue entries can come from: rest (tail), or inserted split boxes B1/B2
             -- Queue construction: rest → maybe insertByBound _ B1 → maybe insertByBound _ B2
             -- Try multiple proof strategies to handle all conditional combinations
             first
               -- Case: came directly from tail (no insertByBound wrapper)
               | (have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                  rw [← hq] at h
                  exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B2 inserted (B2 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B1 inserted (B1 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Both inserted, B2 outermost then B1
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · rw [mem_insertByBound] at hmem
                    rcases hmem with ⟨_, rfl⟩ | hmem
                    · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                      have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                      exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                    · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                      rw [← hq] at h
                      exact hQueueSub lb B' h ρ' hρ'))

/-- The main loop correctness theorem with explicit bestLB tracking -/
theorem minimizeLoop_correct (e : Expr) (hsupp : ADSupported e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat)
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
    let result := minimizeLoop e hsupp cfg queue bestLB bestUB bestBox iters
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) →
        result.bound.lo ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧
        Expr.eval ρ e ≤ result.bound.hi) := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoop]
    exact ⟨hLB, hUB⟩
  | succ n ih =>
    simp only [minimizeLoop]
    cases hstep : minimizeStep e hsupp cfg queue bestLB bestUB bestBox with
    | none =>
      simp only
      exact ⟨hLB, hUB⟩
    | some result =>
      simp only
      -- Apply step lemma
      have ⟨hLB', hUB', hQueueSub'⟩ :=
        minimizeStep_preserves_LB e hsupp cfg origB queue bestLB bestUB bestBox
          result.1 result.2.1 result.2.2.1 result.2.2.2 hstep hLB hUB hQueueSub
      -- Apply IH
      exact ih result.1 result.2.1 result.2.2.1 result.2.2.2 hLB' hUB' hQueueSub'

/-- The key correctness theorem: globalMinimize returns a lower bound that is
    ≤ the minimum of f over any point in the original box. -/
theorem globalMinimize_lo_correct (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimize e hsupp B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimize]
  let I := evalOnBox e hsupp B cfg
  -- Initial invariants
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBox_lo_correct e hsupp B cfg ρ' hρ' hzero'
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBox_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoop_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0
  exact hResult.1 ρ hρ hzero

/-- There exists a point achieving (approximately) the upper bound. -/
theorem globalMinimize_hi_achievable (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ (globalMinimize e hsupp B cfg).bound.hi := by
  simp only [globalMinimize]
  let I := evalOnBox e hsupp B cfg
  -- Initial invariants
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBox_lo_correct e hsupp B cfg ρ' hρ' hzero'
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBox_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoop_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0
  exact hResult.2

/-! ### Correctness theorems for Core (computable) versions -/

/-- The lower bound from core interval evaluation is correct. -/
theorem evalOnBoxCore_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hdom : evalDomainValid e B.toEnv { taylorDepth := cfg.taylorDepth }) :
    (evalOnBoxCore e B cfg).lo ≤ Expr.eval ρ e := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalCore_correct e hsupp ρ (Box.toEnv B) henv { taylorDepth := cfg.taylorDepth } hdom
  simp only [evalOnBoxCore]
  exact hmem.1

/-- The upper bound from core interval evaluation is correct. -/
theorem evalOnBoxCore_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hdom : evalDomainValid e B.toEnv { taylorDepth := cfg.taylorDepth }) :
    Expr.eval ρ e ≤ (evalOnBoxCore e B cfg).hi := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalCore_correct e hsupp ρ (Box.toEnv B) henv { taylorDepth := cfg.taylorDepth } hdom
  simp only [evalOnBoxCore]
  exact hmem.2

/-- minimizeStepCore preserves the lower bound invariant.

    This version uses ExprSupportedCore with an explicit domain validity hypothesis
    for all boxes of the same length as origB. This is necessary because the
    branch-and-bound algorithm operates on sub-boxes that maintain the same length. -/
theorem minimizeStepCore_preserves_LB (e : Expr) (hsupp : ExprSupportedCore e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepCore e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length)
    (hdom : ∀ (B' : Box), B'.length = origB.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB' ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB') ∧
    (∀ lb B', (lb, B') ∈ queue' →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) := by
  cases hq : queue with
  | nil => simp [minimizeStepCore, popBest, hq] at hStep
  | cons hd tl =>
    simp only [hq, minimizeStepCore, popBest] at hStep
    by_cases h_prune : hd.1 > bestUB
    · -- Prune case: bounds unchanged
      simp only [h_prune, ↓reduceIte] at hStep
      cases hStep
      refine ⟨hLB, hUB, ?_⟩
      intro lb B' hmem ρ' hρ'
      have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
      exact hQueueSub lb B' h ρ' hρ'
    · -- Evaluate case
      simp only [h_prune, ↓reduceIte] at hStep
      -- Define B_curr for this branch (same as in minimizeStepCore)
      set B_curr := if cfg.useMonotonicity then
          (pruneBoxForMin hd.2 (gradientIntervalCore e hd.2 { taylorDepth := cfg.taylorDepth })).1
          else hd.2 with hB_curr
      -- Split on remaining conditionals
      split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
      all_goals first
        | (-- Small box or split case, no split children: queue' = tl
           cases hStep
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound: min bestLB I.lo ≤ f(ρ) for all ρ in origB
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             have hmin_le : bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound: witness exists
             first
               | exact hUB
               | (-- Better UB found: use midpoint of hd.2
                  have hmem_hd : (hd.1, hd.2) ∈ queue := by simp only [hq]; exact List.mem_cons_self
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv hd.2)
                    (Box.midpointEnv_mem hd.2)
                  use Box.midpointEnv hd.2
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi; exact Box.midpointEnv_zero hd.2 i (hLen ▸ hi)
                  · have hLen_hd := (hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv hd.2) (Box.midpointEnv_mem hd.2)).2
                    exact evalOnBoxCore_hi_correct e hsupp hd.2 cfg (Box.midpointEnv hd.2)
                      (Box.midpointEnv_mem hd.2) (Box.midpointEnv_zero hd.2) (hdom hd.2 hLen_hd))
           · -- Queue entries
             intro lb B' hmem ρ' hρ'
             have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
             exact hQueueSub lb B' h ρ' hρ')
        | (-- Split case with children
           rcases hStep with ⟨hQ, hLB', hUB', hBox'⟩
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound preserved
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             rw [← hLB']
             have hmin_le : bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound witness: two cases based on whether UB improved
             first
               | (-- No improvement: bestUB' = bestUB, use existing witness
                  rw [← hUB']
                  exact hUB)
               | (-- Improvement case: use pruneBoxForMin_sub_aux
                  have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
                  rw [← hq] at hmem_hd
                  have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
                    intro ρ' hρ'
                    simp only [hB_curr] at hρ'
                    split_ifs at hρ' with h_mono
                    · exact pruneBoxForMin_sub_aux hd.2 _ ρ' hρ'
                    · exact hρ'
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv B_curr)
                    (hB_curr_sub (Box.midpointEnv B_curr) (Box.midpointEnv_mem B_curr))
                  have hlen_B_curr : B_curr.length = hd.2.length := by
                    simp only [hB_curr]
                    split_ifs with h_mono
                    · exact pruneBoxForMin_length hd.2 _
                    · rfl
                  use Box.midpointEnv B_curr
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi
                    exact Box.midpointEnv_zero B_curr i (hlen_B_curr.trans hLen ▸ hi)
                  · -- eval ≤ I.hi = bestUB' (in improvement case)
                    have heval := evalOnBoxCore_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
                      (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr) (hdom B_curr (hlen_B_curr.trans hLen))
                    simp only [← hUB']
                    exact heval)
           · -- Queue entries: come from tail or splits of B_curr
             -- Uses pruneBoxForMin_sub_aux to show split children ⊆ B_curr ⊆ hd.2 ⊆ origB
             intro lb B' hmem ρ' hρ'
             rw [← hQ] at hmem
             have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
             rw [← hq] at hmem_hd
             have hhdSub := hQueueSub hd.1 hd.2 hmem_hd
             have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
               intro ρ'' hρ''
               simp only [hB_curr] at hρ''
               split_ifs at hρ'' with h_mono
               · exact pruneBoxForMin_sub_aux hd.2 _ ρ'' hρ''
               · exact hρ''
             have hlen_B_curr : B_curr.length = hd.2.length := by
               simp only [hB_curr]; split_ifs; exact pruneBoxForMin_length hd.2 _; rfl
             -- Queue entries can come from: rest (tail), or inserted split boxes B1/B2
             -- Queue construction: rest → maybe insertByBound _ B1 → maybe insertByBound _ B2
             -- Try multiple proof strategies to handle all conditional combinations
             first
               -- Case: came directly from tail (no insertByBound wrapper)
               | (have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                  rw [← hq] at h
                  exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B2 inserted (B2 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B1 inserted (B1 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Both inserted, B2 outermost then B1
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · rw [mem_insertByBound] at hmem
                    rcases hmem with ⟨_, rfl⟩ | hmem
                    · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                      have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                      exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                    · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                      rw [← hq] at h
                      exact hQueueSub lb B' h ρ' hρ'))

/-- The main loop correctness theorem for Core version -/
theorem minimizeLoopCore_correct (e : Expr) (hsupp : ExprSupportedCore e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat)
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length)
    (hdom : ∀ (B' : Box), B'.length = origB.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    let result := minimizeLoopCore e cfg queue bestLB bestUB bestBox iters
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) →
        result.bound.lo ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧
        Expr.eval ρ e ≤ result.bound.hi) := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoopCore]
    exact ⟨hLB, hUB⟩
  | succ n ih =>
    simp only [minimizeLoopCore]
    cases hstep : minimizeStepCore e cfg queue bestLB bestUB bestBox with
    | none =>
      simp only
      exact ⟨hLB, hUB⟩
    | some result =>
      simp only
      have ⟨hLB', hUB', hQueueSub'⟩ :=
        minimizeStepCore_preserves_LB e hsupp cfg origB queue bestLB bestUB bestBox
          result.1 result.2.1 result.2.2.1 result.2.2.2 hstep hLB hUB hQueueSub hdom
      exact ih result.1 result.2.1 result.2.2.1 result.2.2.2 hLB' hUB' hQueueSub'

/-- The key correctness theorem for Core version: globalMinimizeCore returns a lower bound
    that is ≤ the minimum of f over any point in the original box.

    This theorem requires a domain validity hypothesis for ExprSupportedCore expressions.
    For ADSupported expressions, use globalMinimizeCore_lo_correct_supported which
    derives domain validity automatically. -/
theorem globalMinimizeCore_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeCore e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeCore]
  let I := evalOnBoxCore e B cfg
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBoxCore_lo_correct e hsupp B cfg ρ' hρ' hzero' (hdom B rfl)
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBoxCore_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B) (hdom B rfl)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoopCore_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0 hdom
  exact hResult.1 ρ hρ hzero

/-- There exists a point achieving (approximately) the upper bound for Core version. -/
theorem globalMinimizeCore_hi_achievable (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ (globalMinimizeCore e B cfg).bound.hi := by
  simp only [globalMinimizeCore]
  let I := evalOnBoxCore e B cfg
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBoxCore_lo_correct e hsupp B cfg ρ' hρ' hzero' (hdom B rfl)
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBoxCore_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B) (hdom B rfl)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoopCore_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0 hdom
  exact hResult.2

/-- The lower bound is ≤ the upper bound.
    This follows from the existence of a witness: there's some ρ with f(ρ) ≤ hi,
    and lo ≤ f(ρ) for all ρ in B, so lo ≤ f(witness) ≤ hi. -/
theorem globalMinimizeCore_lo_le_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    (globalMinimizeCore e B cfg).bound.lo ≤ (globalMinimizeCore e B cfg).bound.hi := by
  -- Get the witness that achieves ≤ hi
  obtain ⟨ρ, hρ, hzero, hhi⟩ := globalMinimizeCore_hi_achievable e hsupp B cfg hdom
  -- Get that lo ≤ f(ρ) for this witness
  have hlo := globalMinimizeCore_lo_correct e hsupp B cfg hdom ρ hρ hzero
  -- Combine: lo ≤ f(ρ) ≤ hi, then cast back to ℚ
  have h : ((globalMinimizeCore e B cfg).bound.lo : ℝ) ≤ (globalMinimizeCore e B cfg).bound.hi :=
    calc ((globalMinimizeCore e B cfg).bound.lo : ℝ)
      ≤ Expr.eval ρ e := hlo
      _ ≤ (globalMinimizeCore e B cfg).bound.hi := hhi
  exact_mod_cast h

/-! ### Maximization correctness theorems -/

/-- The upper bound from globalMaximizeCore is correct: f(ρ) ≤ hi for all ρ in B. -/
theorem globalMaximizeCore_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeCore e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' hB'
    simp only [evalDomainValid]
    exact hdom B' hB'
  have hmin := globalMinimizeCore_lo_correct (Expr.neg e) hneg_supp B cfg hneg_dom ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  have h : Expr.eval ρ e ≤ (-(globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

/-- There exists a point achieving approximately the lower bound for maximization. -/
theorem globalMaximizeCore_lo_achievable (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      (globalMaximizeCore e B cfg).bound.lo ≤ Expr.eval ρ e := by
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' hB'
    simp only [evalDomainValid]
    exact hdom B' hB'
  obtain ⟨ρ, hρ, hzero, hhi⟩ := globalMinimizeCore_hi_achievable (Expr.neg e) hneg_supp B cfg hneg_dom
  use ρ, hρ, hzero
  simp only [Expr.eval_neg] at hhi
  have h : (-(globalMinimizeCore (Expr.neg e) B cfg).bound.hi : ℝ) ≤ Expr.eval ρ e := by linarith
  exact_mod_cast h

/-- The lower bound is ≤ the upper bound for maximization. -/
theorem globalMaximizeCore_lo_le_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    (globalMaximizeCore e B cfg).bound.lo ≤ (globalMaximizeCore e B cfg).bound.hi := by
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' hB'
    simp only [evalDomainValid]
    exact hdom B' hB'
  have h := globalMinimizeCore_lo_le_hi (Expr.neg e) hneg_supp B cfg hneg_dom
  linarith

/-! ### Dyadic backend versions for high-performance optimization

These variants use Dyadic arithmetic (n * 2^e) instead of rationals,
preventing denominator explosion for deep expressions. 10-100x faster
for complex expressions like neural networks. -/

/-- Configuration for Dyadic global optimization -/
structure GlobalOptConfigDyadic where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 1000
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning (requires gradient computation) -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  /-- Dyadic precision (minimum exponent for outward rounding) -/
  precision : Int := -53
  deriving Repr

instance : Inhabited GlobalOptConfigDyadic := ⟨{}⟩

/-- Evaluate expression on a box using Dyadic arithmetic -/
def evalOnBoxDyadic (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic) : IntervalRat :=
  let dyadicEnv : IntervalDyadicEnv := fun i =>
    let irat := B.getD i (IntervalRat.singleton 0)
    Core.IntervalDyadic.ofIntervalRat irat cfg.precision
  let dyadicCfg : DyadicConfig := {
    precision := cfg.precision,
    taylorDepth := cfg.taylorDepth,
  }
  let result := LeanCert.Internal.Dyadic.evalUnchecked e dyadicEnv dyadicCfg
  result.toIntervalRat

/-- One step of branch-and-bound using Dyadic arithmetic -/
def minimizeStepDyadic (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  match popBest queue with
  | none => none
  | some ((lb, B), rest) =>
    if lb > bestUB then
      some (rest, bestLB, bestUB, bestBox)
    else
      let B_curr :=
        if cfg.useMonotonicity then
          let grad := gradientIntervalCore e B { taylorDepth := cfg.taylorDepth }
          (pruneBoxForMin B grad).1
        else B
      let I := evalOnBoxDyadic e B_curr cfg
      let newBestLB := min bestLB I.lo
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      if Box.maxWidth B_curr ≤ cfg.tolerance then
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := evalOnBoxDyadic e B1 cfg
        let I2 := evalOnBoxDyadic e B2 cfg
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound loop using Dyadic arithmetic -/
def minimizeLoopDyadic (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepDyadic e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopDyadic e cfg queue' bestLB' bestUB' bestBox' n

/-- Helper: bestLB only decreases during minimizeStepDyadic. -/
theorem minimizeStepDyadic_bestLB_le (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepDyadic e cfg queue bestLB bestUB bestBox =
      some (queue', bestLB', bestUB', bestBox')) :
    bestLB' ≤ bestLB := by
  cases queue with
  | nil => simp [minimizeStepDyadic, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStepDyadic, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, hLB, _, _⟩
    all_goals rw [← hLB]
    all_goals exact min_le_left _ _

/-- Helper: minimizeLoopDyadic preserves the initial lower bound. -/
theorem minimizeLoopDyadic_bestLB_le (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    (minimizeLoopDyadic e cfg queue bestLB bestUB bestBox iters).bound.lo ≤ bestLB := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoopDyadic, le_refl]
  | succ n ih =>
    simp only [minimizeLoopDyadic]
    cases hstep : minimizeStepDyadic e cfg queue bestLB bestUB bestBox with
    | none =>
      exact le_rfl
    | some queue' =>
      rcases queue' with ⟨queue', bestLB', bestUB', bestBox'⟩
      have hstepLB :=
        minimizeStepDyadic_bestLB_le e cfg queue bestLB bestUB bestBox
          queue' bestLB' bestUB' bestBox' hstep
      have hrec := ih queue' bestLB' bestUB' bestBox'
      exact le_trans hrec hstepLB

/-- Global minimization using Dyadic arithmetic -/
def globalMinimizeDyadic (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic := {}) : GlobalResult :=
  let I := evalOnBoxDyadic e B cfg
  minimizeLoopDyadic e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations

/-- Global maximization using Dyadic arithmetic -/
def globalMaximizeDyadic (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic := {}) : GlobalResult :=
  let result := globalMinimizeDyadic (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Affine backend versions for tight bounds

These variants use Affine Arithmetic to track correlations between variables,
solving the "dependency problem" in interval arithmetic. For example:
- Interval: x - x on [-1, 1] gives [-2, 2]
- Affine: x - x on [-1, 1] gives [0, 0] (exact!) -/

/-- Configuration for Affine global optimization -/
structure GlobalOptConfigAffine where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 1000
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning (requires gradient computation) -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  /-- Max noise symbols before consolidation (0 = no limit) -/
  maxNoiseSymbols : Nat := 0
  deriving Repr

instance : Inhabited GlobalOptConfigAffine := ⟨{}⟩

/-- Evaluate expression on a box using Affine arithmetic -/
def evalOnBoxAffine (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine) : IntervalRat :=
  let affineEnv := toAffineEnv B
  let affineCfg : AffineConfig := {
    taylorDepth := cfg.taylorDepth,
    maxNoiseSymbols := cfg.maxNoiseSymbols
  }
  let result := LeanCert.Internal.Affine.evalUnchecked e affineEnv affineCfg
  result.toInterval

/-- One step of branch-and-bound using Affine arithmetic -/
def minimizeStepAffine (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  match popBest queue with
  | none => none
  | some ((lb, B), rest) =>
    if lb > bestUB then
      some (rest, bestLB, bestUB, bestBox)
    else
      let B_curr :=
        if cfg.useMonotonicity then
          let grad := gradientIntervalCore e B { taylorDepth := cfg.taylorDepth }
          (pruneBoxForMin B grad).1
        else B
      let I := evalOnBoxAffine e B_curr cfg
      let newBestLB := min bestLB I.lo
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      if Box.maxWidth B_curr ≤ cfg.tolerance then
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := evalOnBoxAffine e B1 cfg
        let I2 := evalOnBoxAffine e B2 cfg
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound loop using Affine arithmetic -/
def minimizeLoopAffine (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepAffine e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopAffine e cfg queue' bestLB' bestUB' bestBox' n

/-- Helper: bestLB only decreases during minimizeStepAffine. -/
theorem minimizeStepAffine_bestLB_le (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepAffine e cfg queue bestLB bestUB bestBox =
      some (queue', bestLB', bestUB', bestBox')) :
    bestLB' ≤ bestLB := by
  cases queue with
  | nil => simp [minimizeStepAffine, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStepAffine, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, hLB, _, _⟩
    all_goals rw [← hLB]
    all_goals exact min_le_left _ _

/-- Helper: minimizeLoopAffine preserves the initial lower bound. -/
theorem minimizeLoopAffine_bestLB_le (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    (minimizeLoopAffine e cfg queue bestLB bestUB bestBox iters).bound.lo ≤ bestLB := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoopAffine, le_refl]
  | succ n ih =>
    simp only [minimizeLoopAffine]
    cases hstep : minimizeStepAffine e cfg queue bestLB bestUB bestBox with
    | none =>
      exact le_rfl
    | some queue' =>
      rcases queue' with ⟨queue', bestLB', bestUB', bestBox'⟩
      have hstepLB :=
        minimizeStepAffine_bestLB_le e cfg queue bestLB bestUB bestBox
          queue' bestLB' bestUB' bestBox' hstep
      have hrec := ih queue' bestLB' bestUB' bestBox'
      exact le_trans hrec hstepLB

/-- Global minimization using Affine arithmetic -/
def globalMinimizeAffine (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine := {}) : GlobalResult :=
  let I := evalOnBoxAffine e B cfg
  minimizeLoopAffine e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations

/-- Global maximization using Affine arithmetic -/
def globalMaximizeAffine (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine := {}) : GlobalResult :=
  let result := globalMinimizeAffine (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Correctness theorems for Dyadic optimization -/

/-- The lower bound from Dyadic interval evaluation is correct.

The proof uses `evalIntervalDyadic_correct` and `IntervalDyadic.toIntervalRat_correct`
to show that the true value is contained in the resulting rational interval.

Note: Requires domain validity for expressions with log. -/
theorem evalOnBoxDyadic_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigDyadic) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth }) :
    (evalOnBoxDyadic e B cfg).lo ≤ Expr.eval ρ e := by
  -- Build the Dyadic environment from the box
  set dyadicEnv : IntervalDyadicEnv := fun i =>
    Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision
  set dyadicCfg : DyadicConfig := {
    precision := cfg.precision,
    taylorDepth := cfg.taylorDepth,
  }
  have henv : envMemDyadic ρ dyadicEnv := by
    intro i
    by_cases hi : i < B.length
    · have hmem : ρ i ∈ B[i]'hi := hρ ⟨i, hi⟩
      have hdyad := Core.IntervalDyadic.mem_ofIntervalRat hmem cfg.precision hprec
      simpa [dyadicEnv, List.getD, List.getElem?_eq_getElem hi, Option.getD] using hdyad
    · have hzeroi : ρ i = 0 := hzero i (Nat.le_of_not_lt hi)
      have hmem0 : (0 : ℝ) ∈ IntervalRat.singleton 0 := by
        exact_mod_cast IntervalRat.mem_singleton 0
      have hdyad := Core.IntervalDyadic.mem_ofIntervalRat hmem0 cfg.precision hprec
      simpa [dyadicEnv, List.getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD, hzeroi] using hdyad
  have hmem := evalIntervalDyadic_correct e hsupp ρ dyadicEnv henv dyadicCfg hprec hdom
  have hmem_rat := Core.IntervalDyadic.mem_toIntervalRat.mp hmem
  have hmem_rat' : Expr.eval ρ e ∈ evalOnBoxDyadic e B cfg := by
    simpa [evalOnBoxDyadic, dyadicEnv, dyadicCfg] using hmem_rat
  exact ((IntervalRat.mem_def _ _).mp hmem_rat').1

/-- The key correctness theorem for Dyadic minimization: globalMinimizeDyadic returns
    a lower bound that is ≤ the minimum of f over any point in the original box.

Note: Requires domain validity for expressions with log. -/
theorem globalMinimizeDyadic_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigDyadic)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeDyadic e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeDyadic]
  set I := evalOnBoxDyadic e B cfg
  have hlo : I.lo ≤ Expr.eval ρ e := evalOnBoxDyadic_lo_correct e hsupp B cfg ρ hρ hzero hprec hdom
  have hloop :
      (minimizeLoopDyadic e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo ≤ I.lo := by
    simpa using
      (minimizeLoopDyadic_bestLB_le e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations)
  have hloop' : ((minimizeLoopDyadic e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo : ℝ)
      ≤ (I.lo : ℝ) := by
    exact_mod_cast hloop
  linarith

/-- The upper bound from globalMaximizeDyadic is correct: f(ρ) ≤ hi for all ρ in B.

Note: Requires domain validity for expressions with log. -/
theorem globalMaximizeDyadic_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigDyadic)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeDyadic e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeDyadic]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  -- Domain validity for neg e is the same as for e
  have hdom_neg : evalDomainValidDyadic (Expr.neg e)
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth } := by
    simp only [evalDomainValidDyadic]; exact hdom
  have hmin := globalMinimizeDyadic_lo_correct (Expr.neg e) hneg_supp B cfg hprec hdom_neg ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  -- hmin : (globalMinimizeDyadic e.neg B cfg).bound.lo ≤ -Expr.eval ρ e
  -- Goal : Expr.eval ρ e ≤ -(globalMinimizeDyadic e.neg B cfg).bound.lo
  have h : Expr.eval ρ e ≤ (-(globalMinimizeDyadic (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

/-! ### Correctness theorems for Affine optimization -/

/-- The lower bound from Affine interval evaluation is correct.
    Note: Requires ExprSupportedCore, valid noise assignment, and domain validity for log. -/
theorem evalOnBoxAffine_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigAffine) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hdom : evalDomainValidAffine e (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }) :
    (evalOnBoxAffine e B cfg).lo ≤ Expr.eval ρ e := by
  set affineCfg : AffineConfig := { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }
  obtain ⟨eps, hvalid, henv⟩ := exists_noise_toAffineEnv B ρ
    (fun i hi => hρ ⟨i, hi⟩) hzero
  -- Use evalIntervalAffine_correct to get mem_affine, then mem_toInterval_weak
  have hmem_affine := evalIntervalAffine_correct e hsupp ρ (toAffineEnv B) eps
    hvalid henv affineCfg hdom
  have hmem := AffineForm.mem_toInterval_weak hvalid hmem_affine
  have hmem' : Expr.eval ρ e ∈ evalOnBoxAffine e B cfg := by
    simpa [evalOnBoxAffine, affineCfg] using hmem
  exact ((IntervalRat.mem_def _ _).mp hmem').1

/-- The key correctness theorem for Affine minimization.

Note: Requires domain validity for expressions with log. -/
theorem globalMinimizeAffine_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigAffine)
    (hdom : evalDomainValidAffine e (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeAffine e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeAffine]
  set I := evalOnBoxAffine e B cfg
  have hlo : I.lo ≤ Expr.eval ρ e := evalOnBoxAffine_lo_correct e hsupp B cfg ρ hρ hzero hdom
  have hloop :
      (minimizeLoopAffine e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo ≤ I.lo := by
    simpa using
      (minimizeLoopAffine_bestLB_le e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations)
  have hloop' : ((minimizeLoopAffine e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo : ℝ)
      ≤ (I.lo : ℝ) := by
    exact_mod_cast hloop
  linarith

/-- The upper bound from globalMaximizeAffine is correct.

Note: Requires domain validity for expressions with log. -/
theorem globalMaximizeAffine_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigAffine)
    (hdom : evalDomainValidAffine e (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeAffine e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeAffine]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  -- Domain validity for neg e is the same as for e
  have hdom_neg : evalDomainValidAffine (Expr.neg e) (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols } := by
    simp only [evalDomainValidAffine]; exact hdom
  have hmin := globalMinimizeAffine_lo_correct (Expr.neg e) hneg_supp B cfg hdom_neg ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  -- hmin : (globalMinimizeAffine e.neg B cfg).bound.lo ≤ -Expr.eval ρ e
  -- Goal : Expr.eval ρ e ≤ -(globalMinimizeAffine e.neg B cfg).bound.lo
  have h : Expr.eval ρ e ≤ (-(globalMinimizeAffine (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

/-! ### Checked branch-and-bound

These entry points never consume a finite fallback from a legacy evaluator.
Domain failures are propagated to the caller. Optional monotonicity pruning is
implemented through a checked computable-AD pre-pass; unsupported derivative
expressions use the identity pruner. -/

theorem Box.envMem_splitWidest_cases (B : Box) (rho : Nat → ℝ)
    (hrho : Box.envMem rho B) :
    Box.envMem rho (Box.splitWidest B).1 ∨
      Box.envMem rho (Box.splitWidest B).2 := by
  unfold Box.splitWidest
  by_cases hdim : Box.widestDim B < B.length
  · exact Box.envMem_split_cases B (Box.widestDim B) hdim rho hrho
  · simp [Box.split, hdim, hrho]

theorem Box.splitWidest_fst_length (B : Box) :
    (Box.splitWidest B).1.length = B.length := by
  unfold Box.splitWidest Box.split
  split <;> simp

theorem Box.splitWidest_snd_length (B : Box) :
    (Box.splitWidest B).2.length = B.length := by
  unfold Box.splitWidest Box.split
  split <;> simp

/-- Minimum lower endpoint stored in a collection of bounded boxes. The
fallback is used only for an empty internal state. -/
def minimumStoredBound (fallback : ℚ) : List (ℚ × Box) → ℚ
  | [] => fallback
  | [entry] => entry.1
  | entry :: next :: rest =>
      min entry.1 (minimumStoredBound fallback (next :: rest))

theorem minimumStoredBound_le_of_mem (fallback : ℚ) (boxes : List (ℚ × Box))
    (entry : ℚ × Box) (hentry : entry ∈ boxes) :
    minimumStoredBound fallback boxes ≤ entry.1 := by
  induction boxes with
  | nil => simp at hentry
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at hentry
          subst entry
          exact le_rfl
      | cons next rest =>
          simp only [List.mem_cons] at hentry
          rcases hentry with rfl | htail
          · exact min_le_left _ _
          · exact le_trans (min_le_right _ _) (ih (by simpa using htail))

/-- One backend-independent checked branch-and-bound step.

`finished` stores terminal boxes. Keeping their local lower bounds
separate from the active queue lets the global lower bound rise as the active
partition is refined; the former implementation retained the root lower bound
forever. -/
def minimizeStepCheckedWith (evalBox : Box → EvalResult IntervalRat)
    (pruneBox : Box → Box) (tolerance : ℚ)
    (queue finished : List (ℚ × Box)) (bestUB : ℚ) (bestBox : Box) :
    EvalResult (Option (List (ℚ × Box) × List (ℚ × Box) × ℚ × Box)) :=
  match popBest queue with
  | none => .ok none
  | some ((_, sourceB), rest) => do
    let B := pruneBox sourceB
    let I ← evalBox B
    let newBestUB := min bestUB I.hi
    if B.isEmpty || Box.maxWidth B ≤ tolerance then
      return some (rest, (I.lo, B) :: finished, newBestUB, bestBox)
    let (B₁, B₂) := Box.splitWidest B
    let I₁ ← evalBox B₁
    let I₂ ← evalBox B₂
    let queue' := insertByBound rest I₁.lo B₁
    let queue' := insertByBound queue' I₂.lo B₂
    return some (queue', finished, newBestUB, bestBox)

/-- Every point of the original box is represented by a current partition
cell whose stored lower endpoint is valid for that point. -/
def CheckedLowerInvariant (value : (Nat → ℝ) → ℝ) (original : Box)
    (queue finished : List (ℚ × Box)) : Prop :=
  ∀ rho, Box.envMem rho original → (∀ i, i ≥ original.length → rho i = 0) →
    ∃ rho' entry, entry ∈ finished ++ queue ∧
      Box.envMem rho' entry.2 ∧
      (∀ i, i ≥ original.length → rho' i = 0) ∧
      entry.2.length = original.length ∧
      (entry.1 : ℝ) ≤ value rho' ∧ value rho' ≤ value rho

theorem minimizeStepCheckedWith_preserves_lower
    (evalBox : Box → EvalResult IntervalRat) (pruneBox : Box → Box)
    (tolerance : ℚ)
    (value : (Nat → ℝ) → ℝ) (original : Box)
    (queue finished : List (ℚ × Box)) (bestUB : ℚ) (bestBox : Box)
    (queue' finished' : List (ℚ × Box)) (bestUB' : ℚ) (bestBox' : Box)
    (hevalSound : ∀ B I, evalBox B = .ok I →
      B.length = original.length → ∀ rho, Box.envMem rho B →
        (∀ i, i ≥ original.length → rho i = 0) → (I.lo : ℝ) ≤ value rho)
    (hpruneSound : ∀ B, B.length = original.length →
      ∀ rho, Box.envMem rho B →
        (∀ i, i ≥ original.length → rho i = 0) →
        ∃ rho', Box.envMem rho' (pruneBox B) ∧
          (∀ i, i ≥ original.length → rho' i = 0) ∧
          (pruneBox B).length = original.length ∧ value rho' ≤ value rho)
    (hinv : CheckedLowerInvariant value original queue finished)
    (hstep : minimizeStepCheckedWith evalBox pruneBox tolerance queue finished bestUB bestBox =
      .ok (some (queue', finished', bestUB', bestBox'))) :
    CheckedLowerInvariant value original queue' finished' := by
  cases queue with
  | nil => simp [minimizeStepCheckedWith, popBest] at hstep
  | cons head rest =>
    rcases head with ⟨lb, sourceB⟩
    simp only [minimizeStepCheckedWith, popBest] at hstep
    set B := pruneBox sourceB with hB
    cases hevalB : evalBox B with
    | error err => simp [hevalB, Except.bind, bind] at hstep
    | ok I =>
      simp [hevalB, Except.bind, bind] at hstep
      split at hstep
      · cases hstep
        intro rho hrho hzero
        obtain ⟨rho', entry, hentry, hmem, hzero', hlen, hbound, hvalue⟩ :=
          hinv rho hrho hzero
        have hold : entry ∈ finished ∨ entry = (lb, sourceB) ∨ entry ∈ queue' := by
          simpa [List.mem_append, or_assoc] using hentry
        rcases hold with hfinished | hcurrent | hrest
        · exact ⟨rho', entry, by simp [hfinished], hmem, hzero', hlen, hbound, hvalue⟩
        · subst entry
          obtain ⟨rho'', hmem'', hzero'', hlen'', hle⟩ :=
            hpruneSound sourceB hlen rho' hmem hzero'
          refine ⟨rho'', (I.lo, B), by simp, ?_, hzero'', ?_, ?_, le_trans hle hvalue⟩
          · simpa [hB] using hmem''
          · simpa [hB] using hlen''
          · exact hevalSound B I hevalB (by simpa [hB] using hlen'') rho''
              (by simpa [hB] using hmem'') hzero''
        · exact ⟨rho', entry, by simp [hrest], hmem, hzero', hlen, hbound, hvalue⟩
      · cases hevalOne : evalBox (Box.splitWidest B).1 with
        | error err => simp [hevalOne] at hstep
        | ok Ione =>
          simp [hevalOne] at hstep
          cases hevalTwo : evalBox (Box.splitWidest B).2 with
          | error err => simp [hevalTwo] at hstep
          | ok Itwo =>
            simp [hevalTwo] at hstep
            cases hstep
            intro rho hrho hzero
            obtain ⟨rho', entry, hentry, hmem, hzero', hlen, hbound, hvalue⟩ :=
              hinv rho hrho hzero
            by_cases hcurrent : entry = (lb, sourceB)
            · subst entry
              obtain ⟨rho'', hmem'', hzero'', hlen'', hle⟩ :=
                hpruneSound sourceB hlen rho' hmem hzero'
              have hmemB : Box.envMem rho'' B := by simpa [hB] using hmem''
              have hlenB : B.length = original.length := by simpa [hB] using hlen''
              rcases Box.envMem_splitWidest_cases B rho'' hmemB with hleft | hright
              · refine ⟨rho'', (Ione.lo, (Box.splitWidest B).1), ?_, hleft, hzero'', ?_,
                  hevalSound _ Ione hevalOne ?_ rho'' hleft hzero'', le_trans hle hvalue⟩
                simp [mem_insertByBound_iff]
                · exact Box.splitWidest_fst_length B |>.trans hlenB
                · exact Box.splitWidest_fst_length B |>.trans hlenB
              · refine ⟨rho'', (Itwo.lo, (Box.splitWidest B).2), ?_, hright, hzero'', ?_,
                  hevalSound _ Itwo hevalTwo ?_ rho'' hright hzero'', le_trans hle hvalue⟩
                simp [mem_insertByBound_iff]
                · exact Box.splitWidest_snd_length B |>.trans hlenB
                · exact Box.splitWidest_snd_length B |>.trans hlenB
            · refine ⟨rho', entry, ?_, hmem, hzero', hlen, hbound, hvalue⟩
              have hold : entry ∈ finished ∨ entry ∈ rest := by
                simpa [List.mem_append, hcurrent, or_assoc] using hentry
              rcases hold with hfinished | hrest
              · simp [hfinished]
              · simp [mem_insertByBound_iff, hrest]

/-- Checked branch-and-bound loop. -/
def minimizeLoopCheckedWith (evalBox : Box → EvalResult IntervalRat)
    (pruneBox : Box → Box)
    (maxIterations : Nat) (tolerance fallbackLB : ℚ)
    (queue finished : List (ℚ × Box)) (bestUB : ℚ) (bestBox : Box) :
    Nat → EvalResult GlobalResult
  | 0 => .ok {
      bound := {
        lo := minimumStoredBound fallbackLB (finished ++ queue)
        hi := bestUB, bestBox := bestBox, iterations := maxIterations }
      remainingBoxes := queue }
  | n + 1 => do
      let step ← minimizeStepCheckedWith evalBox pruneBox tolerance queue finished bestUB bestBox
      match step with
      | none => return {
          bound := {
            lo := minimumStoredBound fallbackLB finished
            hi := bestUB, bestBox := bestBox,
                     iterations := maxIterations - n - 1 }
          remainingBoxes := [] }
      | some (queue', finished', bestUB', bestBox') =>
          minimizeLoopCheckedWith evalBox pruneBox maxIterations tolerance fallbackLB
            queue' finished' bestUB' bestBox' n

theorem minimizeStepCheckedWith_eq_ok_none_iff
    (evalBox : Box → EvalResult IntervalRat) (pruneBox : Box → Box) (tolerance : ℚ)
    (queue finished : List (ℚ × Box)) (bestUB : ℚ) (bestBox : Box) :
    minimizeStepCheckedWith evalBox pruneBox tolerance queue finished bestUB bestBox = .ok none ↔
      queue = [] := by
  constructor
  · intro hstep
    cases queue with
    | nil => rfl
    | cons head rest =>
        rcases head with ⟨lb, sourceB⟩
        simp only [minimizeStepCheckedWith, popBest] at hstep
        set B := pruneBox sourceB with hB
        cases hevalB : evalBox B with
        | error err => simp [hevalB, Except.bind, bind] at hstep
        | ok I =>
            simp [hevalB, Except.bind, bind] at hstep
            split at hstep
            · injection hstep with hnone
              simp at hnone
            · cases hevalOne : evalBox (Box.splitWidest B).1 with
              | error err => simp [hevalOne] at hstep
              | ok Ione =>
                  simp [hevalOne] at hstep
                  cases hevalTwo : evalBox (Box.splitWidest B).2 with
                  | error err => simp [hevalTwo] at hstep
                  | ok Itwo =>
                      simp [hevalTwo] at hstep
                      injection hstep with hnone
                      simp at hnone
  · intro hqueue
    subst queue
    rfl

theorem CheckedLowerInvariant.minimumStoredBound_correct
    (value : (Nat → ℝ) → ℝ) (original : Box)
    (queue finished : List (ℚ × Box)) (fallback : ℚ)
    (hinv : CheckedLowerInvariant value original queue finished)
    (rho : Nat → ℝ) (hrho : Box.envMem rho original)
    (hzero : ∀ i, i ≥ original.length → rho i = 0) :
    (minimumStoredBound fallback (finished ++ queue) : ℝ) ≤ value rho := by
  obtain ⟨rho', entry, hentry, _, _, _, hbound, hvalue⟩ := hinv rho hrho hzero
  have hmin := minimumStoredBound_le_of_mem fallback (finished ++ queue) entry hentry
  exact le_trans (le_trans (by exact_mod_cast hmin) hbound) hvalue

theorem minimizeLoopCheckedWith_lower_correct
    (evalBox : Box → EvalResult IntervalRat) (pruneBox : Box → Box)
    (maxIterations : Nat) (tolerance fallbackLB : ℚ)
    (value : (Nat → ℝ) → ℝ) (original : Box)
    (hevalSound : ∀ B I, evalBox B = .ok I →
      B.length = original.length → ∀ rho, Box.envMem rho B →
        (∀ i, i ≥ original.length → rho i = 0) → (I.lo : ℝ) ≤ value rho) :
    (∀ B, B.length = original.length → ∀ rho, Box.envMem rho B →
      (∀ i, i ≥ original.length → rho i = 0) →
      ∃ rho', Box.envMem rho' (pruneBox B) ∧
        (∀ i, i ≥ original.length → rho' i = 0) ∧
        (pruneBox B).length = original.length ∧ value rho' ≤ value rho) →
    ∀ (iters : Nat) (queue finished : List (ℚ × Box)) (bestUB : ℚ)
      (bestBox : Box) (result : GlobalResult),
      CheckedLowerInvariant value original queue finished →
      minimizeLoopCheckedWith evalBox pruneBox maxIterations tolerance fallbackLB
          queue finished bestUB bestBox iters = .ok result →
      ∀ rho, Box.envMem rho original →
        (∀ i, i ≥ original.length → rho i = 0) →
        (result.bound.lo : ℝ) ≤ value rho := by
  intro hpruneSound iters
  induction iters with
  | zero =>
      intro queue finished bestUB bestBox result hinv hsuccess rho hrho hzero
      simp [minimizeLoopCheckedWith] at hsuccess
      subst result
      exact CheckedLowerInvariant.minimumStoredBound_correct
        value original queue finished fallbackLB hinv rho hrho hzero
  | succ n ih =>
      intro queue finished bestUB bestBox result hinv hsuccess rho hrho hzero
      simp only [minimizeLoopCheckedWith] at hsuccess
      cases hstep : minimizeStepCheckedWith evalBox pruneBox tolerance queue finished bestUB bestBox with
      | error err => simp [hstep, Except.bind, bind] at hsuccess
      | ok step =>
          simp [hstep, Except.bind, bind] at hsuccess
          cases step with
          | none =>
              have hqueue : queue = [] :=
                (minimizeStepCheckedWith_eq_ok_none_iff
                  evalBox pruneBox tolerance queue finished bestUB bestBox).mp hstep
              subst queue
              injection hsuccess with hresult
              subst result
              simpa using (CheckedLowerInvariant.minimumStoredBound_correct
                value original [] finished fallbackLB hinv rho hrho hzero)
          | some state =>
              rcases state with ⟨queue', finished', bestUB', bestBox'⟩
              have hinv' := minimizeStepCheckedWith_preserves_lower evalBox pruneBox tolerance
                value original queue finished bestUB bestBox queue' finished' bestUB' bestBox'
                hevalSound hpruneSound hinv hstep
              exact ih queue' finished' bestUB' bestBox' result hinv' hsuccess rho hrho hzero

/-- Checked minimization parameterized by a sound finite-enclosure backend. -/
def checkedMonotonicityPruner (e : Expr) (enabled : Bool) (cfg : EvalConfig) :
    Box → Box := fun B =>
  if enabled && e.checkADSupported then
    (pruneBoxForMin B (gradientIntervalCore e B cfg)).1
  else B

theorem checkedMonotonicityPruner_correct (e : Expr) (enabled : Bool)
    (cfg : EvalConfig) (B : Box) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      ∃ rho', Box.envMem rho' (checkedMonotonicityPruner e enabled cfg B) ∧
        (∀ i, i ≥ B.length → rho' i = 0) ∧
        (checkedMonotonicityPruner e enabled cfg B).length = B.length ∧
        Expr.eval rho' e ≤ Expr.eval rho e := by
  intro rho hrho hzero
  by_cases henabled : enabled = true
  · by_cases hsupport : e.checkADSupported = true
    · have hsupp : ADSupported e :=
        (Expr.checkADSupported_eq_true_iff e).mp hsupport
      obtain ⟨rho', hmem, hzero', hvalue⟩ :=
        pruneBoxForMin_correct e hsupp B (cfg := cfg) rho hrho hzero
      have hlen := pruneBoxForMin_length B (gradientIntervalCore e B cfg)
      refine ⟨rho', ?_, ?_, ?_, hvalue⟩
      · simpa [checkedMonotonicityPruner, henabled, hsupport] using hmem
      · intro i hi
        exact hzero' i (by simpa [hlen] using hi)
      · simpa [checkedMonotonicityPruner, henabled, hsupport] using hlen
    · exact ⟨rho, by simpa [checkedMonotonicityPruner, henabled, hsupport] using hrho,
        hzero, by simp [checkedMonotonicityPruner, henabled, hsupport], le_rfl⟩
  · exact ⟨rho, by simpa [checkedMonotonicityPruner, henabled] using hrho,
      hzero, by simp [checkedMonotonicityPruner, henabled], le_rfl⟩

theorem checkedMonotonicityPruner_correct_of_length (e : Expr) (enabled : Bool)
    (cfg : EvalConfig) (original B : Box) (hlen : B.length = original.length)
    (rho : Nat → ℝ) (hrho : Box.envMem rho B)
    (hzero : ∀ i, i ≥ original.length → rho i = 0) :
    ∃ rho', Box.envMem rho' (checkedMonotonicityPruner e enabled cfg B) ∧
      (∀ i, i ≥ original.length → rho' i = 0) ∧
      (checkedMonotonicityPruner e enabled cfg B).length = original.length ∧
      Expr.eval rho' e ≤ Expr.eval rho e := by
  obtain ⟨rho', hmem, hzero', hlen', hvalue⟩ :=
    checkedMonotonicityPruner_correct e enabled cfg B rho hrho
      (fun i hi => hzero i (by simpa [hlen] using hi))
  exact ⟨rho', hmem, fun i hi => hzero' i (by simpa [hlen] using hi),
    hlen'.trans hlen, hvalue⟩

def globalMinimizeCheckedWith (evalBox : Box → EvalResult IntervalRat)
    (pruneBox : Box → Box) (B : Box) (maxIterations : Nat) (tolerance : ℚ) :
    EvalResult GlobalResult := do
  let I ← evalBox B
  minimizeLoopCheckedWith evalBox pruneBox maxIterations tolerance I.lo
    [(I.lo, B)] [] I.hi B maxIterations

theorem globalMinimizeCheckedWith_lower_correct
    (evalBox : Box → EvalResult IntervalRat) (pruneBox : Box → Box) (B : Box)
    (maxIterations : Nat) (tolerance : ℚ)
    (value : (Nat → ℝ) → ℝ)
    (hevalSound : ∀ box I, evalBox box = .ok I →
      box.length = B.length → ∀ rho, Box.envMem rho box →
        (∀ i, i ≥ B.length → rho i = 0) → (I.lo : ℝ) ≤ value rho)
    (hpruneSound : ∀ box, box.length = B.length →
      ∀ rho, Box.envMem rho box → (∀ i, i ≥ B.length → rho i = 0) →
        ∃ rho', Box.envMem rho' (pruneBox box) ∧
          (∀ i, i ≥ B.length → rho' i = 0) ∧
          (pruneBox box).length = B.length ∧ value rho' ≤ value rho)
    (result : GlobalResult)
    (hsuccess : globalMinimizeCheckedWith evalBox pruneBox B maxIterations tolerance = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      (result.bound.lo : ℝ) ≤ value rho := by
  cases heval : evalBox B with
  | error err =>
      simp [globalMinimizeCheckedWith, heval, Except.bind, bind] at hsuccess
  | ok I =>
      simp [globalMinimizeCheckedWith, heval, Except.bind, bind] at hsuccess
      have hinv : CheckedLowerInvariant value B [(I.lo, B)] [] := by
        intro rho hrho hzero
        exact ⟨rho, (I.lo, B), by simp, hrho, hzero, rfl,
          hevalSound B I heval rfl rho hrho hzero, le_rfl⟩
      exact minimizeLoopCheckedWith_lower_correct evalBox pruneBox maxIterations tolerance I.lo
        value B hevalSound hpruneSound maxIterations [(I.lo, B)] [] I.hi B result hinv hsuccess

/-- Checked maximization parameterized by a sound finite-enclosure backend. -/
def globalMaximizeCheckedWith (evalBox : Expr → Box → EvalResult IntervalRat)
    (pruneBox : Expr → Box → Box) (e : Expr) (B : Box) (maxIterations : Nat)
    (tolerance : ℚ) : EvalResult GlobalResult := do
  let result ← globalMinimizeCheckedWith (evalBox (Expr.neg e)) (pruneBox (Expr.neg e))
    B maxIterations tolerance
  return {
    bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

theorem globalMaximizeCheckedWith_upper_correct
    (evalBox : Expr → Box → EvalResult IntervalRat)
    (pruneBox : Expr → Box → Box)
    (e : Expr) (B : Box) (maxIterations : Nat) (tolerance : ℚ)
    (hevalSound : ∀ box I, evalBox (Expr.neg e) box = .ok I →
      box.length = B.length → ∀ rho, Box.envMem rho box →
        (∀ i, i ≥ B.length → rho i = 0) →
        (I.lo : ℝ) ≤ Expr.eval rho (Expr.neg e))
    (hpruneSound : ∀ box, box.length = B.length →
      ∀ rho, Box.envMem rho box → (∀ i, i ≥ B.length → rho i = 0) →
        ∃ rho', Box.envMem rho' (pruneBox (Expr.neg e) box) ∧
          (∀ i, i ≥ B.length → rho' i = 0) ∧
          (pruneBox (Expr.neg e) box).length = B.length ∧
          Expr.eval rho' (Expr.neg e) ≤ Expr.eval rho (Expr.neg e))
    (result : GlobalResult)
    (hsuccess : globalMaximizeCheckedWith evalBox pruneBox e B maxIterations tolerance = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      Expr.eval rho e ≤ (result.bound.hi : ℝ) := by
  cases hmin : globalMinimizeCheckedWith (evalBox (Expr.neg e)) (pruneBox (Expr.neg e))
      B maxIterations tolerance with
  | error err =>
      simp [globalMaximizeCheckedWith, hmin, Except.bind, bind] at hsuccess
  | ok minResult =>
      have hresult : result = {
          bound := { lo := -minResult.bound.hi
                     hi := -minResult.bound.lo
                     bestBox := minResult.bound.bestBox
                     iterations := minResult.bound.iterations }
          remainingBoxes := minResult.remainingBoxes.map fun (lb, box) => (-lb, box) } := by
        simp [globalMaximizeCheckedWith, hmin, Except.bind, bind] at hsuccess
        injection hsuccess with h
        exact h.symm
      subst result
      intro rho hrho hzero
      have hlower := globalMinimizeCheckedWith_lower_correct
        (evalBox (Expr.neg e)) (pruneBox (Expr.neg e)) B maxIterations tolerance
        (fun rho => Expr.eval rho (Expr.neg e)) hevalSound hpruneSound minResult hmin rho hrho hzero
      simp only [Expr.eval_neg] at hlower
      rw [Rat.cast_neg]
      linarith

/-- Checked rational evaluation on a box. -/
def evalOnBoxRationalChecked (e : Expr) (B : Box) : EvalResult IntervalRat :=
  evalIntervalChecked e (Box.toEnv B)

def globalMinimizeRationalChecked (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) :
    EvalResult GlobalResult :=
  globalMinimizeCheckedWith (evalOnBoxRationalChecked e)
    (checkedMonotonicityPruner e cfg.useMonotonicity { taylorDepth := cfg.taylorDepth })
    B cfg.maxIterations cfg.tolerance

def globalMaximizeRationalChecked (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) :
    EvalResult GlobalResult :=
  globalMaximizeCheckedWith evalOnBoxRationalChecked
    (fun expr => checkedMonotonicityPruner expr cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth }) e B cfg.maxIterations cfg.tolerance

theorem evalOnBoxRationalChecked_lo_correct (e : Expr) (B : Box)
    (I : IntervalRat) (hsuccess : evalOnBoxRationalChecked e B = .ok I)
    (rho : Nat → ℝ) (hrho : Box.envMem rho B)
    (hzero : ∀ i, i ≥ B.length → rho i = 0) :
    (I.lo : ℝ) ≤ Expr.eval rho e := by
  have henv := Box.envMem_toEnv rho B hrho hzero
  have hmem := evalIntervalChecked_correct e (Box.toEnv B) I hsuccess rho henv
  exact ((IntervalRat.mem_def _ _).mp hmem).1

theorem globalMinimizeRationalChecked_lo_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfig) (result : GlobalResult)
    (hsuccess : globalMinimizeRationalChecked e B cfg = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      (result.bound.lo : ℝ) ≤ Expr.eval rho e := by
  intro rho hrho hzero
  apply globalMinimizeCheckedWith_lower_correct
    (evalOnBoxRationalChecked e)
    (checkedMonotonicityPruner e cfg.useMonotonicity { taylorDepth := cfg.taylorDepth })
    B cfg.maxIterations cfg.tolerance (fun rho => Expr.eval rho e)
  intro box I heval hlen rho' hrho' hzero'
  exact evalOnBoxRationalChecked_lo_correct e box I heval rho' hrho'
    (fun i hi => hzero' i (by simpa [hlen] using hi))
  · intro box hlen rho' hrho' hzero'
    exact checkedMonotonicityPruner_correct_of_length e cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth } B box hlen rho' hrho' hzero'
  · exact hsuccess
  · exact hrho
  · exact hzero

theorem globalMaximizeRationalChecked_hi_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfig) (result : GlobalResult)
    (hsuccess : globalMaximizeRationalChecked e B cfg = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      Expr.eval rho e ≤ (result.bound.hi : ℝ) := by
  apply globalMaximizeCheckedWith_upper_correct evalOnBoxRationalChecked
    (fun expr => checkedMonotonicityPruner expr cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth }) e B
    cfg.maxIterations cfg.tolerance
  intro box I heval hlen rho hrho hzero
  exact evalOnBoxRationalChecked_lo_correct (Expr.neg e) box I heval rho hrho
    (fun i hi => hzero i (by simpa [hlen] using hi))
  · intro box hlen rho hrho hzero
    exact checkedMonotonicityPruner_correct_of_length (Expr.neg e) cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth } B box hlen rho hrho hzero
  exact hsuccess

/-- Checked Dyadic evaluation on a box. -/
def evalOnBoxDyadicChecked (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic) :
    EvalResult IntervalRat :=
  let ρ : IntervalDyadicEnv := fun i =>
    let I := B.getD i (IntervalRat.singleton 0)
    Core.IntervalDyadic.ofIntervalRat I cfg.precision
  let dcfg : DyadicConfig := {
    precision := cfg.precision, taylorDepth := cfg.taylorDepth }
  match evalIntervalDyadicChecked e ρ dcfg with
  | .ok I => .ok I.toIntervalRat
  | .error err => .error err

def globalMinimizeDyadicChecked (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic := {}) :
    EvalResult GlobalResult :=
  globalMinimizeCheckedWith (fun box => evalOnBoxDyadicChecked e box cfg)
    (checkedMonotonicityPruner e cfg.useMonotonicity { taylorDepth := cfg.taylorDepth })
    B cfg.maxIterations cfg.tolerance

def globalMaximizeDyadicChecked (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic := {}) :
    EvalResult GlobalResult :=
  globalMaximizeCheckedWith (fun e box => evalOnBoxDyadicChecked e box cfg)
    (fun expr => checkedMonotonicityPruner expr cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth }) e B cfg.maxIterations cfg.tolerance

theorem evalOnBoxDyadicChecked_lo_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfigDyadic) (hprec : cfg.precision ≤ 0)
    (I : IntervalRat) (hsuccess : evalOnBoxDyadicChecked e B cfg = .ok I)
    (rho : Nat → ℝ) (hrho : Box.envMem rho B)
    (hzero : ∀ i, i ≥ B.length → rho i = 0) :
    (I.lo : ℝ) ≤ Expr.eval rho e := by
  let rhoD : IntervalDyadicEnv := fun i =>
    Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision
  let dcfg : DyadicConfig := {
    precision := cfg.precision, taylorDepth := cfg.taylorDepth }
  have henv : envMemDyadic rho rhoD := by
    intro i
    by_cases hi : i < B.length
    · have hmem : rho i ∈ B[i]'hi := hrho ⟨i, hi⟩
      simpa [rhoD, List.getD, List.getElem?_eq_getElem hi, Option.getD] using
        (Core.IntervalDyadic.mem_ofIntervalRat hmem cfg.precision hprec)
    · have hmem0 : (0 : ℝ) ∈ IntervalRat.singleton 0 := by
        exact_mod_cast IntervalRat.mem_singleton 0
      simpa [rhoD, List.getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD,
        hzero i (Nat.le_of_not_lt hi)] using
        (Core.IntervalDyadic.mem_ofIntervalRat hmem0 cfg.precision hprec)
  cases heval : evalIntervalDyadicChecked e rhoD dcfg with
  | error err =>
      change (match evalIntervalDyadicChecked e rhoD dcfg with
        | Except.ok J => Except.ok J.toIntervalRat
        | Except.error err => Except.error err) = (Except.ok I : EvalResult IntervalRat) at hsuccess
      rw [heval] at hsuccess
      contradiction
  | ok resultD =>
      have hresult : I = resultD.toIntervalRat := by
        change (match evalIntervalDyadicChecked e rhoD dcfg with
          | Except.ok J => Except.ok J.toIntervalRat
          | Except.error err => Except.error err) = (Except.ok I : EvalResult IntervalRat) at hsuccess
        rw [heval] at hsuccess
        injection hsuccess with h
        exact h.symm
      subst I
      have hmem := evalIntervalDyadicChecked_correct e rho rhoD henv dcfg hprec resultD heval
      exact ((IntervalRat.mem_def _ _).mp
        (Core.IntervalDyadic.mem_toIntervalRat.mp hmem)).1

theorem globalMinimizeDyadicChecked_lo_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfigDyadic) (hprec : cfg.precision ≤ 0)
    (result : GlobalResult)
    (hsuccess : globalMinimizeDyadicChecked e B cfg = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      (result.bound.lo : ℝ) ≤ Expr.eval rho e := by
  apply globalMinimizeCheckedWith_lower_correct
    (fun box => evalOnBoxDyadicChecked e box cfg)
    (checkedMonotonicityPruner e cfg.useMonotonicity { taylorDepth := cfg.taylorDepth })
    B cfg.maxIterations cfg.tolerance (fun rho => Expr.eval rho e)
  intro box I heval hlen rho hrho hzero
  exact evalOnBoxDyadicChecked_lo_correct e box cfg hprec I heval rho hrho
    (fun i hi => hzero i (by simpa [hlen] using hi))
  · intro box hlen rho hrho hzero
    exact checkedMonotonicityPruner_correct_of_length e cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth } B box hlen rho hrho hzero
  · exact hsuccess

theorem globalMaximizeDyadicChecked_hi_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfigDyadic) (hprec : cfg.precision ≤ 0)
    (result : GlobalResult)
    (hsuccess : globalMaximizeDyadicChecked e B cfg = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      Expr.eval rho e ≤ (result.bound.hi : ℝ) := by
  apply globalMaximizeCheckedWith_upper_correct
    (fun expr box => evalOnBoxDyadicChecked expr box cfg)
    (fun expr => checkedMonotonicityPruner expr cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth }) e B
      cfg.maxIterations cfg.tolerance
  intro box I heval hlen rho hrho hzero
  exact evalOnBoxDyadicChecked_lo_correct (Expr.neg e) box cfg hprec I heval rho hrho
    (fun i hi => hzero i (by simpa [hlen] using hi))
  · intro box hlen rho hrho hzero
    exact checkedMonotonicityPruner_correct_of_length (Expr.neg e) cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth } B box hlen rho hrho hzero
  exact hsuccess

/-- Checked affine evaluation on a box. -/
def evalOnBoxAffineChecked (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine) :
    EvalResult IntervalRat :=
  let acfg : AffineConfig := {
    taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }
  match evalIntervalAffineChecked e (toAffineEnv B) acfg with
  | .ok a => .ok a.toInterval
  | .error err => .error err

def globalMinimizeAffineChecked (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine := {}) :
    EvalResult GlobalResult :=
  globalMinimizeCheckedWith (fun box => evalOnBoxAffineChecked e box cfg)
    (checkedMonotonicityPruner e cfg.useMonotonicity { taylorDepth := cfg.taylorDepth })
    B cfg.maxIterations cfg.tolerance

def globalMaximizeAffineChecked (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine := {}) :
    EvalResult GlobalResult :=
  globalMaximizeCheckedWith (fun e box => evalOnBoxAffineChecked e box cfg)
    (fun expr => checkedMonotonicityPruner expr cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth }) e B cfg.maxIterations cfg.tolerance

theorem evalOnBoxAffineChecked_lo_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfigAffine) (I : IntervalRat)
    (hsuccess : evalOnBoxAffineChecked e B cfg = .ok I)
    (rho : Nat → ℝ) (hrho : Box.envMem rho B)
    (hzero : ∀ i, i ≥ B.length → rho i = 0) :
    (I.lo : ℝ) ≤ Expr.eval rho e := by
  let acfg : AffineConfig := {
    taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }
  obtain ⟨eps, hvalid, henv⟩ := LeanCert.Engine.exists_noise_toAffineEnv B rho
    (fun i hi => hrho ⟨i, hi⟩) hzero
  cases heval : evalIntervalAffineChecked e (toAffineEnv B) acfg with
  | error err =>
      change (match evalIntervalAffineChecked e (toAffineEnv B) acfg with
        | Except.ok a => Except.ok a.toInterval
        | Except.error err => Except.error err) =
          (Except.ok I : EvalResult IntervalRat) at hsuccess
      rw [heval] at hsuccess
      contradiction
  | ok a =>
      have hresult : I = a.toInterval := by
        change (match evalIntervalAffineChecked e (toAffineEnv B) acfg with
          | Except.ok a => Except.ok a.toInterval
          | Except.error err => Except.error err) =
            (Except.ok I : EvalResult IntervalRat) at hsuccess
        rw [heval] at hsuccess
        injection hsuccess with h
        exact h.symm
      subst I
      have hmemAffine := evalIntervalAffineChecked_correct e rho (toAffineEnv B) eps
        hvalid henv acfg a heval
      exact ((IntervalRat.mem_def _ _).mp
        (AffineForm.mem_toInterval_weak hvalid hmemAffine)).1

theorem globalMinimizeAffineChecked_lo_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfigAffine) (result : GlobalResult)
    (hsuccess : globalMinimizeAffineChecked e B cfg = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      (result.bound.lo : ℝ) ≤ Expr.eval rho e := by
  apply globalMinimizeCheckedWith_lower_correct
    (fun box => evalOnBoxAffineChecked e box cfg)
    (checkedMonotonicityPruner e cfg.useMonotonicity { taylorDepth := cfg.taylorDepth })
    B cfg.maxIterations cfg.tolerance (fun rho => Expr.eval rho e)
  intro box I heval hlen rho hrho hzero
  exact evalOnBoxAffineChecked_lo_correct e box cfg I heval rho hrho
    (fun i hi => hzero i (by simpa [hlen] using hi))
  · intro box hlen rho hrho hzero
    exact checkedMonotonicityPruner_correct_of_length e cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth } B box hlen rho hrho hzero
  · exact hsuccess

theorem globalMaximizeAffineChecked_hi_correct (e : Expr) (B : Box)
    (cfg : GlobalOptConfigAffine) (result : GlobalResult)
    (hsuccess : globalMaximizeAffineChecked e B cfg = .ok result) :
    ∀ rho, Box.envMem rho B → (∀ i, i ≥ B.length → rho i = 0) →
      Expr.eval rho e ≤ (result.bound.hi : ℝ) := by
  apply globalMaximizeCheckedWith_upper_correct
    (fun expr box => evalOnBoxAffineChecked expr box cfg)
    (fun expr => checkedMonotonicityPruner expr cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth }) e B
      cfg.maxIterations cfg.tolerance
  intro box I heval hlen rho hrho hzero
  exact evalOnBoxAffineChecked_lo_correct (Expr.neg e) box cfg I heval rho hrho
    (fun i hi => hzero i (by simpa [hlen] using hi))
  · intro box hlen rho hrho hzero
    exact checkedMonotonicityPruner_correct_of_length (Expr.neg e) cfg.useMonotonicity
      { taylorDepth := cfg.taylorDepth } B box hlen rho hrho hzero
  exact hsuccess

end LeanCert.Engine.Optimization
