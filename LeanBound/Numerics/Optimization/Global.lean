/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.IntervalEval
import LeanBound.Numerics.IntervalEvalRefined
import LeanBound.Numerics.Optimization.Box
import LeanBound.Numerics.Optimization.Gradient

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

namespace LeanBound.Numerics.Optimization

open LeanBound.Core
open LeanBound.Numerics

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

/-- Pop the box with smallest lower bound -/
def popBest (queue : List (ℚ × Box)) : Option ((ℚ × Box) × List (ℚ × Box)) :=
  match queue with
  | [] => none
  | best :: rest => some (best, rest)

/-! ### Core algorithm -/

/-- Evaluate expression on a box and get interval bounds -/
noncomputable def evalOnBox (e : Expr) (B : Box) (_cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalRefined e (Box.toEnv B)

/-- One step of branch-and-bound for minimization with explicit bestLB tracking.
    When `cfg.useMonotonicity` is true, applies gradient-based pruning before evaluation. -/
noncomputable def minimizeStep (e : Expr) (cfg : GlobalOptConfig)
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
      let I := evalOnBox e B_curr cfg
      -- Update global lower bound: min of old and this box's local lower bound
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
        let I1 := evalOnBox e B1 cfg
        let I2 := evalOnBox e B2 cfg
        -- Only add boxes that can potentially improve
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound for a fixed number of iterations with explicit bestLB tracking -/
noncomputable def minimizeLoop (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStep e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoop e cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization over a box -/
noncomputable def globalMinimize (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBox e B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  let initialBestLB : ℚ := I.lo
  let initialBestUB : ℚ := I.hi
  let initialBestBox : Box := B
  minimizeLoop e cfg initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/-- Global maximization over a box (minimize -e) -/
noncomputable def globalMaximize (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimize (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Computable versions for execution -/

/-- Evaluate expression on a box (computable version for ExprSupportedCore) -/
def evalOnBoxCore (e : Expr) (B : Box) (cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalCore e (Box.toEnv B) { taylorDepth := cfg.taylorDepth }

/-- Evaluate expression on a box (computable version with division support).
    This is used by the Python bridge for applications where division is common.
    Note: No formal correctness proof yet; returns sound but possibly wide bounds. -/
def evalOnBoxCoreDiv (e : Expr) (B : Box) (cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalCoreWithDiv e (Box.toEnv B) { taylorDepth := cfg.taylorDepth }

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

/-! ### Division-supporting versions for Python bridge

These variants use evalIntervalCoreWithDiv which handles division (inv) properly.
They have the same structure as the standard versions but support expressions with division. -/

/-- One step of branch-and-bound with division support -/
def minimizeStepCoreDiv (e : Expr) (cfg : GlobalOptConfig)
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
      let I := evalOnBoxCoreDiv e B_curr cfg
      let newBestLB := min bestLB I.lo
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      if Box.maxWidth B_curr ≤ cfg.tolerance then
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := evalOnBoxCoreDiv e B1 cfg
        let I2 := evalOnBoxCoreDiv e B2 cfg
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound loop with division support -/
def minimizeLoopCoreDiv (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepCoreDiv e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopCoreDiv e cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization with division support -/
def globalMinimizeCoreDiv (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBoxCoreDiv e B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  minimizeLoopCoreDiv e cfg initialQueue I.lo I.hi B cfg.maxIterations

/-- Global maximization with division support -/
def globalMaximizeCoreDiv (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimizeCoreDiv (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Correctness theorems -/

/-- The lower bound from interval evaluation is correct. -/
theorem evalOnBox_lo_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    (evalOnBox e B cfg).lo ≤ Expr.eval ρ e := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalRefined_correct e hsupp ρ (Box.toEnv B) henv
  simp only [evalOnBox]
  exact hmem.1

/-- The upper bound from interval evaluation is correct (∃ point achieving it). -/
theorem evalOnBox_hi_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    Expr.eval ρ e ≤ (evalOnBox e B cfg).hi := by
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

/-! ### New simplified correctness architecture with explicit bestLB tracking

The key idea: track both bestLB (global lower bound) and bestUB (global upper bound) explicitly.
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
theorem minimizeStep_nonempty (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    ∃ result, minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some result := by
  simp only [minimizeStep, popBest]
  split_ifs <;> exact ⟨_, rfl⟩

/-- Helper: bestUB only decreases during minimizeStep -/
theorem minimizeStep_bestUB_le (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
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
theorem minimizeStep_bestLB_le (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
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
theorem minimizeStep_queue_entries (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
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
theorem minimizeStep_bestBox_cases (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestBox' = bestBox ∨
    bestBox' = (if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2) := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals rcases hStep with ⟨_, _, _, hBox⟩
  all_goals rw [← hBox]
  all_goals first | left; rfl | right; simp_all

/-- Helper: queue entries in result are either from tl or splits of B_curr (the possibly pruned hd.2) -/
theorem minimizeStep_queue_boxes (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
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
theorem minimizeStep_bestUB_achievable (e : Expr) (hsupp : ExprSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
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
theorem minimizeStep_preserves_LB (e : Expr) (hsupp : ExprSupported e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
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
             have hmin_le : bestLB ⊓ (evalOnBox e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBox e B_curr cfg).lo : ℚ) : ℝ)
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
             have hmin_le : bestLB ⊓ (evalOnBox e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBox e B_curr cfg).lo : ℚ) : ℝ)
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
theorem minimizeLoop_correct (e : Expr) (hsupp : ExprSupported e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat)
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
    let result := minimizeLoop e cfg queue bestLB bestUB bestBox iters
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
    cases hstep : minimizeStep e cfg queue bestLB bestUB bestBox with
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
theorem globalMinimize_lo_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimize e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimize]
  let I := evalOnBox e B cfg
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
theorem globalMinimize_hi_achievable (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ (globalMinimize e B cfg).bound.hi := by
  simp only [globalMinimize]
  let I := evalOnBox e B cfg
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
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    (evalOnBoxCore e B cfg).lo ≤ Expr.eval ρ e := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalCore_correct e hsupp ρ (Box.toEnv B) henv { taylorDepth := cfg.taylorDepth }
  simp only [evalOnBoxCore]
  exact hmem.1

/-- The upper bound from core interval evaluation is correct. -/
theorem evalOnBoxCore_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    Expr.eval ρ e ≤ (evalOnBoxCore e B cfg).hi := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalCore_correct e hsupp ρ (Box.toEnv B) henv { taylorDepth := cfg.taylorDepth }
  simp only [evalOnBoxCore]
  exact hmem.2

/-- minimizeStepCore preserves the lower bound invariant. -/
theorem minimizeStepCore_preserves_LB (e : Expr) (hsupp : ExprSupportedCore e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepCore e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
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
                  · exact evalOnBoxCore_hi_correct e hsupp hd.2 cfg (Box.midpointEnv hd.2)
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
                    have heval := evalOnBoxCore_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
                      (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr)
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
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
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
          result.1 result.2.1 result.2.2.1 result.2.2.2 hstep hLB hUB hQueueSub
      exact ih result.1 result.2.1 result.2.2.1 result.2.2.2 hLB' hUB' hQueueSub'

/-- The key correctness theorem for Core version: globalMinimizeCore returns a lower bound
    that is ≤ the minimum of f over any point in the original box. -/
theorem globalMinimizeCore_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeCore e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeCore]
  let I := evalOnBoxCore e B cfg
  -- Initial invariants
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBoxCore_lo_correct e hsupp B cfg ρ' hρ' hzero'
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBoxCore_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoopCore_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0
  exact hResult.1 ρ hρ hzero

/-- There exists a point achieving (approximately) the upper bound for Core version. -/
theorem globalMinimizeCore_hi_achievable (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ (globalMinimizeCore e B cfg).bound.hi := by
  simp only [globalMinimizeCore]
  let I := evalOnBoxCore e B cfg
  -- Initial invariants
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBoxCore_lo_correct e hsupp B cfg ρ' hρ' hzero'
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBoxCore_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoopCore_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0
  exact hResult.2

/-- The lower bound is ≤ the upper bound.
    This follows from the existence of a witness: there's some ρ with f(ρ) ≤ hi,
    and lo ≤ f(ρ) for all ρ in B, so lo ≤ f(witness) ≤ hi. -/
theorem globalMinimizeCore_lo_le_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) :
    (globalMinimizeCore e B cfg).bound.lo ≤ (globalMinimizeCore e B cfg).bound.hi := by
  -- Get the witness that achieves ≤ hi
  obtain ⟨ρ, hρ, hzero, hhi⟩ := globalMinimizeCore_hi_achievable e hsupp B cfg
  -- Get that lo ≤ f(ρ) for this witness
  have hlo := globalMinimizeCore_lo_correct e hsupp B cfg ρ hρ hzero
  -- Combine: lo ≤ f(ρ) ≤ hi, then cast back to ℚ
  have h : ((globalMinimizeCore e B cfg).bound.lo : ℝ) ≤ (globalMinimizeCore e B cfg).bound.hi :=
    calc ((globalMinimizeCore e B cfg).bound.lo : ℝ)
      ≤ Expr.eval ρ e := hlo
      _ ≤ (globalMinimizeCore e B cfg).bound.hi := hhi
  exact_mod_cast h

/-! ### Maximization correctness theorems -/

/-- The upper bound from globalMaximizeCore is correct: f(ρ) ≤ hi for all ρ in B. -/
theorem globalMaximizeCore_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeCore e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hmin := globalMinimizeCore_lo_correct (Expr.neg e) hneg_supp B cfg ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  -- hmin : (globalMinimizeCore e.neg B cfg).bound.lo ≤ -Expr.eval ρ e
  -- Goal: Expr.eval ρ e ≤ -(globalMinimizeCore e.neg B cfg).bound.lo
  have h : Expr.eval ρ e ≤ (-(globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

/-- There exists a point achieving approximately the lower bound for maximization. -/
theorem globalMaximizeCore_lo_achievable (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      (globalMaximizeCore e B cfg).bound.lo ≤ Expr.eval ρ e := by
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  obtain ⟨ρ, hρ, hzero, hhi⟩ := globalMinimizeCore_hi_achievable (Expr.neg e) hneg_supp B cfg
  use ρ, hρ, hzero
  simp only [Expr.eval_neg] at hhi
  -- hhi : -Expr.eval ρ e ≤ (globalMinimizeCore e.neg B cfg).bound.hi
  -- Goal: -(globalMinimizeCore e.neg B cfg).bound.hi ≤ Expr.eval ρ e
  have h : (-(globalMinimizeCore (Expr.neg e) B cfg).bound.hi : ℝ) ≤ Expr.eval ρ e := by linarith
  exact_mod_cast h

/-- The lower bound is ≤ the upper bound for maximization. -/
theorem globalMaximizeCore_lo_le_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) :
    (globalMaximizeCore e B cfg).bound.lo ≤ (globalMaximizeCore e B cfg).bound.hi := by
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have h := globalMinimizeCore_lo_le_hi (Expr.neg e) hneg_supp B cfg
  linarith

end LeanBound.Numerics.Optimization
