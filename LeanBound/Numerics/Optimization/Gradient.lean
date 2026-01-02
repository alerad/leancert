/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.AD
import LeanBound.Numerics.Optimize
import LeanBound.Numerics.Optimization.Box

/-!
# Gradient Interval Computation for Optimization

This file provides functions to compute interval bounds on the gradient ∇f(B)
of an expression over a box B. This is used for monotonicity-based pruning
in branch-and-bound global optimization.

## Main definitions

* `gradientInterval` - Compute interval bounds on all partial derivatives over a box
* `gradientSignature` - Determine the sign of each partial derivative
* `canPruneToLo` / `canPruneToHi` - Check if a coordinate can be pruned by monotonicity

## Design

The gradient is computed by running forward-mode AD (from AD.lean) for each
coordinate direction. The result is a list of intervals, one per variable.

Monotonicity pruning: If ∂f/∂xᵢ > 0 on the entire box B, then f is minimized
when xᵢ = B[i].lo. We can shrink the box in that dimension to a point.
-/

namespace LeanBound.Numerics.Optimization

open LeanBound.Core
open LeanBound.Numerics

/-! ### Gradient computation -/

/-- Compute the gradient interval: bounds on each partial derivative over a box.
    Returns a list of intervals, where the i-th interval contains ∂f/∂xᵢ for all x ∈ B. -/
noncomputable def gradientInterval (e : Expr) (B : Box) : List IntervalRat :=
  List.ofFn fun (i : Fin B.length) => derivInterval e (Box.toEnv B) i.val

/-- Compute gradient for n variables (explicit dimension) -/
noncomputable def gradientIntervalN (e : Expr) (B : Box) (n : Nat) : List IntervalRat :=
  (List.range n).map fun i => derivInterval e (Box.toEnv B) i

/-! ### Computable versions -/

/-- Create dual environment for differentiating with respect to variable `idx` (computable).
    Active variable gets der = 1, passive variables get der = 0. -/
def mkDualEnvCore (ρ : IntervalEnv) (idx : Nat) : DualEnv :=
  fun i => if i = idx then DualInterval.varActive (ρ i) else DualInterval.varPassive (ρ i)

/-- Evaluate with derivative with respect to variable `idx` (computable version) -/
def evalWithDerivCore (e : Expr) (ρ : IntervalEnv) (idx : Nat) (cfg : EvalConfig := {}) : DualInterval :=
  evalDualCore e (mkDualEnvCore ρ idx) cfg

/-- Computable derivative interval for multi-variable expressions.
    Computes the interval containing ∂f/∂xᵢ over the box. -/
def derivIntervalCoreN (e : Expr) (ρ : IntervalEnv) (idx : Nat) (cfg : EvalConfig := {}) : IntervalRat :=
  (evalWithDerivCore e ρ idx cfg).der

/-- Computable version of gradient interval for Core expressions.
    This can be used with `native_decide` for verified optimization. -/
def gradientIntervalCore (e : Expr) (B : Box) (cfg : EvalConfig := {}) : List IntervalRat :=
  (List.range B.length).map fun i => derivIntervalCoreN e (Box.toEnv B) i cfg

/-! ### Sign classification -/

/-- Classification of an interval's sign -/
inductive IntervalSign where
  | positive     -- lo > 0 (strictly positive)
  | negative     -- hi < 0 (strictly negative)
  | nonpositive  -- hi ≤ 0
  | nonnegative  -- lo ≥ 0
  | indefinite   -- contains zero in interior
  deriving Repr, DecidableEq

/-- Classify the sign of an interval -/
def classifySign (I : IntervalRat) : IntervalSign :=
  if I.lo > 0 then .positive
  else if I.hi < 0 then .negative
  else if I.hi ≤ 0 then .nonpositive
  else if I.lo ≥ 0 then .nonnegative
  else .indefinite

/-- The gradient signature: sign of each partial derivative (noncomputable wrapper) -/
noncomputable def gradientSignature (e : Expr) (B : Box) : List IntervalSign :=
  (gradientIntervalN e B B.length).map classifySign

/-! ### Monotonicity predicates -/

/-- Check if interval is strictly positive -/
def isStrictlyPositive (I : IntervalRat) : Bool := I.lo > 0

/-- Check if interval is strictly negative -/
def isStrictlyNegative (I : IntervalRat) : Bool := I.hi < 0

/-- Check if interval is nonnegative -/
def isNonnegative (I : IntervalRat) : Bool := I.lo ≥ 0

/-- Check if interval is nonpositive -/
def isNonpositive (I : IntervalRat) : Bool := I.hi ≤ 0

/-! ### Pruning queries -/

/-- Can we prune coordinate i to its low endpoint for minimization?
    True if ∂f/∂xᵢ > 0 on B (f is increasing in xᵢ, so min is at lo). -/
def canPruneToLo (deriv_i : IntervalRat) : Bool :=
  isStrictlyPositive deriv_i

/-- Can we prune coordinate i to its high endpoint for minimization?
    True if ∂f/∂xᵢ < 0 on B (f is decreasing in xᵢ, so min is at hi). -/
def canPruneToHi (deriv_i : IntervalRat) : Bool :=
  isStrictlyNegative deriv_i

/-- Prune a box for minimization by fixing monotonic coordinates.
    Returns a (potentially smaller) box and a list of fixed coordinates. -/
def pruneBoxForMin (B : Box) (grad : List IntervalRat) : Box × List Nat :=
  let pruned := B.zipIdx.map fun (I, idx) =>
    match grad[idx]? with
    | some di =>
      if canPruneToLo di then
        -- ∂f/∂xᵢ > 0: fix xᵢ = I.lo
        (IntervalRat.singleton I.lo, some idx)
      else if canPruneToHi di then
        -- ∂f/∂xᵢ < 0: fix xᵢ = I.hi
        (IntervalRat.singleton I.hi, some idx)
      else
        (I, none)
    | none => (I, none)
  (pruned.map (·.1), pruned.filterMap (·.2))

/-! ### Correctness theorems -/

/-- The computed gradient interval contains the true partial derivatives.
    This follows from evalDual_der_correct_idx in AD.lean. -/
theorem gradientInterval_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (i : Fin B.length) :
    deriv (Expr.evalAlong e ρ i.val) (ρ i.val) ∈
      ((gradientIntervalN e B B.length)[i.val]?).getD default := by
  -- The i-th element of gradientIntervalN is derivInterval e (toEnv B) i
  have hget : (gradientIntervalN e B B.length)[i.val]? =
      some (derivInterval e (Box.toEnv B) i.val) := by
    simp only [gradientIntervalN]
    rw [List.getElem?_map]
    simp only [List.getElem?_range i.isLt, Option.map_some]
  simp only [hget, Option.getD]
  -- Apply the AD correctness theorem
  have henv : ∀ j, ρ j ∈ Box.toEnv B j := Box.envMem_toEnv ρ B hρ hzero
  exact derivInterval_correct_idx e hsupp ρ (Box.toEnv B) i.val henv (ρ i.val) (henv i.val)

/-- If we prune a coordinate to lo because ∂f/∂xᵢ > 0, the minimum is preserved.
    Informal: if f is increasing in xᵢ on B, then min{f(x) : x ∈ B} = min{f(x) : xᵢ = B[i].lo}.
    NOTE: Requires ρ j = 0 for j ≥ B.length (standard assumption for box membership). -/
theorem pruneToLo_preserves_min (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (i : Fin B.length)
    (hgrad : isStrictlyPositive (derivInterval e (Box.toEnv B) i.val) = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ j, j ≥ B.length → ρ j = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B ∧ (∀ j, j ≥ B.length → ρ' j = 0) ∧
        ρ' i.val = B[i.val].lo ∧ Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  -- The idea: if ∂f/∂xᵢ > 0 everywhere, then f(ρ) ≥ f(ρ[xᵢ := lo])
  -- We construct ρ' by replacing coordinate i with the low endpoint
  let ρ' : Nat → ℝ := fun j => if j = i.val then (B[i.val].lo : ℝ) else ρ j
  use ρ'
  constructor
  · -- ρ' ∈ B
    intro ⟨j, hj⟩
    by_cases h : j = i.val
    · subst h
      simp only [↓reduceIte, ρ', IntervalRat.mem_def]
      constructor
      · exact le_refl _
      · have := B[i.val].le
        exact_mod_cast this
    · simp only [if_neg h, ρ']
      exact hρ ⟨j, hj⟩
  constructor
  · -- ρ' j = 0 for j ≥ B.length
    intro j hj
    simp only [ρ']
    have hne : j ≠ i.val := by
      intro heq
      rw [heq] at hj
      exact absurd i.isLt (not_lt.mpr hj)
    simp only [if_neg hne]
    exact hzero j hj
  constructor
  · -- ρ' i = B[i].lo
    simp only [↓reduceIte, ρ']
  · -- f(ρ') ≤ f(ρ)
    -- Use the monotonicity theorem: if ∂f/∂xᵢ > 0, minimum is at left endpoint
    -- Convert the boolean condition to a real inequality
    simp only [isStrictlyPositive, decide_eq_true_eq] at hgrad
    -- Build the interval environment from the box
    let ρ_int : IntervalEnv := Box.toEnv B
    -- Show ρ ∈ ρ_int (membership in the interval environment)
    have hρ_int : ∀ j, ρ j ∈ ρ_int j := by
      intro j
      simp only [ρ_int, Box.toEnv, List.getD]
      by_cases hj : j < B.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD]
        exact hρ ⟨j, hj⟩
      · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
        rw [IntervalRat.mem_default]
        exact hzero j (not_lt.mp hj)
    -- Apply the monotonicity theorem
    have hmono := increasing_min_at_left_idx e hsupp ρ ρ_int i.val hρ_int hgrad
    -- The key fact: ρ i.val ∈ ρ_int i.val = B[i.val]
    have hρ_i_mem : ρ i.val ∈ ρ_int i.val := hρ_int i.val
    have hmin := hmono (ρ i.val) hρ_i_mem
    -- Now relate evalAlong to eval via ρ'
    -- evalAlong e ρ i.val t = eval (updateVar ρ i.val t) e
    simp only [Expr.evalAlong] at hmin
    -- Need: (ρ_int i.val).lo = B[i.val].lo
    have hlo_eq : (ρ_int i.val).lo = B[i.val].lo := by
      simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem i.isLt, Option.getD]
    -- And: updateVar ρ i.val (ρ_int i.val).lo = ρ'
    have hρ'_eq : Expr.updateVar ρ i.val ((ρ_int i.val).lo : ℝ) = ρ' := by
      funext j
      simp only [Expr.updateVar, ρ']
      split_ifs with hj
      · simp only [hlo_eq]
      · rfl
    -- And: updateVar ρ i.val (ρ i.val) = ρ
    have hρ_eq : Expr.updateVar ρ i.val (ρ i.val) = ρ := Expr.updateVar_self ρ i.val
    rw [hρ'_eq, hρ_eq] at hmin
    exact hmin

/-- If we prune a coordinate to hi because ∂f/∂xᵢ < 0, the minimum is preserved.
    NOTE: Requires ρ j = 0 for j ≥ B.length (standard assumption for box membership). -/
theorem pruneToHi_preserves_min (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (i : Fin B.length)
    (hgrad : isStrictlyNegative (derivInterval e (Box.toEnv B) i.val) = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ j, j ≥ B.length → ρ j = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B ∧ (∀ j, j ≥ B.length → ρ' j = 0) ∧
        ρ' i.val = B[i.val].hi ∧ Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  let ρ' : Nat → ℝ := fun j => if j = i.val then (B[i.val].hi : ℝ) else ρ j
  use ρ'
  constructor
  · -- ρ' ∈ B
    intro ⟨j, hj⟩
    by_cases h : j = i.val
    · subst h
      simp only [↓reduceIte, ρ', IntervalRat.mem_def]
      constructor
      · have := B[i.val].le
        exact_mod_cast this
      · exact le_refl _
    · simp only [if_neg h, ρ']
      exact hρ ⟨j, hj⟩
  constructor
  · -- ρ' j = 0 for j ≥ B.length
    intro j hj
    simp only [ρ']
    have hne : j ≠ i.val := by
      intro heq
      rw [heq] at hj
      exact absurd i.isLt (not_lt.mpr hj)
    simp only [if_neg hne]
    exact hzero j hj
  constructor
  · simp only [↓reduceIte, ρ']
  · -- f(ρ') ≤ f(ρ)
    -- Use the monotonicity theorem: if ∂f/∂xᵢ < 0, minimum is at right endpoint
    simp only [isStrictlyNegative, decide_eq_true_eq] at hgrad
    -- Build the interval environment from the box
    let ρ_int : IntervalEnv := Box.toEnv B
    -- Show ρ ∈ ρ_int
    have hρ_int : ∀ j, ρ j ∈ ρ_int j := by
      intro j
      simp only [ρ_int, Box.toEnv, List.getD]
      by_cases hj : j < B.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD]
        exact hρ ⟨j, hj⟩
      · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
        rw [IntervalRat.mem_default]
        exact hzero j (not_lt.mp hj)
    -- Apply the monotonicity theorem for decreasing functions
    have hmono := decreasing_min_at_right_idx e hsupp ρ ρ_int i.val hρ_int hgrad
    -- The key fact: ρ i.val ∈ ρ_int i.val = B[i.val]
    have hρ_i_mem : ρ i.val ∈ ρ_int i.val := hρ_int i.val
    have hmin := hmono (ρ i.val) hρ_i_mem
    -- Now relate evalAlong to eval via ρ'
    simp only [Expr.evalAlong] at hmin
    -- Need: (ρ_int i.val).hi = B[i.val].hi
    have hhi_eq : (ρ_int i.val).hi = B[i.val].hi := by
      simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem i.isLt, Option.getD]
    -- And: updateVar ρ i.val (ρ_int i.val).hi = ρ'
    have hρ'_eq : Expr.updateVar ρ i.val ((ρ_int i.val).hi : ℝ) = ρ' := by
      funext j
      simp only [Expr.updateVar, ρ']
      split_ifs with hj
      · simp only [hhi_eq]
      · rfl
    -- And: updateVar ρ i.val (ρ i.val) = ρ
    have hρ_eq : Expr.updateVar ρ i.val (ρ i.val) = ρ := Expr.updateVar_self ρ i.val
    rw [hρ'_eq, hρ_eq] at hmin
    exact hmin

/-! ### Pruned box membership and correctness -/

/-- Helper: membership in the pruned box implies membership in the original box.
    The pruned box only shrinks coordinates, never expands them. -/
theorem pruneBoxForMin_subset (B : Box) (grad : List IntervalRat) :
    ∀ ρ, Box.envMem ρ (pruneBoxForMin B grad).1 → Box.envMem ρ B := by
  intro ρ hρ'
  let B' := (pruneBoxForMin B grad).1
  intro ⟨j, hj⟩
  have hj' : j < B'.length := by
    simp only [B', pruneBoxForMin, List.length_map, List.length_zipIdx]
    exact hj
  have hρ'_mem : ρ j ∈ B'[j] := hρ' ⟨j, hj'⟩
  -- Get the j-th element of B'
  simp only [B', pruneBoxForMin] at hρ'_mem
  rw [List.getElem_map, List.getElem_map] at hρ'_mem
  have h_zipIdx_len : j < (B.zipIdx).length := by simp only [List.length_zipIdx]; exact hj
  have h_zipIdx : (B.zipIdx)[j] = (B[j], j) := by
    rw [List.getElem_zipIdx (h := h_zipIdx_len)]
    simp only [Nat.zero_add]
  simp only [h_zipIdx] at hρ'_mem
  -- Now analyze the cases
  cases hgrad_j : grad[j]? with
  | none =>
    simp only [hgrad_j] at hρ'_mem
    exact hρ'_mem
  | some di =>
    simp only [hgrad_j] at hρ'_mem
    by_cases hlo : canPruneToLo di
    · simp only [hlo, ↓reduceIte] at hρ'_mem
      simp only [IntervalRat.mem_def]
      have hρ_eq : ρ j = B[j].lo := by
        simp only [IntervalRat.singleton, IntervalRat.mem_def] at hρ'_mem
        linarith [hρ'_mem.1, hρ'_mem.2]
      rw [hρ_eq]
      exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
    · by_cases hhi : canPruneToHi di
      · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi] at hρ'_mem
        simp only [IntervalRat.mem_def]
        have hρ_eq : ρ j = B[j].hi := by
          simp only [IntervalRat.singleton, IntervalRat.mem_def] at hρ'_mem
          linarith [hρ'_mem.1, hρ'_mem.2]
        rw [hρ_eq]
        exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
      · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi] at hρ'_mem
        exact hρ'_mem

/-- The pruned box has the same length as the original box -/
theorem pruneBoxForMin_length (B : Box) (grad : List IntervalRat) :
    (pruneBoxForMin B grad).1.length = B.length := by
  simp only [pruneBoxForMin, List.length_map, List.length_zipIdx]

/-- **Main correctness theorem for pruneBoxForMin:**

    After pruning, for any point ρ in the original box B, there exists a point ρ'
    in the pruned box B' such that f(ρ') ≤ f(ρ).

    This means the minimum over B can be found by searching only in B'.

    The proof constructs ρ' by moving each coordinate to its endpoint when the
    gradient has a definite sign. For each coordinate:
    - If ∂f/∂xᵢ > 0 on B, move xᵢ to B[i].lo (f is increasing, min at left)
    - If ∂f/∂xᵢ < 0 on B, move xᵢ to B[i].hi (f is decreasing, min at right)
    - Otherwise, keep xᵢ = ρ[i]

    The proof then shows f(ρ') ≤ f(ρ) by induction on coordinates, using
    the monotonicity lemmas `increasing_min_at_left_idx` and `decreasing_min_at_right_idx`.
-/
theorem pruneBoxForMin_correct (e : Expr) (hsupp : ExprSupported e) (B : Box) :
    let grad := gradientIntervalN e B B.length
    let B' := (pruneBoxForMin B grad).1
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B' ∧ (∀ i, i ≥ B'.length → ρ' i = 0) ∧
        Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro grad B' ρ hρB hzero
  -- The proof proceeds by induction on the number of coordinates that can be pruned.
  -- For each pruneable coordinate i:
  -- - If grad[i] > 0: apply pruneToLo_preserves_min to move ρ[i] to B[i].lo
  -- - If grad[i] < 0: apply pruneToHi_preserves_min to move ρ[i] to B[i].hi
  --
  -- This is a bit complex because we need to apply the pruning steps sequentially.
  -- For simplicity, we'll prove a helper that applies a single pruning step,
  -- then use induction on the list of fixed coordinates.
  --
  -- Alternative approach: directly construct ρ' and prove the properties.
  -- ρ'[j] := B[j].lo if grad[j] > 0
  --          B[j].hi if grad[j] < 0
  --          ρ[j] otherwise
  --
  -- Then show f(ρ') ≤ f(ρ) using the individual monotonicity lemmas.

  -- Define ρ' based on gradient signs
  let ρ' : Nat → ℝ := fun j =>
    if h : j < B.length then
      match grad[j]? with
      | some di =>
        if canPruneToLo di then (B[j].lo : ℝ)
        else if canPruneToHi di then (B[j].hi : ℝ)
        else ρ j
      | none => ρ j
    else 0

  use ρ'
  constructor
  · -- ρ' ∈ B'
    intro ⟨j, hj'⟩
    have hB'_len : B'.length = B.length := pruneBoxForMin_length B grad
    have hj : j < B.length := by rw [← hB'_len]; exact hj'
    simp only [ρ', hj, ↓reduceDIte]
    -- B'[j] is determined by grad[j]
    simp only [B', pruneBoxForMin]
    rw [List.getElem_map, List.getElem_map]
    have h_zipIdx_len : j < (B.zipIdx).length := by simp only [List.length_zipIdx]; exact hj
    have h_zipIdx : (B.zipIdx)[j] = (B[j], j) := by
      rw [List.getElem_zipIdx (h := h_zipIdx_len)]
      simp only [Nat.zero_add]
    simp only [h_zipIdx]
    cases hgrad_j : grad[j]? with
    | none =>
      simp
      exact hρB ⟨j, hj⟩
    | some di =>
      simp
      by_cases hlo : canPruneToLo di
      · simp only [hlo, ↓reduceIte]
        exact IntervalRat.mem_singleton _
      · by_cases hhi : canPruneToHi di
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi]
          exact IntervalRat.mem_singleton _
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi]
          exact hρB ⟨j, hj⟩
  constructor
  · -- ρ' i = 0 for i ≥ B'.length
    intro i hi
    have hB'_len : B'.length = B.length := pruneBoxForMin_length B grad
    rw [hB'_len] at hi
    simp only [ρ', not_lt.mpr hi, ↓reduceDIte]
  · -- f(ρ') ≤ f(ρ)
    -- This is the key part. We need to show that replacing each coordinate
    -- according to gradient signs only decreases the function value.
    --
    -- Ideally, we'd use a lemma like:
    -- "If ρ' differs from ρ only in coordinates with definite gradient signs,
    --  and each changed coordinate moves in the direction that decreases f,
    --  then f(ρ') ≤ f(ρ)"
    --
    -- This requires reasoning about partial derivatives and MVT.
    -- The individual lemmas pruneToLo_preserves_min and pruneToHi_preserves_min
    -- handle single coordinates. For multiple coordinates, we need to compose them.
    --
    -- Key insight: the derivative bounds derivInterval are computed over the entire box,
    -- so they remain valid regardless of which other coordinates have been fixed.
    --
    -- Proof strategy: induct on the number of coordinates that differ between ρ and ρ'.
    -- At each step, change one coordinate using the appropriate monotonicity lemma.
    --
    -- For simplicity in this initial implementation, we'll use a direct approach
    -- leveraging the Mean Value Theorem for each coordinate.
    --
    -- TODO: This requires a more sophisticated proof involving MVT and sequential
    -- application of monotonicity. For now, we'll prove the key parts and leave
    -- the final integration as a task for later refinement.
    --
    -- Actually, the cleanest approach is to prove by induction on B.length,
    -- handling one coordinate at a time.

    -- For now, we use the fact that each coordinate change is monotonicity-preserving.
    -- The full proof requires showing that these changes compose correctly.
    -- We'll establish the result through a sequence of single-coordinate improvements.

    -- Sketch: For each j from 0 to B.length-1:
    --   Let ρⱼ be the environment after fixing coordinates 0..j-1
    --   If coord j is pruned, use pruneToLo/Hi_preserves_min to get ρⱼ₊₁ with f(ρⱼ₊₁) ≤ f(ρⱼ)
    --   Otherwise, ρⱼ₊₁ = ρⱼ
    -- The final ρ_{n} = ρ', and f(ρ') ≤ f(ρ₀) = f(ρ).

    -- For the actual proof, we need helper lemmas about sequential coordinate fixing.
    -- This is left as a refinement. For now, we establish the structure.

    -- TEMPORARY: Use the fact that when all coordinates are fixed according to
    -- their gradient signs, the result is at least as good as the original.
    -- Full proof requires induction on coordinates.

    -- Let's prove this by building a sequence of environments
    -- and showing each step doesn't increase the function value.

    -- Actually, we can prove this more directly by observing that:
    -- 1. For each coordinate j where ρ'[j] ≠ ρ[j], the gradient has a definite sign
    -- 2. The change ρ[j] → ρ'[j] moves in the direction that decreases f
    -- 3. By MVT, the total change is the sum of partial derivative contributions

    -- The formal proof uses induction on the number of differing coordinates.
    -- For now, we note that the building blocks (pruneToLo/Hi_preserves_min) are proven,
    -- and the composition follows from the same MVT reasoning applied sequentially.

    -- Implement the induction: build sequence ρ = ρ₀ → ρ₁ → ... → ρₙ = ρ'
    -- where each step fixes one coordinate and maintains f(ρⱼ₊₁) ≤ f(ρⱼ)

    -- We prove by strong induction on the number of coordinates n = B.length.
    -- Base case: n = 0, then ρ' = ρ (no coordinates to fix)
    -- Inductive case: fix coordinate 0 if needed, then apply IH to remaining coords

    -- Helper: sequence of intermediate environments
    -- ρ_seq k = environment with first k coordinates fixed according to pruning
    let ρ_seq : Nat → (Nat → ℝ) := fun k j =>
      if h : j < k ∧ j < B.length then
        match grad[j]? with
        | some di =>
          if canPruneToLo di then (B[j].lo : ℝ)
          else if canPruneToHi di then (B[j].hi : ℝ)
          else ρ j
        | none => ρ j
      else if hj : j < B.length then ρ j
      else 0

    -- Key property: ρ_seq 0 = ρ (modulo the zero extension)
    have hρ_seq_zero : ∀ j, ρ_seq 0 j = if j < B.length then ρ j else 0 := by
      intro j
      simp only [ρ_seq]
      -- j < 0 ∧ j < B.length is always false since j : Nat
      have h_neg : ¬(j < 0 ∧ j < B.length) := fun h => Nat.not_lt_zero j h.1
      simp only [dif_neg h_neg]
      -- Now we have: (if hj : j < B.length then ρ j else 0) = if j < B.length then ρ j else 0
      split_ifs <;> rfl

    -- Key property: ρ_seq B.length = ρ'
    have hρ_seq_final : ∀ j, ρ_seq B.length j = ρ' j := by
      intro j
      simp only [ρ_seq, ρ']
      by_cases hj : j < B.length
      · -- j < B.length
        have h_and : j < B.length ∧ j < B.length := ⟨hj, hj⟩
        simp only [dif_pos h_and, dif_pos hj]
      · -- j ≥ B.length
        have h_nand : ¬(j < B.length ∧ j < B.length) := fun h => hj h.2
        simp only [dif_neg h_nand, dif_neg hj]

    -- Key property: each step ρ_seq k → ρ_seq (k+1) only changes coord k
    have hρ_seq_step : ∀ k j, k ≠ j → ρ_seq k j = ρ_seq (k + 1) j := by
      intro k j hne
      simp only [ρ_seq]
      by_cases h1 : j < k ∧ j < B.length
      · -- j < k and j < B.length: both difs are positive
        have h2 : j < k + 1 ∧ j < B.length := ⟨Nat.lt_of_lt_of_le h1.1 (Nat.le_succ k), h1.2⟩
        simp only [dif_pos h1, dif_pos h2]
      · by_cases h2 : j < k + 1 ∧ j < B.length
        · -- j < k + 1 but not (j < k ∧ j < B.length)
          -- Since j < B.length (from h2.2), we must have ¬(j < k)
          have hj_ge_k : k ≤ j := by
            by_contra hlt
            push_neg at hlt
            exact h1 ⟨hlt, h2.2⟩
          have hj_lt_k1 : j < k + 1 := h2.1
          have hj_eq_k : j = k := Nat.eq_of_le_of_lt_succ hj_ge_k hj_lt_k1
          exact absurd hj_eq_k.symm hne
        · -- Neither condition holds
          simp only [dif_neg h1, dif_neg h2]

    -- The main induction: prove f(ρ_seq k) is non-increasing in k
    -- Use the single-coordinate monotonicity lemmas

    -- First, prove the single step property (needed for both induction cases)
    have hstep : ∀ m < B.length, Expr.eval (ρ_seq (m + 1)) e ≤ Expr.eval (ρ_seq m) e := by
        intro m hm
        -- At step m, we potentially fix coordinate m
        -- If grad[m] > 0, we set coord m to lo
        -- If grad[m] < 0, we set coord m to hi
        -- Otherwise, no change

        -- Check what happens at coordinate m
        cases hgrad_m : grad[m]? with
        | none =>
          -- No gradient info, ρ_seq (m+1) and ρ_seq m agree
          have heq : ∀ j, ρ_seq (m + 1) j = ρ_seq m j := by
            intro j
            by_cases hj_eq : j = m
            · -- When j = m: both sides simplify to ρ m
              simp only [ρ_seq, hgrad_m, hj_eq]
              have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
              have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
              simp only [dif_neg h1, dif_pos h2, dif_pos hm]
            · exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
          simp only [funext heq]
          exact le_refl _
        | some di =>
          by_cases hlo : canPruneToLo di
          · -- ∂f/∂x_m > 0, fixing x_m = lo decreases f
            -- Need to show ρ_seq (m+1) is like ρ_seq m but with coord m fixed to lo
            -- And that this decreases f by pruneToLo_preserves_min

            -- First, understand the relationship between ρ_seq m and ρ_seq (m+1)
            have hcoord_m_before : ρ_seq m m = ρ m := by
              simp only [ρ_seq]
              have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
              simp only [dif_neg h1, dif_pos hm]

            have hcoord_m_after : ρ_seq (m + 1) m = B[m].lo := by
              simp only [ρ_seq, hgrad_m, hlo, ↓reduceIte]
              have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
              simp only [dif_pos h2]

            -- ρ_seq m is in B
            have hρ_seq_m_mem : Box.envMem (ρ_seq m) B := by
              intro ⟨j, hj⟩
              simp only [ρ_seq]
              by_cases h1 : j < m ∧ j < B.length
              · simp only [dif_pos h1]
                cases hgrad_j : grad[j]? with
                | none => exact hρB ⟨j, hj⟩
                | some dj =>
                  simp
                  by_cases hlo_j : canPruneToLo dj
                  · simp only [hlo_j, ↓reduceIte]
                    exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
                  · by_cases hhi_j : canPruneToHi dj
                    · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
                      exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
                    · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
                      exact hρB ⟨j, hj⟩
              · simp only [dif_neg h1, dif_pos hj]
                exact hρB ⟨j, hj⟩

            have hρ_seq_m_zero : ∀ j, j ≥ B.length → ρ_seq m j = 0 := by
              intro j hjge
              simp only [ρ_seq]
              have h1 : ¬(j < m ∧ j < B.length) := fun h => absurd h.2 (not_lt.mpr hjge)
              simp only [dif_neg h1]
              have h2 : ¬(j < B.length) := not_lt.mpr hjge
              simp only [dif_neg h2]

            -- The gradient at coord m is strictly positive
            have hgrad_di : derivInterval e (Box.toEnv B) m = di := by
              simp only [grad, gradientIntervalN] at hgrad_m
              rw [List.getElem?_map, List.getElem?_range hm] at hgrad_m
              simp only [Option.map_some] at hgrad_m
              exact Option.some.inj hgrad_m

            -- Build the interval environment from the box
            let ρ_int : IntervalEnv := Box.toEnv B

            -- Show ρ_seq m ∈ ρ_int
            have hρ_int : ∀ j, ρ_seq m j ∈ ρ_int j := by
              intro j
              simp only [ρ_int, Box.toEnv, List.getD]
              by_cases hj : j < B.length
              · simp only [List.getElem?_eq_getElem hj, Option.getD]
                exact hρ_seq_m_mem ⟨j, hj⟩
              · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
                rw [IntervalRat.mem_default]
                exact hρ_seq_m_zero j (not_lt.mp hj)

            -- Convert isStrictlyPositive to 0 < lo
            have hpos : 0 < (derivInterval e ρ_int m).lo := by
              simp only [ρ_int]
              rw [hgrad_di]
              simp only [isStrictlyPositive, canPruneToLo] at hlo
              exact decide_eq_true_iff.mp hlo

            -- Apply the monotonicity theorem for increasing functions
            have hmono := increasing_min_at_left_idx e hsupp (ρ_seq m) ρ_int m hρ_int hpos

            -- ρ_seq m at coord m is in the interval
            have hρ_m_mem : ρ_seq m m ∈ ρ_int m := hρ_int m
            have hmin := hmono (ρ_seq m m) hρ_m_mem

            -- (ρ_int m).lo = B[m].lo
            have hlo_eq : (ρ_int m).lo = B[m].lo := by
              simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem hm, Option.getD]

            -- Rewrite in terms of eval
            simp only [Expr.evalAlong] at hmin
            have hupdate_self : Expr.updateVar (ρ_seq m) m (ρ_seq m m) = ρ_seq m :=
              Expr.updateVar_self (ρ_seq m) m

            -- ρ_seq (m+1) = updateVar (ρ_seq m) m (B[m].lo)
            have hρ_seq_update : ρ_seq (m + 1) = Expr.updateVar (ρ_seq m) m (B[m].lo : ℝ) := by
              funext j
              simp only [Expr.updateVar]
              by_cases hj_eq : j = m
              · subst hj_eq
                simp only [↓reduceIte]
                exact hcoord_m_after
              · simp only [if_neg hj_eq]
                exact (hρ_seq_step m j (Ne.symm hj_eq)).symm

            have hupdate_lo : Expr.updateVar (ρ_seq m) m ((ρ_int m).lo : ℝ) = ρ_seq (m + 1) := by
              rw [hlo_eq, ← hρ_seq_update]
            rw [hupdate_lo, hupdate_self] at hmin
            exact hmin

          · by_cases hhi : canPruneToHi di
            · -- ∂f/∂x_m < 0, fixing x_m = hi decreases f
              -- Similar to above
              have hcoord_m_before : ρ_seq m m = ρ m := by
                simp only [ρ_seq]
                have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
                simp only [dif_neg h1, dif_pos hm]

              have hcoord_m_after : ρ_seq (m + 1) m = B[m].hi := by
                simp only [ρ_seq, hgrad_m, hlo, Bool.false_eq_true, ↓reduceIte, hhi]
                have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
                simp only [dif_pos h2]

              have hρ_seq_m_mem : Box.envMem (ρ_seq m) B := by
                intro ⟨j, hj⟩
                simp only [ρ_seq]
                by_cases h1 : j < m ∧ j < B.length
                · simp only [dif_pos h1]
                  cases hgrad_j : grad[j]? with
                  | none => exact hρB ⟨j, hj⟩
                  | some dj =>
                    simp
                    by_cases hlo_j : canPruneToLo dj
                    · simp only [hlo_j, ↓reduceIte]
                      exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
                    · by_cases hhi_j : canPruneToHi dj
                      · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
                        exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
                      · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
                        exact hρB ⟨j, hj⟩
                · simp only [dif_neg h1, dif_pos hj]
                  exact hρB ⟨j, hj⟩

              have hρ_seq_m_zero : ∀ j, j ≥ B.length → ρ_seq m j = 0 := by
                intro j hjge
                simp only [ρ_seq]
                have h1 : ¬(j < m ∧ j < B.length) := fun h => absurd h.2 (not_lt.mpr hjge)
                simp only [dif_neg h1]
                have h2 : ¬(j < B.length) := not_lt.mpr hjge
                simp only [dif_neg h2]

              have hgrad_di : derivInterval e (Box.toEnv B) m = di := by
                simp only [grad, gradientIntervalN] at hgrad_m
                rw [List.getElem?_map, List.getElem?_range hm] at hgrad_m
                simp only [Option.map_some] at hgrad_m
                exact Option.some.inj hgrad_m

              -- Build the interval environment from the box
              let ρ_int : IntervalEnv := Box.toEnv B

              -- Show ρ_seq m ∈ ρ_int
              have hρ_int : ∀ j, ρ_seq m j ∈ ρ_int j := by
                intro j
                simp only [ρ_int, Box.toEnv, List.getD]
                by_cases hj : j < B.length
                · simp only [List.getElem?_eq_getElem hj, Option.getD]
                  exact hρ_seq_m_mem ⟨j, hj⟩
                · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
                  rw [IntervalRat.mem_default]
                  exact hρ_seq_m_zero j (not_lt.mp hj)

              -- Convert isStrictlyNegative to hi < 0
              have hneg : (derivInterval e ρ_int m).hi < 0 := by
                simp only [ρ_int]
                rw [hgrad_di]
                simp only [isStrictlyNegative, canPruneToHi] at hhi
                exact decide_eq_true_iff.mp hhi

              -- Apply the monotonicity theorem for decreasing functions
              have hmono := decreasing_min_at_right_idx e hsupp (ρ_seq m) ρ_int m hρ_int hneg

              -- ρ_seq m at coord m is in the interval
              have hρ_m_mem : ρ_seq m m ∈ ρ_int m := hρ_int m
              have hmin := hmono (ρ_seq m m) hρ_m_mem

              -- (ρ_int m).hi = B[m].hi
              have hhi_eq : (ρ_int m).hi = B[m].hi := by
                simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem hm, Option.getD]

              -- Rewrite in terms of eval
              simp only [Expr.evalAlong] at hmin
              have hupdate_self : Expr.updateVar (ρ_seq m) m (ρ_seq m m) = ρ_seq m :=
                Expr.updateVar_self (ρ_seq m) m

              -- ρ_seq (m+1) = updateVar (ρ_seq m) m (B[m].hi)
              have hρ_seq_update : ρ_seq (m + 1) = Expr.updateVar (ρ_seq m) m (B[m].hi : ℝ) := by
                funext j
                simp only [Expr.updateVar]
                by_cases hj_eq : j = m
                · subst hj_eq
                  simp only [↓reduceIte]
                  exact hcoord_m_after
                · simp only [if_neg hj_eq]
                  exact (hρ_seq_step m j (Ne.symm hj_eq)).symm

              have hupdate_hi : Expr.updateVar (ρ_seq m) m ((ρ_int m).hi : ℝ) = ρ_seq (m + 1) := by
                rw [hhi_eq, ← hρ_seq_update]
              rw [hupdate_hi, hupdate_self] at hmin
              exact hmin

            · -- No pruning at coord m: ρ_seq (m+1) = ρ_seq m at all coords
              have heq : ∀ j, ρ_seq (m + 1) j = ρ_seq m j := by
                intro j
                by_cases hj_eq : j = m
                · -- When j = m: need ρ_seq (m+1) m = ρ_seq m m
                  simp only [ρ_seq, hgrad_m, hlo, Bool.false_eq_true, ↓reduceIte, hhi, hj_eq]
                  have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
                  have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
                  simp only [dif_neg h1, dif_pos h2, dif_pos hm]
                  -- Both sides are ρ m since we're not pruning
                · exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
              simp only [funext heq]
              exact le_refl _

    -- Compose all steps: f(ρ_seq n) ≤ f(ρ_seq 0) for all n ≤ B.length
    have hchain : ∀ n ≤ B.length, Expr.eval (ρ_seq n) e ≤ Expr.eval (ρ_seq 0) e := by
      intro n hn
      induction n with
      | zero => exact le_refl _
      | succ m ih =>
        have hm_lt : m < B.length := Nat.lt_of_succ_le hn
        calc Expr.eval (ρ_seq (m + 1)) e ≤ Expr.eval (ρ_seq m) e := hstep m hm_lt
          _ ≤ Expr.eval (ρ_seq 0) e := ih (Nat.le_of_lt hm_lt)

    -- ρ_seq B.length = ρ'
    have hfinal_eq : Expr.eval (ρ_seq B.length) e = Expr.eval ρ' e := by
      congr 1; funext j; exact hρ_seq_final j

    -- Prove ρ' ≤ ρ via the chain: ρ' = ρ_seq B.length ≤ ρ_seq 0 = ρ
    have hρ_seq0_eq : Expr.eval (ρ_seq 0) e = Expr.eval ρ e := by
      congr 1
      funext j
      rw [hρ_seq_zero]
      split_ifs with hj
      · rfl
      · exact (hzero j (not_lt.mp hj)).symm

    rw [← hfinal_eq, ← hρ_seq0_eq]
    exact hchain B.length (le_refl _)

end LeanBound.Numerics.Optimization
