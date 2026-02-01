/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Simproc.FinsetInterval
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.VecNotation

/-!
# finsum_expand: Expand Finset sums to explicit additions

## Problem

When proving bounds involving finite sums like `∑ k ∈ Finset.Icc 1 2, f k`,
we often need to expand them to `f 1 + f 2` for arithmetic simplification.

Mathlib doesn't provide a general tactic for this, so projects typically
define "bridge lemmas" manually for each specific range:
```lean
lemma sum_Icc_1_2 (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 2, f k = f 1 + f 2 := by
  have h : Finset.Icc 1 2 = {1, 2} := by native_decide
  rw [h, Finset.sum_insert (by simp), Finset.sum_singleton]
```

This is tedious and error-prone.

## Solution

This file provides two tactics:
- `finsum_expand` - expands finite sums over concrete finsets to explicit additions
- `finsum_expand!` - also simplifies `dite` conditions and absolute values

Supports:
- **Interval finsets**: `Icc`, `Ico`, `Ioc`, `Ioo`, `Iic`, `Iio`
- **Explicit finsets**: `{a, b, c, ...}`
- **Fin sums**: `∑ i : Fin n, f i` for any literal n (uses Mathlib's simproc)

The `!` variant is useful when summands contain:
- `dite` expressions: `if h : x ≤ 2 then f x else 0` → `f x`
- Absolute values of positive literals: `|4321/432|` → `4321/432`

## Design Notes

### Interval sums: simproc + repeat pattern
For interval finsets, we use Mathlib's existing simprocs to convert intervals
to explicit sets, then repeatedly apply `Finset.sum_insert`.

### Fin sums: Mathlib's `Fin.sum_univ_ofNat` simproc
For `∑ i : Fin n, f i`, we use Mathlib's `Fin.sum_univ_ofNat` simproc from
`Mathlib.Data.Fin.Tuple.Reflection`. This simproc:
1. Pattern-matches on `∑ _ : Fin n, _`
2. Extracts `n` as a literal using `n.nat?`
3. Builds the expanded form `f 0 + f 1 + ... + f (n-1)` via `mkSumEqQ`
4. Returns the proof using `FinVec.sum_eq`

Works for any concrete literal n.

### Fallback for non-literal Fin dimensions
When n is not a syntactic literal (e.g., `Fin (2 + 1)` instead of `Fin 3`),
`n.nat?` returns `none` and the simproc doesn't fire. We fall back to
repeatedly applying `Fin.sum_univ_succ` to expand element by element.

## Main definitions

* `finsum_expand` - tactic that expands Finset sums to explicit additions
* `finsum_expand!` - aggressive variant that also simplifies `dite` conditions
-/

namespace FinSumExpand

open Lean Meta

/-- Extract natural number from a Fin expression.
    Handles both `Fin.mk n proof` and numeric literals like `(2 : Fin 3)`. -/
def getFinVal? (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnfR e
  if e'.getAppFn.constName? == some ``Fin.mk then
    let args := e'.getAppArgs
    if args.size == 3 then
      let val ← whnfR args[1]!
      if let some n := val.nat? then
        return some n
  try
    let finVal ← mkAppM ``Fin.val #[e]
    let finValReduced ← reduce finVal
    return finValReduced.nat?
  catch _ =>
    return none

/-- Recursively traverse a vecCons chain to extract the element at index `idx`.
    Handles explicit vecCons chains, lambda tails from matrix column extraction,
    and nested vecCons after lambda reduction.

    Uses `inferType` for lambda domain to handle implicit binder types.
    Uses `instantiateMVars` + `reduce` before `nat?` to handle metavariables. -/
partial def getVecElem (idx : Nat) (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfR e
  let args := e.getAppArgs
  if e.getAppFn.constName? == some ``Matrix.vecCons && args.size >= 4 then
    let head := args[2]!
    let tail := args[3]!
    if idx == 0 then
      return some head
    else
      getVecElem (idx - 1) tail
  else if e.isLambda then
    -- Get the Fin type from the lambda's inferred type (more robust than bindingDomain!)
    let lamType ← inferType e
    let lamType' ← whnfR lamType
    -- Instantiate metavariables that may have been assigned during elaboration
    let lamType'' ← instantiateMVars lamType'
    if !lamType''.isForall then return none
    let domain := lamType''.bindingDomain!
    let finType ← whnfR domain
    if finType.isAppOf ``Fin then
      let finArgs := finType.getAppArgs
      if finArgs.size >= 1 then
        let nExpr := finArgs[0]!
        let nExprReduced ← reduce nExpr
        let some _ := nExprReduced.nat? | return none
        let idxExpr := mkNatLit idx
        let proof ← mkDecideProof (← mkAppM ``LT.lt #[idxExpr, nExprReduced])
        let finIdx ← mkAppM ``Fin.mk #[idxExpr, proof]
        let applied := Expr.app e finIdx
        let reduced ← reduce applied
        -- Recursively process - handles nested vecCons after lambda application
        let reduced' ← whnfR reduced
        if reduced'.getAppFn.constName? == some ``Matrix.vecCons && reduced'.getAppArgs.size == 5 then
          -- Result is vecCons applied to an index - extract via recursive getVecElem
          let rargs := reduced'.getAppArgs
          let ridxExpr := rargs[4]!
          let some remainingIdx ← getFinVal? ridxExpr | return some reduced
          return ← getVecElem remainingIdx reduced'
        else
          return some reduced
    return none
  else
    return none

/-- Simproc: Reduce `![a, b, c, ...] i` to the i-th element.
    Handles numeric literals, Fin.mk, and lambda tails from matrix column extraction. -/
dsimproc vecConsFinMk (Matrix.vecCons _ _ _) := fun e => do
  let e ← whnfR e
  let args := e.getAppArgs
  if e.getAppFn.constName? != some ``Matrix.vecCons || args.size != 5 then
    return .continue
  let x := args[2]!
  let xs := args[3]!
  let ei := args[4]!
  let ei' ← whnfR ei
  let i : Nat ← match ei'.int? with
    | some n => pure n.toNat
    | none =>
      let some n ← getFinVal? ei | return .continue
      pure n
  if i == 0 then
    return .done x
  else
    let some result ← getVecElem (i - 1) xs | return .continue
    return .done result

end FinSumExpand

/-- Tactic that expands finite sums to explicit additions.

Supports:
- **Interval finsets**: `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Iic b`, `Iio b`
- **Explicit finsets**: `{a, b, c, ...}`
- **Fin sums**: `∑ i : Fin n, f i` for any literal `n`

Works for any concrete natural number bounds. See also `finsum_expand!` which
additionally simplifies `dite` conditions and handles non-literal Fin dimensions.

## Algorithm
1. Expand `∑ i : Fin n, f i` using Mathlib's `Fin.sum_univ_ofNat` simproc
2. Convert intervals to explicit sets using Mathlib's simprocs
3. Repeatedly apply `Finset.sum_insert` with `native_decide` proving membership
4. Terminate with `Finset.sum_singleton` or `rfl` (empty sums reduce definitionally)

## Example
```lean
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by
  finsum_expand

example (f : Fin 3 → ℝ) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  finsum_expand
```
-/
macro "finsum_expand" : tactic =>
  `(tactic| (
    -- Step 0: Expand Fin sums using Mathlib's simproc (works for literal n)
    try simp only [Fin.sum_univ_ofNat]
    -- Step 1: Use Mathlib's simprocs to compute Finset intervals to explicit sets
    try simp only [Finset.Icc_ofNat_ofNat, Finset.Ico_ofNat_ofNat,
                   Finset.Ioc_ofNat_ofNat, Finset.Ioo_ofNat_ofNat,
                   Finset.Iic_ofNat, Finset.Iio_ofNat]
    -- Step 2: Repeatedly peel off elements until singleton or empty
    -- Note: ∑ k ∈ ∅, f k = 0 definitionally, so rfl handles empty sums
    repeat (first
      | rfl
      | simp only [Finset.sum_singleton]
      | (rw [Finset.sum_insert (by native_decide)]; try simp only [add_assoc]))
  ))

/-- Aggressive variant of `finsum_expand` that also simplifies `dite` conditions,
absolute values, matrix indexing, and handles non-literal Fin dimensions.

After expanding the sum:
- Simplifies `if h : 1 ≤ 2 then f x else 0` to `f x`
- Simplifies `|4321/432|` to `4321/432` when the argument is provably positive/nonnegative
- Simplifies matrix indexing including nested 2D access like `![![1,2],[3,4]] i j`
- Handles lambda tails from column extraction
- Handles `∑ i : Fin (n + 1), f i` via `Fin.sum_univ_succ` fallback

Uses `repeat simp` for vector indexing to handle any nesting depth.

## Example
```lean
-- dite simplification:
-- ∑ x ∈ Finset.Icc 1 2, (if _ : x ≤ 2 then f x else 0) → f 1 + f 2

-- Non-literal Fin dimension:
-- ∑ i : Fin (2 + 1), f i → f 0 + f 1 + f 2

-- Matrix column sums:
-- ∑ i : Fin 3, |M i 0| → fully simplified to concrete values

-- Nested 2D sums:
-- ∑ i : Fin 2, ∑ j : Fin 2, ![![1,2],[3,4]] i j → 1 + 2 + 3 + 4
```
-/
macro "finsum_expand!" : tactic =>
  `(tactic| (
    finsum_expand
    -- Fallback for non-literal Fin n (e.g., Fin (2 + 1))
    -- Repeatedly expand using Fin.sum_univ_succ until we hit Fin 0
    repeat rw [Fin.sum_univ_succ]
    -- Simplify Fin expressions and handle empty Fin 0 sum
    try simp only [Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero,
                   Fin.castSucc_zero, Fin.zero_eta, add_assoc]
    -- Normalize nested Fin.succ
    try simp only [Fin.succ_one_eq_two]
    -- Simplify dite conditions with decidable literal bounds
    try simp (config := { decide := true }) only [dite_true, dite_false]
    -- Simplify matrix/vector indexing (handles lambda tails from column extraction)
    -- Matrix.of_apply: unwraps !![...] notation: (Matrix.of f) i j → f i j
    try simp only [Matrix.of_apply]
    -- Nested indexing (![![...]] i j) requires multiple reduction passes:
    --   Pass 1: ![![1,2],[3,4]] 0 → ![1,2]
    --   Pass 2: ![1,2] 0 → 1
    -- Each pass reduces one level of vecCons application
    repeat simp only [FinSumExpand.vecConsFinMk,
                      Matrix.cons_val_zero, Matrix.cons_val_zero',
                      Matrix.cons_val_one, Matrix.head_cons]
    -- Simplify absolute values of positive/nonnegative literals
    try simp only [abs_of_pos, abs_of_nonneg]
  ))
