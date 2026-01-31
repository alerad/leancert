/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Simproc.FinsetInterval

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

This file provides the `finsum_expand` tactic that **automatically** expands
finite sums over any concrete finset to explicit additions.

Supports:
- **Interval finsets**: `Icc`, `Ico`, `Ioc`, `Ioo`, `Iic`, `Iio`
- **Explicit finsets**: `{a, b, c, ...}`

## Design Journey & Failed Approaches

### Attempt 1: dsimproc (Failed)
We first tried a `dsimproc` approach similar to `vec_simp`:
```lean
dsimproc sumIccExpand (Finset.sum (Finset.Icc _ _) _) := fun e => do
  -- Extract bounds, build explicit sum expression
  return .done result
```
**Why it failed:** `dsimproc` only works for *definitional* equality. But
`∑ k ∈ Finset.Icc 1 2, f k` is NOT definitionally equal to `f 1 + f 2` -
they are only *propositionally* equal (require a proof). Unlike vector
indexing (which reduces definitionally), Finset sums are defined inductively.

### Attempt 2: Precomputed Lemma Library (Worked but limited)
We then tried precomputing lemmas for common ranges:
```lean
lemma sum_Icc_1_2 ... := by native_decide; simp [sum_insert, sum_singleton]
lemma sum_Icc_0_3 ... := by native_decide; simp [sum_insert, sum_singleton]
-- etc.
```
**Why it's suboptimal:** Requires enumerating all needed ranges upfront.
Not truly automated - fails for ranges not in the library.

### Attempt 3: simp with (by decide) hypothesis (Failed)
```lean
simp only [Finset.sum_insert (by decide), Finset.sum_singleton]
```
**Why it failed:** `decide` tries to prove membership before simp knows
the concrete finset, resulting in "type contains metavariables" errors.

### Final Design: Mathlib simproc + repeat/native_decide (Works!)
The key insight: use Mathlib's existing `Icc_ofNat_ofNat` simproc first,
then use `repeat` with `rw [Finset.sum_insert (by native_decide)]`.

**Why it works:**
1. The simproc converts `Finset.Icc 1 3` → `{1, 2, 3}` (concrete set)
2. Now `native_decide` can prove `1 ∉ {2, 3}` because the set is concrete
3. `repeat` peels off one element at a time until we reach `sum_singleton`

## Implementation

The tactic leverages:
1. **Mathlib's interval simprocs** (from `Mathlib.Tactic.Simproc.FinsetInterval`)
   - Computes `Finset.Icc a b` to explicit `{a, a+1, ..., b}` form
2. **`Finset.sum_insert`** with `native_decide` for membership proofs
   - Peels off elements: `∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`
3. **`Finset.sum_singleton`** as base case
   - `∑ x ∈ {a}, f x = f a`

## Main definitions

* `finsum_expand` - tactic that expands Finset sums to explicit additions
-/

namespace FinSumExpand

/-- Sum over a two-element set (helper lemma, not strictly needed but useful) -/
@[simp]
lemma sum_pair_insert {α : Type*} [AddCommMonoid α] {a b : ℕ} (f : ℕ → α) (h : a ≠ b) :
    ∑ x ∈ ({a, b} : Finset ℕ), f x = f a + f b := by
  rw [Finset.sum_insert (Finset.notMem_singleton.mpr h), Finset.sum_singleton]

end FinSumExpand

/-- Tactic that expands finite sums to explicit additions.

Supports:
- **Interval finsets**: `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Iic b`, `Iio b`
- **Explicit finsets**: `{a, b, c, ...}`

**Fully automated** - works for any concrete natural number or integer bounds.

## Algorithm
1. Convert intervals to explicit sets using Mathlib's simprocs
2. Repeatedly apply `Finset.sum_insert` with `native_decide` proving membership
3. Terminate with `Finset.sum_singleton` or `rfl` (empty sums reduce definitionally)

## Example
```lean
-- Interval sums
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by
  finsum_expand

-- Explicit finsets
example (f : ℕ → ℝ) : ∑ k ∈ ({1, 3, 7} : Finset ℕ), f k = f 1 + f 3 + f 7 := by
  finsum_expand

-- Empty sums
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 5 6, f k = 0 := by
  finsum_expand
```
-/
macro "finsum_expand" : tactic =>
  `(tactic| (
    -- Step 1: Use Mathlib's simprocs to compute Finset intervals to explicit sets
    -- (wrapped in try since it won't apply to explicit finsets)
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
