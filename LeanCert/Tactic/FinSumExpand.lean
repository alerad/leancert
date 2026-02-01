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
- **Interval finsets**: `Icc`, `Ico`, `Ioc`, `Ioo`, `Iic`, `Iio` (fully automated)
- **Explicit finsets**: `{a, b, c, ...}` (fully automated)
- **Fin sums**: `∑ i : Fin n, f i` for any literal n (uses Mathlib's simproc)

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

This is **truly automated** - works for any concrete literal n, not limited to n ≤ 8.

## Main definitions

* `finsum_expand` - tactic that expands Finset sums to explicit additions
-/

namespace FinSumExpand

-- This namespace is kept for potential future extensions.
-- The main automation comes from Mathlib's `Fin.sum_univ_ofNat` simproc.

end FinSumExpand

/-- Tactic that expands finite sums to explicit additions.

Supports:
- **Interval finsets**: `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b`, `Iic b`, `Iio b`
- **Explicit finsets**: `{a, b, c, ...}`
- **Fin sums**: `∑ i : Fin n, f i` for any literal `n` (truly automated)

**Fully automated** - works for any concrete natural number bounds.

## Algorithm
1. Expand `Finset.univ : Finset (Fin n)` using custom simproc `finUnivExpand`
2. Convert intervals to explicit sets using Mathlib's simprocs
3. Repeatedly apply `Finset.sum_insert` with `native_decide` proving membership
4. Terminate with `Finset.sum_singleton` or `rfl` (empty sums reduce definitionally)

## Example
```lean
-- Interval sums
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by
  finsum_expand

-- Fin sums (works for any n, not just n ≤ 8)
example (f : Fin 10 → ℝ) : ∑ i : Fin 10, f i = f 0 + f 1 + ... + f 9 := by
  finsum_expand

-- Empty sums
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 5 6, f k = 0 := by
  finsum_expand
```
-/
macro "finsum_expand" : tactic =>
  `(tactic| (
    -- Step 0: Expand Fin sums using Mathlib's simproc (works for any n)
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
