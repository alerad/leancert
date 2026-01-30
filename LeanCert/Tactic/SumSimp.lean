/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Simproc.FinsetInterval

/-!
# sum_simp: Expand Finset interval sums to explicit additions

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

This file provides the `sum_simp` tactic that **automatically** expands
`∑ k ∈ Finset.Icc a b, f k` to `f a + f (a+1) + ... + f b` for **any** concrete bounds.

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
1. **Mathlib's `Icc_ofNat_ofNat` simproc** (from `Mathlib.Tactic.Simproc.FinsetInterval`)
   - Computes `Finset.Icc a b` to explicit `{a, a+1, ..., b}` form
2. **`Finset.sum_insert`** with `native_decide` for membership proofs
   - Peels off elements: `∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`
3. **`Finset.sum_singleton`** as base case
   - `∑ x ∈ {a}, f x = f a`

## Main definitions

* `sum_simp` - tactic that expands Finset interval sums to explicit additions
* `sum_simp!` - extended version with additional normalization
-/

namespace SumSimp

/-- Sum over a two-element set (helper lemma, not strictly needed but useful) -/
@[simp]
lemma sum_pair_insert {α : Type*} [AddCommMonoid α] {a b : ℕ} (f : ℕ → α) (h : a ≠ b) :
    ∑ x ∈ ({a, b} : Finset ℕ), f x = f a + f b := by
  rw [Finset.sum_insert (Finset.notMem_singleton.mpr h), Finset.sum_singleton]

end SumSimp

/-- Tactic that expands finite interval sums to explicit additions.

Supports all Finset interval types:
- `Icc a b` (closed-closed): `[a, b]`
- `Ico a b` (closed-open): `[a, b)`
- `Ioc a b` (open-closed): `(a, b]`
- `Ioo a b` (open-open): `(a, b)`
- `Iic b` (unbounded below, closed): `[0, b]` for ℕ
- `Iio b` (unbounded below, open): `[0, b)` for ℕ

**Fully automated** - works for any concrete natural number or integer bounds.

## Algorithm
1. Convert interval to explicit set using Mathlib's simprocs
2. Repeatedly apply `Finset.sum_insert` with `native_decide` proving membership
3. Terminate with `Finset.sum_singleton` or `rfl`

## Example
```lean
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by
  sum_simp

example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 1 4, f k = f 1 + f 2 + f 3 := by
  sum_simp

example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iic 2, f k = f 0 + f 1 + f 2 := by
  sum_simp
```
-/
macro "sum_simp" : tactic =>
  `(tactic| (
    -- Step 1: Use Mathlib's simprocs to compute Finset intervals to explicit sets
    simp only [Finset.Icc_ofNat_ofNat, Finset.Ico_ofNat_ofNat,
               Finset.Ioc_ofNat_ofNat, Finset.Ioo_ofNat_ofNat,
               Finset.Iic_ofNat, Finset.Iio_ofNat]
    -- Step 2: Repeatedly expand using sum_insert with native_decide for membership
    repeat (first
      | rfl
      | simp only [Finset.sum_singleton]
      | (rw [Finset.sum_insert (by native_decide)]; try simp only [add_assoc]))
  ))

/-- Extended version that also handles empty sums and additional normalization.

Use this when the sum might be empty (b < a) or when you need `add_zero`/`zero_add`
simplifications.
-/
macro "sum_simp!" : tactic =>
  `(tactic| (
    simp only [Finset.Icc_ofNat_ofNat, Finset.Ico_ofNat_ofNat,
               Finset.Ioc_ofNat_ofNat, Finset.Ioo_ofNat_ofNat,
               Finset.Iic_ofNat, Finset.Iio_ofNat]
    repeat (first
      | rfl
      | simp only [Finset.sum_singleton]
      | simp only [Finset.sum_empty]
      | (rw [Finset.sum_insert (by native_decide)]; try simp only [add_assoc]))
    try simp only [add_zero, zero_add]
  ))
