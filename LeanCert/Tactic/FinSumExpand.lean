/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecUtil
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Simproc.FinsetInterval
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# finsum_expand: Expand Finset sums to explicit additions

## Tactics

* `finsum_expand` - expand `∑ k ∈ Finset.Icc 1 3, f k` → `f 1 + f 2 + f 3`
* `finsum_expand!` - + computed bounds (`2*2`), non-literal Fin, dite, abs, matrix indexing

## Supported

- Intervals: `Icc`, `Ico`, `Ioc`, `Ioo`, `Iic`, `Iio`
- Explicit finsets: `{a, b, c}`
- Fin sums: `∑ i : Fin n, f i` (literal n via `Fin.sum_univ_ofNat`, else `Fin.sum_univ_succ`)

Shared utilities in `LeanCert.Tactic.VecUtil`. Debug: `set_option trace.VecUtil.debug true`
-/

/-- Expand finite sums: `∑ k ∈ Finset.Icc 1 3, f k` → `f 1 + f 2 + f 3`.
    Supports intervals (`Icc`, `Ico`, etc.), explicit finsets, and `∑ i : Fin n, f i`.
    See `finsum_expand!` for computed bounds, dite, abs, matrix indexing. -/
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

/-- `finsum_expand` + computed bounds (`Nat.reduceAdd/Mul/Sub`), non-literal Fin
    (`Fin.sum_univ_succ`), dite, matrix indexing (`VecUtil.vecConsFinMk`), abs. -/
macro "finsum_expand!" : tactic =>
  `(tactic| (
    -- Step 0: Normalize arithmetic in interval bounds
    -- E.g., Finset.Icc 3 (2 * 2) → Finset.Icc 3 4
    try simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
    -- Now run standard finsum_expand with literal bounds
    finsum_expand
    -- Fallback for non-literal Fin n (e.g., Fin (2 + 1))
    -- Repeatedly expand using Fin.sum_univ_succ until we hit Fin 0
    repeat rw [Fin.sum_univ_succ]
    -- Simplify Fin expressions and handle empty Fin 0 sum
    try simp only [Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero,
                   Fin.castSucc_zero, Fin.zero_eta, add_assoc]
    -- Normalize nested Fin.succ
    try simp only [Fin.succ_one_eq_two]
    -- Vector/matrix indexing + dite + abs with fixed-point iteration
    -- Must use vec_index_simp_with_dite (not vec_index_simp_core) so abs lemmas are
    -- in the same simp call, allowing simp to descend into |vecCons ...| and reduce
    vec_index_simp_with_dite
  ))
