/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.FinSumExpand
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Tests for finsum_expand tactics

Tests for `finsum_expand` and `finsum_expand!`.

- `finsum_expand` - expands Finset sums to explicit additions
- `finsum_expand!` - also simplifies `dite` conditions and absolute values

Supports intervals, explicit sets, and Fin sums.
-/

namespace FinSumExpand.Test

/-! ### Explicit finsets (non-interval) -/

example (f : ℕ → ℝ) : ∑ k ∈ ({1, 3, 7} : Finset ℕ), f k = f 1 + f 3 + f 7 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ ({5} : Finset ℕ), f k = f 5 := by finsum_expand

/-! ### Interval types -/

-- Icc (closed-closed)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 5 5, f k = f 5 := by finsum_expand  -- single element

-- Ico (closed-open)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 1 4, f k = f 1 + f 2 + f 3 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 5 5, f k = 0 := by finsum_expand  -- empty

-- Ioc (open-closed)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 1 3, f k = f 2 + f 3 := by finsum_expand

-- Ioo (open-open)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 1 4, f k = f 2 + f 3 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 5 6, f k = 0 := by finsum_expand  -- empty

-- Iic (unbounded below, closed) - for ℕ, means [0, n]
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iic 2, f k = f 0 + f 1 + f 2 := by finsum_expand

-- Iio (unbounded below, open) - for ℕ, means [0, n)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iio 3, f k = f 0 + f 1 + f 2 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iio 0, f k = 0 := by finsum_expand  -- empty

/-! ### Arbitrary bounds -/

example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 10 12, f k = f 10 + f 11 + f 12 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 5, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  finsum_expand

/-! ### Power series patterns -/

section PowerSeries
variable (a : ℕ → ℝ) (r : ℝ)

example : ∑ n ∈ Finset.Icc 1 3, |a n| * r ^ n =
    |a 1| * r ^ 1 + |a 2| * r ^ 2 + |a 3| * r ^ 3 := by finsum_expand
end PowerSeries

/-! ### Combination with other tactics -/

example : ∑ k ∈ Finset.Icc 1 3, (fun _ : ℕ => (1 : ℝ)) k = 3 := by finsum_expand; ring
example : ∑ k ∈ Finset.Icc 1 4, (fun n : ℕ => (n : ℝ)) k = 10 := by finsum_expand; ring

/-! ### Fin sums -/

-- Small Fin
example (f : Fin 3 → ℝ) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by finsum_expand

-- Larger Fin
example (f : Fin 10 → ℝ) : ∑ i : Fin 10, f i =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by finsum_expand

-- With vector notation
example (a b c : ℝ) : ∑ i : Fin 3, (![a, b, c] : Fin 3 → ℝ) i = a + b + c := by finsum_expand

/-! ### finsum_expand! (with dite, abs, and non-literal Fin fallback) -/

-- dite conditions are simplified
example (f : ℕ → ℝ) : ∑ x ∈ Finset.Icc 1 2, (if _ : x ≤ 2 then f x else 0) =
    f 1 + f 2 := by finsum_expand!

-- finsum_expand! with abs in summands
example : ∑ k ∈ Finset.Icc 1 2, |(k : ℤ)| = 1 + 2 := by finsum_expand!

-- Non-literal Fin dimensions (fallback via Fin.sum_univ_succ)
-- When n is not a syntactic literal, finsum_expand! uses the fallback
example (f : Fin (2 + 1) → ℝ) : ∑ i : Fin (2 + 1), f i =
    f 0 + f 1 + f 2 := by finsum_expand!

example (f : Fin (1 + 2) → ℝ) : ∑ i : Fin (1 + 2), f i =
    f 0 + f 1 + f 2 := by finsum_expand!

/-! ### Matrix column sums -/

-- finsum_expand! handles matrix indexing including lambda tails from column extraction
open Matrix in
def testMatrix : Fin 3 → Fin 3 → ℚ := ![![1, 2, 3], ![-4, 5, 6], ![7, -8, 9]]

-- Sum of column 0 elements
example : ∑ i : Fin 3, testMatrix i 0 = 1 + (-4) + 7 := by finsum_expand!

-- Sum of column 0 with absolute values
example : ∑ i : Fin 3, |testMatrix i 0| = 1 + 4 + 7 := by finsum_expand!

-- Sum of column 1 with absolute values
example : ∑ i : Fin 3, |testMatrix i 1| = 2 + 5 + 8 := by finsum_expand!

/-! ### 2D matrix indexing (nested vector access) -/

-- finsum_expand! handles nested vector indexing like ![![...], ![...]] i j
-- This tests the Mathlib fallback lemmas (cons_val_zero, cons_val_one, head_cons)
example : ∑ i : Fin 2, ![![(1 : ℚ), 2], ![3, 4]] i 0 = 1 + 3 := by finsum_expand!
example : ∑ i : Fin 2, ![![(1 : ℚ), 2], ![3, 4]] i 1 = 2 + 4 := by finsum_expand!

-- With absolute values
example : ∑ i : Fin 2, |![![(1 : ℚ), -2], ![-3, 4]] i 0| = 1 + 3 := by finsum_expand!
example : ∑ i : Fin 2, |![![(1 : ℚ), -2], ![-3, 4]] i 1| = 2 + 4 := by finsum_expand!

-- Sum over both indices
example : ∑ i : Fin 2, ∑ j : Fin 2, ![![(1 : ℚ), 2], ![3, 4]] i j = 1 + 2 + 3 + 4 := by
  finsum_expand!

-- Nested vecCons after lambda reduction: handles cases where lambda application
-- returns another vecCons that still needs element extraction
example : ∑ i : Fin 3, (Matrix.vecCons (10 : ℚ)
    (fun j => Matrix.vecCons (20 : ℚ) (fun _ => 30) j) : Fin 3 → ℚ) i = 10 + 20 + 30 := by
  finsum_expand!

/-! ### Inferred dimension (metavariable reduction)

When the outer expression has a type annotation but inner lambdas don't have explicit
binder types, `nExpr` (the dimension in `Fin n`) may be `Nat.succ ?m` rather than a
raw literal. We must `reduce nExpr` before calling `nat?` to convert it to a concrete
literal. This is the same fix applied in VecSimp.
-/

-- Type annotation on outer expression, but lambda binders are implicit
-- The fix ensures getVecElem reduces nExpr before nat? check
example : ∑ i : Fin 3, (Matrix.vecCons (1 : ℚ)
    (fun j => Matrix.vecCons (2 : ℚ) (fun _ => 3) j) : Fin 3 → ℚ) i = 1 + 2 + 3 := by
  finsum_expand!

end FinSumExpand.Test
