/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.FinSumExpand
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Tests for finsum_expand tactic

Verifies that `finsum_expand` expands Finset sums to explicit additions.

Supports:
- **Intervals**: `Icc`, `Ico`, `Ioc`, `Ioo`, `Iic`, `Iio`
- **Explicit sets**: `{a, b, c, ...}`
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

/-! ### Arbitrary bounds (automation showcase) -/

example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 10 12, f k = f 10 + f 11 + f 12 := by finsum_expand
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 5, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  finsum_expand

/-! ### Power series patterns -/

variable (a : ℕ → ℝ) (r : ℝ)

example : ∑ n ∈ Finset.Icc 1 3, |a n| * r ^ n =
    |a 1| * r ^ 1 + |a 2| * r ^ 2 + |a 3| * r ^ 3 := by finsum_expand

/-! ### Combination with other tactics -/

example : ∑ k ∈ Finset.Icc 1 3, (fun _ : ℕ => (1 : ℝ)) k = 3 := by finsum_expand; ring
example : ∑ k ∈ Finset.Icc 1 4, (fun n : ℕ => (n : ℝ)) k = 10 := by finsum_expand; ring

end FinSumExpand.Test
