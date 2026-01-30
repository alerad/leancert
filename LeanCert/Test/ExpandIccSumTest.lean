/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.ExpandIccSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Tests for expand_Icc_sum tactic

These tests verify that `expand_Icc_sum` correctly expands Finset interval sums
to explicit additions for **any** concrete bounds.

Supported interval types:
- `Icc` (closed-closed): `[a, b]`
- `Ico` (closed-open): `[a, b)`
- `Ioc` (open-closed): `(a, b]`
- `Ioo` (open-open): `(a, b)`
- `Iic` (unbounded below, closed): `[0, b]` for ℕ
- `Iio` (unbounded below, open): `[0, b)` for ℕ

## Key Feature: Fully Automated

Unlike a precomputed lemma library, `expand_Icc_sum` works for ANY concrete
natural number or integer bounds - no need to enumerate cases upfront.
-/

namespace ExpandIccSum.Test

/-! ### Direct simproc tests (intervals without sums)

These tests verify that the Mathlib simprocs work directly on intervals.
-/

section SimprocTests

-- Icc simproc (should work)
example : Finset.Icc 1 3 = {1, 2, 3} := by simp only [Finset.Icc_ofNat_ofNat]

-- Ico simproc (should work)
example : Finset.Ico 1 4 = {1, 2, 3} := by simp only [Finset.Ico_ofNat_ofNat]

-- Ioc simproc (test if it works directly)
example : Finset.Ioc 1 3 = {2, 3} := by simp only [Finset.Ioc_ofNat_ofNat]

-- Test Ioc inside a sum - does simp reach it?
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 1 3, f k = ∑ k ∈ ({2, 3} : Finset ℕ), f k := by
  simp only [Finset.Ioc_ofNat_ofNat]

-- Ioo simproc (test if it works directly)
example : Finset.Ioo 1 4 = {2, 3} := by simp only [Finset.Ioo_ofNat_ofNat]

-- Iic simproc (test if it works directly)
example : Finset.Iic 2 = {0, 1, 2} := by simp only [Finset.Iic_ofNat]

-- Iio simproc (test if it works directly)
example : Finset.Iio 3 = {0, 1, 2} := by simp only [Finset.Iio_ofNat]

end SimprocTests

/-! ### Basic functionality tests -/

section BasicTests

-- Two elements
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 2, f k = f 1 + f 2 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 1, f k = f 0 + f 1 := by expand_Icc_sum

-- Three elements
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 2, f k = f 0 + f 1 + f 2 := by expand_Icc_sum

-- Four elements
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 3 6, f k = f 3 + f 4 + f 5 + f 6 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 3, f k = f 0 + f 1 + f 2 + f 3 := by expand_Icc_sum

-- Single element
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 5 5, f k = f 5 := by expand_Icc_sum

-- Five elements
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 4, f k = f 0 + f 1 + f 2 + f 3 + f 4 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 5, f k = f 1 + f 2 + f 3 + f 4 + f 5 := by expand_Icc_sum

end BasicTests

/-! ### Ico (closed-open) interval tests -/

section IcoTests

-- Ico excludes the upper bound
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 1 3, f k = f 1 + f 2 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 0 4, f k = f 0 + f 1 + f 2 + f 3 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 5 8, f k = f 5 + f 6 + f 7 := by expand_Icc_sum

-- Single element (upper = lower + 1)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 3 4, f k = f 3 := by expand_Icc_sum

-- Empty (upper = lower)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ico 5 5, f k = 0 := by expand_Icc_sum!

end IcoTests

/-! ### Ioc (open-closed) interval tests -/

section IocTests

-- Ioc excludes the lower bound
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 1 3, f k = f 2 + f 3 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 0 4, f k = f 1 + f 2 + f 3 + f 4 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 5 8, f k = f 6 + f 7 + f 8 := by expand_Icc_sum

-- Single element (upper = lower + 1)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 3 4, f k = f 4 := by expand_Icc_sum

-- Empty (upper = lower)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioc 5 5, f k = 0 := by expand_Icc_sum!

end IocTests

/-! ### Ioo (open-open) interval tests -/

section IooTests

-- Ioo excludes both bounds
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 1 4, f k = f 2 + f 3 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 0 5, f k = f 1 + f 2 + f 3 + f 4 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 5 9, f k = f 6 + f 7 + f 8 := by expand_Icc_sum

-- Single element
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 3 5, f k = f 4 := by expand_Icc_sum

-- Empty (upper = lower + 1)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Ioo 5 6, f k = 0 := by expand_Icc_sum!

end IooTests

/-! ### Iic (unbounded below, closed) interval tests -/

section IicTests

-- Iic n = [0, n] for ℕ
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iic 2, f k = f 0 + f 1 + f 2 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iic 4, f k = f 0 + f 1 + f 2 + f 3 + f 4 := by expand_Icc_sum

-- Single element
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iic 0, f k = f 0 := by expand_Icc_sum

end IicTests

/-! ### Iio (unbounded below, open) interval tests -/

section IioTests

-- Iio n = [0, n) for ℕ
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iio 3, f k = f 0 + f 1 + f 2 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iio 5, f k = f 0 + f 1 + f 2 + f 3 + f 4 := by expand_Icc_sum

-- Single element
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iio 1, f k = f 0 := by expand_Icc_sum

-- Empty
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Iio 0, f k = 0 := by expand_Icc_sum!

end IioTests

/-! ### Automation showcase: arbitrary bounds

The key advantage of `expand_Icc_sum` is that it works for ANY concrete bounds,
not just pre-enumerated cases. A lemma library would need separate lemmas for
each range, but this tactic handles them all automatically.
-/

section AutomationShowcase

-- Arbitrary starting points (would require many lemmas in a library approach)
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 7 9, f k = f 7 + f 8 + f 9 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 10 12, f k = f 10 + f 11 + f 12 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 15 17, f k = f 15 + f 16 + f 17 := by expand_Icc_sum
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 20 22, f k = f 20 + f 21 + f 22 := by expand_Icc_sum

-- Larger ranges
example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 0 5, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  expand_Icc_sum

example (f : ℕ → ℝ) : ∑ k ∈ Finset.Icc 1 6, f k = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  expand_Icc_sum

end AutomationShowcase

/-! ### RadiiPolynomial-style tests

These tests mimic the actual use case in Example_7_7_LeanCert_Clean.lean where:
- Sums appear in bound calculations like Z₁_bound
- Named constants and products are involved
- expand_Icc_sum is followed by other simplifications
-/

section RadiiPolynomialStyle

variable (ā : ℕ → ℝ) (ν : ℝ)

-- Pattern from Z₁_bound: ∑ n ∈ Finset.Icc 1 N, |ā n| * ν ^ n
-- With N = 2
example : ∑ n ∈ Finset.Icc 1 2, |ā n| * ν ^ n = |ā 1| * ν ^ 1 + |ā 2| * ν ^ 2 := by
  expand_Icc_sum

-- Pattern from Y₀_tail: ∑ k ∈ Finset.Icc 3 4, f k
-- (when N = 2, the tail sum goes from N+1=3 to 2N=4)
example : ∑ k ∈ Finset.Icc 3 4, |ā k| * ν ^ k = |ā 3| * ν ^ 3 + |ā 4| * ν ^ 4 := by
  expand_Icc_sum

-- Larger coefficient vector (N = 4)
example : ∑ n ∈ Finset.Icc 1 4, |ā n| * ν ^ n =
    |ā 1| * ν ^ 1 + |ā 2| * ν ^ 2 + |ā 3| * ν ^ 3 + |ā 4| * ν ^ 4 := by
  expand_Icc_sum

-- Tail sum for N = 4 (goes from 5 to 8)
example : ∑ k ∈ Finset.Icc 5 8, |ā k| * ν ^ k =
    |ā 5| * ν ^ 5 + |ā 6| * ν ^ 6 + |ā 7| * ν ^ 7 + |ā 8| * ν ^ 8 := by
  expand_Icc_sum

end RadiiPolynomialStyle

/-! ### Combination with other tactics

`expand_Icc_sum` often appears as part of a larger proof, followed by
`ring`, `simp`, or certified bound verification.
-/

section CombinedTactics

variable (a b c : ℝ)

-- Expand then use simp to verify (if needed)
example : ∑ k ∈ Finset.Icc 0 2, (fun n => if n = 0 then a else if n = 1 then b else c) k =
    a + b + c := by
  expand_Icc_sum
  -- expand_Icc_sum + native_decide handles the ite conditions automatically

-- Sum of constants (note: the function type is ℕ → ℝ, not ℝ → ℝ)
example : ∑ k ∈ Finset.Icc 1 3, (fun _ : ℕ => (1 : ℝ)) k = 3 := by
  expand_Icc_sum
  ring

-- Sum with explicit function
example : ∑ k ∈ Finset.Icc 1 4, (fun n : ℕ => (n : ℝ)) k = 10 := by
  expand_Icc_sum
  ring

end CombinedTactics

end ExpandIccSum.Test
