/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Natural-Syntax Hardening Tests

Regression coverage for bridges between ordinary Lean expressions and the
reflected expressions checked by LeanCert.
-/

open LeanCert

set_option linter.unnecessarySimpa false

def shiftedSquare (x : ℝ) : ℝ := (x - 1) ^ 2

example : ∀ x ∈ Set.Icc (0 : ℝ) 2, shiftedSquare x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + 1 ≠ 0 := by
  root_bound

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  interval_roots

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, 2 = x ^ 2 := by
  interval_roots

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 = 2 := by
  interval_unique_root

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ 2 = x ^ 2 := by
  interval_unique_root

def wrappedSquare (x : ℝ) : ℝ := x ^ 2

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, wrappedSquare x = 2 := by
  interval_roots

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ wrappedSquare x = 2 := by
  interval_unique_root

example : ∃ x ∈ Set.Icc (0 : ℝ) 2, x + 1 = 2 * x := by
  interval_roots

example : ∃ x ∈ Set.Icc (0 : ℝ) 2, 0 = x - 1 := by
  interval_roots

example : ∃! x, x ∈ Set.Icc (0 : ℝ) 2 ∧ 0 = x - 1 := by
  interval_unique_root
