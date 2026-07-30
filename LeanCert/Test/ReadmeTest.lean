import LeanCert.Tactic

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

/-!
# README headline examples

This is a fast, explicit regression target for the four flagship README
theorems. `scripts/check_docs_snippets.py` separately extracts and compiles
every Lean fence from the README itself, preventing the copies from drifting.
-/

example : Real.log 2 < 7 / 10 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x * Real.cos x ≤ 3 := by
  leancert

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  leancert

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert

example : Real.log 2 < 7 / 10 := by
  leancert (trust := kernel)
