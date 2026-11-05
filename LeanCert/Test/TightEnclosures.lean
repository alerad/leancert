/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic
import LeanCert.Core.IntervalRat.Arctan
import LeanCert.Core.IntervalRat.Derived

/-!
# Regression tests: tight enclosures for atan, tanh, sinc, arsinh, erf

These functions previously evaluated to global bounds (`atan ∈ [-2, 2]`,
`tanh, sinc ∈ [-1, 1]`, and in the Dyadic backend `erf ∈ [-1, 1]`;
`arsinh ∈ [-(|x|+1), |x|+1]`). Every goal below is false for those bounds'
endpoints, so it can only be certified through the tight enclosures.
-/

namespace LeanCert.Test.TightEnclosures

open LeanCert.Core

/-! ### Enclosure-level checks (pure computation, kernel-decidable) -/

/-- `π/4` via Machin's formula, to better than `10⁻¹²` at 10 terms. -/
example : (IntervalRat.piQuarterComputable 10).hi - (IntervalRat.piQuarterComputable 10).lo
    < 1 / 10 ^ 12 := by decide +kernel

example : (IntervalRat.arctanPoint 1 10).lo < 7854 / 10000 ∧
    7853 / 10000 < (IntervalRat.arctanPoint 1 10).lo := by decide +kernel

/-! ### Tactic-level goals -/

-- atan: point bounds (π/4 = arctan 1 ≈ 0.785398)
example : Real.arctan 1 < 7854 / 10000 := by leancert
example : 7853 / 10000 < Real.arctan 1 := by leancert
example : Real.arctan 100 < 1561 / 1000 := by leancert
example : Real.arctan 1 < 7854 / 10000 := by leancert (trust := kernel)

-- atan: quantified bound on a box (true max is arctan 1 ≈ 0.7854)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.arctan x ≤ 79 / 100 := by leancert

-- tanh (tanh 1 ≈ 0.761594)
example : Real.tanh 1 < 7616 / 10000 := by leancert
example : 7615 / 10000 < Real.tanh 1 := by leancert
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, Real.tanh x ≤ 97 / 100 := by leancert

-- tanh on huge arguments stays cheap (endpoints are clamped before exp)
example : 99 / 100 < Real.tanh 1000000 := by leancert

-- sinc (sinc 1 = sin 1 ≈ 0.841471, sinc 2 ≈ 0.454649)
example : Real.sinc 1 < 8415 / 10000 := by leancert
example : Real.sinc 2 < 46 / 100 := by leancert
example : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), 95 / 100 ≤ Real.sinc x := by leancert

-- arsinh (arsinh 3 ≈ 1.818446)
example : Real.arsinh 3 < 1819 / 1000 := by leancert
example : 1818 / 1000 < Real.arsinh 3 := by leancert

-- erf (erf 1 ≈ 0.842701), previously [-1, 1] in the Dyadic backend
example : Real.erf 1 < 8428 / 10000 := by leancert

/-! ### Trust audit -/

theorem arctan_one_lt : Real.arctan 1 < 7854 / 10000 := by leancert (trust := kernel)

/-- info: 'LeanCert.Test.TightEnclosures.arctan_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctan_one_lt

end LeanCert.Test.TightEnclosures
