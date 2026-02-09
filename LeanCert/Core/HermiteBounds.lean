/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hermite Polynomial Bounds for Gaussian Derivatives

This file provides bounds on derivatives of exp(-x²) using Hermite polynomials.

## Main Results

* `gaussianSq_iteratedDeriv_bound`: The key bound |d^n/dx^n[exp(-x²)]| ≤ 2 for all n, x.
* `erfInner_iteratedDeriv_bound`: Bound |erfInner^{(n+1)}(x)| ≤ 2.

## Mathematical Background

The n-th derivative of exp(-x²) can be expressed using Hermite polynomials:
  d^n/dx^n[exp(-x²)] = (-√2)^n * H_n(√2 x) * exp(-x²)

where H_n is the probabilist's Hermite polynomial. The product
H_n(y) * exp(-y²/2) is bounded for all y, and this gives us derivative bounds.

## References

* Mathlib's `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian` for exp(-x²/2)
-/

noncomputable section

open Polynomial Real MeasureTheory

namespace LeanCert.Core

/-! ### Basic definitions and properties -/

/-- Our target function exp(-x²). -/
def gaussianSq (x : ℝ) : ℝ := Real.exp (-(x^2))

/-- Bound on |exp(-x²)|. -/
theorem gaussianSq_le_one (x : ℝ) : gaussianSq x ≤ 1 := by
  unfold gaussianSq
  calc Real.exp (-(x^2))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
    _ = 1 := Real.exp_zero

/-- exp(-x²) is positive. -/
theorem gaussianSq_pos (x : ℝ) : 0 < gaussianSq x := by
  unfold gaussianSq; exact Real.exp_pos _

/-- exp(-x²) is nonnegative. -/
theorem gaussianSq_nonneg (x : ℝ) : 0 ≤ gaussianSq x := le_of_lt (gaussianSq_pos x)

/-!
This file currently contains only elementary properties of `exp (-x^2)`.
Previous placeholder axioms for high-order derivative bounds and erf Taylor
coefficients were removed in favor of fully proved, conservative enclosures
in the interval-evaluation layer.
-/

end LeanCert.Core
