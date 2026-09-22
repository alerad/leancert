/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Bernstein polynomial bound tests

Univariate polynomial interval bounds through the public `leancert` front door
and the dedicated `bernstein_bound` tactic, plus the engine-level certificate on
a degree-134 polynomial.
-/

open Set
open LeanCert.Core LeanCert.Engine

set_option linter.unusedTactic false

/-- The degree-18 running-integral certificate polynomial from
`rnt-paper` Remark 2.4: positive on `[0,1]` with minimum `34619/4476780 ≈ 0.0077`
at `c = 1`. Horner interval arithmetic encloses it in roughly `[-0.6, 1.1]`. -/
noncomputable def Qt (c : ℝ) : ℝ :=
  1 / 2 - c / 3 - c ^ 2 / 4 - c ^ 3 / 5 + c ^ 6 / 8 + c ^ 7 / 9 + c ^ 8 / 10
    + c ^ 9 / 11 + c ^ 10 / 12 - c ^ 12 / 14 - c ^ 13 / 15 - c ^ 14 / 8
    - c ^ 15 / 17 + c ^ 17 / 19 + c ^ 18 / 20

example : ∀ c ∈ Icc (0 : ℝ) 1, 0 < Qt c := by
  unfold Qt; leancert

/--
info: LeanCert recognized: univariate interval bound

Selected strategy:
  Bernstein polynomial certificate
  exact Bernstein coefficients, bisecting up to depth 4; polynomial goals only
  bisection depth used: 0 of 4
  boxes examined: 1

Numerical computation:
  exact rational arithmetic

Certificate verification:
  requested native → used native
Checker: LeanCert.Validity.Bernstein.checkPolyStrictLowerBound
Verifier: LeanCert.Validity.Bernstein.verify_poly_strict_lower_bound_Icc

Suggested proof:
  by
    leancert

Advanced control:
  by
    bernstein_bound 4
-/
#guard_msgs in
example : ∀ c ∈ Icc (0 : ℝ) 1, 0 < Qt c := by
  unfold Qt; leancert?

/-! ## Dedicated tactic: four comparisons, both interval syntaxes -/

example : ∀ c ∈ Icc (0 : ℝ) 1, 0 < Qt c := by
  unfold Qt; bernstein_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  bernstein_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, (-27 / 100 : ℚ) ≤ x * x - x := by
  bernstein_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, x * (1 - x) < (27 / 100 : ℚ) := by
  bernstein_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, (-27 / 100 : ℚ) < x * x - x := by
  bernstein_bound

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

example : ∀ x ∈ I01, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  bernstein_bound

example : ∀ x ∈ Icc (1 / 2 : ℝ) 2, x ^ 3 - x ≥ -1 := by
  leancert

/-! ## Trust modes -/

example : ∀ x ∈ Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  bernstein_bound (trust := kernel)

example : ∀ c ∈ Icc (0 : ℝ) 1, 0 < Qt c := by
  unfold Qt; leancert (trust := kernel)

example : ∀ x ∈ Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  bernstein_bound (trust := auto)

/-! ## Typed failures -/

/-- error: bernstein_bound: no Bernstein certificate up to bisection depth 3; the coefficient enclosure on the whole interval is [-1/9, 4/9] -/
#guard_msgs in
example : ∀ x ∈ Icc (0 : ℝ) 1, (x - 1 / 3) ^ 2 ≥ 0 := by
  bernstein_bound 3

/-- error: bernstein_bound: the function is not recognized as a univariate rational polynomial:
fun (x : Real) => Real.exp x -/
#guard_msgs in
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  bernstein_bound

/-- The strategy is skipped, not reported, for non-polynomial goals. -/
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  first
  | bernstein_bound
  | leancert

-- A false bound is refuted by the existing counterexample search.
/--
error: LeanCert recognized: univariate interval bound

The statement is false.

Certified counterexample: (16383/32768 (≈ 0.499969))
At this point, the checked function value is approximately enclosed by [0.249999, 0.249999], which violates the requested comparison. The certificate uses exact rational endpoints.
-/
#guard_msgs in
example : ∀ x ∈ Icc (0 : ℝ) 1, x * (1 - x) ≤ (24 / 100 : ℚ) := by
  leancert

/-! ## The former subdivision internal error is now a proof -/

example : ∀ c ∈ Icc (0 : ℝ) 1, 0 < Qt c := by
  unfold Qt; leancert (subdivisions := 14)

/-- Subdivision transport on a high-degree polynomial no longer fails on the
`pow_succ`-normalised reification side goal. -/
example : ∀ c ∈ Icc (0 : ℝ) (1 / 2), 0 < Qt c := by
  unfold Qt; interval_bound_subdiv 10 6

/-! ## Engine level: the degree-134 cutoff-16 certificate (native trust) -/

/-- Monomial coefficients of `Q₁₆` from `rnt-paper` Appendix A: all 135
Bernstein coefficients on `[0,1]` are positive, the least being `Q₁₆(1)`. -/
def Q16 : QPoly := ⟨#[1/2, -1/3, -1/4, -1/5, 0, 0, 1/8, 1/9, 1/10, 1/11, 1/12, 0, 0, 0, -1/16, -1/17, -1/18, -1/19, -1/20, -1/21, -1/11, -2/23, -1/12, -1/25, 0, 2/27, 3/28, 4/29, 2/15, 4/31, 1/8, 1/11, 1/17, 2/35, 0, -1/37, -3/38, -5/39, -3/20, -8/41, -4/21, -8/43, -3/22, -4/45, -1/46, 1/47, 1/12, 6/49, 4/25, 3/17, 3/13, 11/53, 5/27, 8/55, 5/56, 2/57, -1/58, -5/59, -3/20, -11/61, -13/62, -13/63, -13/64, -11/65, -3/22, -6/67, -3/68, 1/23, 3/35, 9/71, 11/72, 13/73, 13/74, 13/75, 11/76, 9/77, 5/78, 1/79, -1/40, -5/81, -4/41, -10/83, -11/84, -12/85, -9/86, -8/87, -3/44, -4/89, -1/90, 1/91, 1/23, 2/31, 4/47, 8/95, 1/12, 6/97, 5/98, 1/33, 1/100, 0, -1/51, -2/103, -3/104, -4/105, -2/53, -4/107, -1/27, -3/109, -1/55, 0, 1/112, 2/113, 1/57, 3/115, 1/58, 1/117, 0, 0, 1/120, 1/121, 0, 0, 0, -1/125, -1/126, -1/127, -1/128, -1/129, 0, 0, 1/132, 1/133, 1/134, 0, -1/136]⟩

set_option maxRecDepth 8000 in
theorem Q16_pos : ∀ x ∈ I01, ((0 : ℚ) : ℝ) < Polynomial.aeval x Q16.toPoly :=
  QPoly.lt_aeval_of_bernsteinCheck (p := Q16) (c := 0) (I := I01) (depth := 0)
    (by native_decide)

/-- The certificate is exact: the enclosure's lower endpoint is `Q₁₆(1)`. -/
example : (QPoly.bernsteinEnclosure Q16 I01).lo =
    173583348686897205568920457842667584980439352718239 /
      132215406841558530489146031727131054876622501861872000 := by
  native_decide

/-! ## Goal isolation and inexpensive polynomial routing regressions -/

-- Success must preserve the second goal instead of dropping it during transport.
example : (∀ x ∈ Icc (0 : ℝ) 1, x ≤ 1) ∧ True := by
  constructor
  bernstein_bound
  trivial

-- Failure must restore both the main goal and its pending sibling.
example : (∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3) ∧ True := by
  constructor
  fail_if_success bernstein_bound
  · certify_bound
  · trivial

-- Horner handles this immediately; Bernstein kernel verification exceeds the
-- default heartbeat allowance. Keep the default allowance in this regression.
example : ∀ x ∈ Icc (0 : ℝ) 1, x ^ 100 ≤ 2 := by
  leancert (trust := kernel)
