# DBN contour shifts and exact saddle cancellation

**Completion update:** the full lower bound `0 ≤ Lambda` is now proved in
`DBN/DobnerLimit.lean`. See [the final theorem](dbn-nonnegative.md).
Descriptions of remaining work below record the earlier stage of development.


**Proved:** actual termwise contour shifts between any two positive vertical
lines, including the change of variables connecting them to
`normalizedContourTerm`. **Not proved:** the relative saddle asymptotic or
`Lambda≥0`.

This uses the existing [contour-shift certificate engine](contour-shift.md),
not a new contour integration axiom.

## Reusable certificate additions

`LeanCert.Analysis.ContourShift.Decay` adds:

- `RectangleShiftCert.ofHolomorphicStrip`: a zero-residue constructor from
  holomorphy on a closed strip; either horizontal orientation is allowed.
- `horizontalBoundOfStrip`: bounds both horizontal integrals from a uniform
  strip bound tending to zero.
- `integral_vertical_eq_of_holomorphic_of_vanish`: constructs a
  `ContourShiftCert` and identifies its limiting values with actual Lebesgue
  integrals using absolute integrability and improper-integral convergence.

The last theorem closes the distinction between chosen sequence-relative
limits and actual infinite vertical-line integrals for this integrable case.
The original certificate's general semantics are unchanged.

## Actual DBN instance

For `b>0`, center `w`, and real `L` (specialized later to `log n`), define

```text
F(z) = exp((w-z)^2/b) * xiGamma(z) * exp(-z L).
```

On each fixed positive strip `p≤Re(z)≤q`, we prove a bound

```text
|F(z)| ≤ C (1+Im(z)^2) exp(-Im(z)^2/(2b)).
```

**The constant depends on `b,w,L,p,q`.** It is not yet uniform as the center
moves to infinite height or as the Dirichlet index grows. The estimate proves
horizontal-side vanishing and absolute integrability on every positive
vertical line. Gamma's Euler integral controls its modulus there, and
compactness controls the remaining real-coordinate factors.

The zero-residue certificate then yields:

```lean
import LeanCert.Analysis.DBN.DobnerContourShift

open LeanCert.Analysis.DBN Complex MeasureTheory

example {b : ℝ} (hb : 0 < b) (w : ℂ) (L σ₀ σ₁ : ℝ)
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) :
    (∫ y : ℝ, saddleIntegrand b w L ((σ₀ : ℂ)+(y : ℂ)*I)) =
      ∫ y : ℝ, saddleIntegrand b w L ((σ₁ : ℂ)+(y : ℂ)*I) :=
  saddleIntegrand_contour_shift b hb w L σ₀ σ₁ h₀ h₁
```

This is safe in either direction, provided both real parts are positive.
It does not authorize shifting a full contour through Gamma's negative-real
poles. No residue calculation is needed inside this positive strip.

## Connection to the existing heat-function series

The theorem `normalizedContourTerm_eq_shifted_integral` proves

```text
normalizedContourTerm(a,s,k)
  = integral_y F(sigma+i*y) /
      (2 sqrt(a) sqrt(pi) dobnerGamma(a,s)),

where b=4a, w=J_a(s), L=log(k+1), a>0, sigma>0.
```

The factor `2 sqrt(a)` comes from the actual change of variables in the
previously defined coefficient; it is not dropped or inferred numerically.
This is the same coefficient used in the already-proved exact series for
`normalizedHeat`, not a replacement definition.

`normalizedContourTerm_eq_saddle_line` chooses

```text
sigma = max(2, Re(s)+2a log(k+1)).
```

The line lies through or to the right of the leading real saddle and stays
pole-free even when `Re(s)` is negative. This is the leading saddle location,
not a claim that it is the exact stationary point of the full integrand.

## Exact cancellation: now checked in Lean

For `ell=Log(s/(2pi))`, `b=4a`, `w=J_a(s)`, the actual normalized integrand
factors as

```text
F(s+u)/dobnerGamma(a,s)
  = [xiGamma(s+u)/xiGamma(s) * exp(-ell*u/2)]
      * exp(-s L + u^2/(4a) - u L).
```

This is `saddleIntegrand_normalized_factorization`. The remaining factor in
brackets is precisely the relative Gamma expression that must be controlled
near the moving saddle. The Gaussian cancellation is exact, not an
application of Stirling with an unproved remainder.

## Asymptotic continuation — now completed

1. **Done:** [proved local relative Gamma estimates](dbn-gamma-ratio.md),
   including a pointwise bound for this actual normalized integrand.
2. **Done:** bound remote portions uniformly after normalization as the center moves.
3. **Done:** establish a summable all-index envelope and pass to the infinite series.

The new fixed-parameter decay bounds do not discharge (2) or (3). Together
with the previously proved reciprocal-normalization bound, they remove the
basic contour deformation and orientation obligations, but not the uniform
asymptotic analysis.

Tests: `LeanCert/Test/DBNContourShift.lean`. The contour identity and exact
factorization are pinned by the trust and axiom audits.

The next implementation steps and reusable-library audit are in the
[DBN completion strategy](dbn-completion-strategy.md).
