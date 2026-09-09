# Relative Gamma estimates for the DBN route

**Status:** proved analytic estimates for the actual Gamma and `xiGamma`
functions. **The full lower bound is now also proved:** see
[Newman nonnegativity](dbn-nonnegative.md) for the integrated bounds,
`normalizedHeatApproximation`, and unconditional `Lambda_nonneg`.

## Quantitative theorems

Set `y = Im(s)`, `r = ‖u‖`. In
`LeanCert/Analysis/GammaRatio.lean`, `relative_error_bound` proves

```text
y ≥ 2, Re(s) ≥ -y/2, r ≤ y/2
  ⇒ |Gamma(s+u)/(Gamma(s) exp(u Log(s)+u²/(2s))) - 1|
      ≤ exp(8r/y + 4r²/y² + 8r³/y²) - 1.
```

The omitted linear Stirling correction is included in the explicit `O(r/y)`
error. This is a relative estimate, not an absolute Gamma asymptotic or a
statement about the principal logarithm of Gamma.

`relative_error_bound_growing` specializes it to

```text
h ≥ 2, y ≥ h⁵, Re(s) ≥ -y/2, |u| ≤ h³
  ⇒ relative error ≤ exp(20/h) - 1.
```

Thus the theorem handles genuinely growing displacements. The main bound
also applies beyond this particular radius specialization, up to `r ≤ y/2`;
its error is not asserted to be small on that entire range.

In `LeanCert/Analysis/DBN/DobnerGammaRatio.lean`, put
`ell = Log(s/(2*pi))`. `xiGamma_relative_error_bound` proves

```text
y ≥ 4, Re(s) ≥ -y/2, r ≤ y/2
  ⇒ |xiGamma(s+u)/(xiGamma(s) exp(ell*u/2+u²/(4s))) - 1|
      ≤ (1+r/y)² exp(8r/y + 4r²/y² + 4r³/y²) - 1.
```

`xiGamma_relative_error_eventually` proves bounded-displacement convergence
uniformly throughout the sector. In particular, it is uniform on any fixed
vertical strip once `y ≥ 2M`, where `|Re(s)| ≤ M`.

```lean
import LeanCert.Analysis.DBN.DobnerGammaRatio

open Complex LeanCert.Analysis

example {s u : ℂ} (hr : 0 ≤ s.re+s.im/2) (hy : 2 ≤ s.im)
    (hu : ‖u‖ ≤ s.im/2) :
    ‖Gamma (s+u)/Gamma s / Complex.exp (u*Complex.log s+u^2/(2*s))-1‖ ≤
      Real.exp (GammaRatio.ratioError s.im ‖u‖)-1 :=
  GammaRatio.relative_error_bound hr hy hu
```

## Proof, without importing a Stirling hypothesis

1. Bound the finite resolvent square sum by `8/y`, using a positive real
   telescoping majorant. The cubic sum is at most `8/y²`.
2. Justify the principal-log identity along the upper-half-plane horizontal
   ray, then telescope it. Apply Mathlib's complex-log Taylor remainder to
   obtain the linear Euler-sum error and the cubic product-log remainder.
3. Telescope the quadratic coefficient using
   `z⁻² - (z⁻¹-(z+1)⁻¹) = z⁻²*(z+1)⁻¹`.
4. Identify the exponential of the finite logarithmic expression with the
   **actual quotient of Euler Gamma approximants**. Pass to Gamma using
   `Complex.GammaSeq_tendsto_Gamma` and proved nonvanishing. No derivative
   of a pointwise limit is taken; no analytic branch is silently replaced
   by `Log(Gamma(s))`.
5. Factor `xiGamma` exactly into its polynomial, pi exponential, and Gamma
   ratio. Bound the polynomial correction and apply the half-argument
   Gamma estimate.

Theorems are pinned as kernel-trusted in `Tests/TrustManifest.lean` and
covered by `LeanCert/Test/GammaRatio.lean` and `Tests/AxiomAudit.lean`.

## Connection to the contour and completion

`saddleIntegrand_quadratic_relative_error_bound` applies the proved estimate
to the **actual normalized contour integrand**, divided by its quadratic
Gaussian model. It uses `saddleIntegrand_normalized_factorization`; it is not
an assumed model for the heat function.

The following formerly missing stages are now proved in `DobnerLimit.lean`
and `DobnerCenteredKernel.lean`:

- Integrable, parameter-explicit control outside the local Gamma region.
- Uniform fixed-index convergence after integrating over the entire contour.
- One common height threshold and summable log-Gaussian majorant for **all**
  indices, including the large-index regime.
- The final limit/sum interchange establishing `NormalizedHeatApproximation`.

The pointwise estimates do not justify these interchanges on their own.
See [the completed theorem](dbn-nonnegative.md) for the integration and
summation proofs that discharge these obligations.
