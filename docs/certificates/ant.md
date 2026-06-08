# Analytic Number Theory Certificates

`LeanCert.ANT` packages reusable finite certificate machinery for analytic
number theory pipelines:

```text
finite arithmetic data
+ rational envelopes
+ Abel / partial-summation transforms
+ Euler-product or log-product certificates
= semantic real-number bounds
```

## Import

```lean
import LeanCert.ANT
```

or through the main API:

```lean
import LeanCert
```

## Certificate Helpers

The ANT layer uses the shared rational interval helpers:

```lean
LeanCert.Cert.checkRatInterval
LeanCert.Cert.verify_rat_interval
LeanCert.Cert.verify_rat_upper
LeanCert.Cert.verify_rat_lower
```

Domain-specific modules provide the semantic lower/upper endpoint proofs; the
generic helper handles the repeated boolean-check-to-real-interval boilerplate.

## Step Sums

`StepFn` represents a semantic real-valued sequence with computable rational
lower and upper envelopes.

Golden Theorems:

```lean
verify_stepSum_interval
verify_stepSum_lower
verify_stepSum_upper
```

These turn checks over `stepLowerRat` and `stepUpperRat` into bounds for the
semantic finite sum.

## Abel Summation

The discrete Abel transform is certified exactly:

```lean
weightedSumRat_eq_abelTransformRat
```

Public checkers:

```lean
checkAbelInterval
checkAbelUpper
checkAbelLower
```

Golden Theorems:

```lean
verify_abel_interval
verify_abel_upper
verify_abel_lower
```

This is the finite backbone for later continuous partial-summation and
Stieltjes-integral APIs.

For propagation from certified prefix bounds, use the bounded Abel API:

```lean
abelBoundLowerRat
abelBoundUpperRat
checkAbelBoundInterval
verify_abelBound_interval
```

This proves weighted-sum bounds from envelopes for the prefix function
`A(k) = ∑ i < k, a i`. Coefficient signs are handled automatically when building
the lower and upper Abel endpoints.

## Euler And Log Products

Finite products are certified from pointwise nonnegative rational factor
envelopes:

```lean
verify_eulerProduct_interval
```

Finite log-products are certified from pointwise logarithm envelopes:

```lean
verify_logProduct_interval
```

Positive products can also be bounded through their logs:

```lean
finiteProduct_eq_exp_finiteLogProduct
verify_product_interval_of_log_interval
verify_product_lower_of_log_lower
verify_product_upper_of_log_upper
```

Prime-product presets are included for the most common Mertens factors:

```lean
primeEulerOneMinusInv        -- ∏ p ≤ N, (1 - 1 / p)
primeEulerOnePlusInv         -- ∏ p ≤ N, (1 + 1 / p)
verify_primeEulerOneMinusInv_interval
verify_primeEulerOnePlusInv_interval
```

The generic product machinery lives in `LeanCert.ANT.EulerProduct`; these
number-theoretic presets live in `LeanCert.ANT.PrimeEuler`.

## Prime-Power Extensionality

For multiplicative arithmetic functions, equality can be reduced to equality on
prime powers.  LeanCert exposes a stable ANT-facing wrapper around mathlib's
prime-power extensionality theorem:

```lean
LeanCert.ANT.PrimePowerExt.ext_prime_powers
LeanCert.ANT.PrimePowerExt.eq_iff_eq_on_prime_powers
```

For generated or data-driven local-factor proofs, LeanCert also exposes a
certificate object:

```lean
LeanCert.ANT.PrimePowerExt.LocalPrimePowerCert
LeanCert.ANT.PrimePowerExt.LocalPrimePowerCert.sound
```

`LocalPrimePowerCert f g` stores multiplicativity for both arithmetic functions
and equality on every prime power.  The soundness theorem proves `f = g`.

The intended workflow is:

```lean
apply LeanCert.ANT.PrimePowerExt.ext_prime_powers
-- prove multiplicativity of both sides
-- reduce the goal to:
--   ∀ p k, Nat.Prime p → f (p ^ k) = g (p ^ k)
```

This is the lightweight first layer for local Euler-factor and
arithmetic-function identity certificates.

## Explicit-PNT Compiler Schemas

`LeanCert.ANT.PNTCompilers` contains theorem schemas for the two standard
explicit-PNT envelope transfers.  They are deliberately project-agnostic:
LeanCert proves the reusable inequality algebra, while project files provide
the semantic definitions of `ψ`, `θ`, `π`, `Li`, and the decomposition
identities.

Public theorems:

```lean
psi_to_theta_bound
theta_to_pi_bound_of_decomposition
theta_to_pi_bound
```

`psi_to_theta_bound` proves the abstract transfer:

```text
theta x - x = (psi x - x) - powerContribution
|psi x - x| <= psiError
0 <= powerContribution <= powerBound
------------------------------------------------
|theta x - x| <= psiError + powerBound
```

`theta_to_pi_bound_of_decomposition` packages the partial-summation error
algebra once the project has proved a decomposition of `primeCount x - li x`
into endpoint and integral terms.

`theta_to_pi_bound` is the endpoint-specialized version where the endpoint
terms are `deltaTheta x / log x` and `deltaTheta x0 / log x0`.

These schemas are intended as the bridge between project-specific analytic
identities and LeanCert's table, interval, and Taylor integral certificates.

## Dirichlet Truncations

`LeanCert.ANT.Dirichlet` certifies finite Dirichlet-style weighted sums:

```lean
finiteDirichletSum S a w = ∑ n ∈ S, a n * w n
```

The generic checker accepts rational coefficient envelopes and nonnegative
weight envelopes:

```lean
checkDirichletSumInterval
verify_dirichletSum_interval
verify_dirichletSum_lower
verify_dirichletSum_upper
```

The multiplication envelope is sign-aware in the coefficient interval, which is
the common analytic-number-theory case: signed arithmetic coefficients against
positive weights such as `1 / n^s`.

Included presets:

```lean
harmonicSum
primeHarmonicSum
logPrimeOverPrimeSum
verify_harmonicSum_interval
verify_primeHarmonicSum_interval
verify_logPrimeOverPrimeSum_interval
```

More specialized sums, such as Möbius or von Mangoldt Dirichlet truncations, can
use the generic theorem once coefficient envelopes are supplied.

## Mertens-Style Prime Sums

The first Chebyshev integration point is:

```lean
mertensLogSum N = ∑ p ∈ primesLE N, Real.log p / p
```

The checker uses the existing Chebyshev theta log enclosures:

```lean
checkMertensLogSumInterval
verify_mertensLogSum_interval
```

There is also an Abel-routed version:

```lean
mertensAbelSum
checkMertensAbelInterval
verify_mertensAbel_interval
```

This is the finite Chebyshev-to-Abel-to-Mertens bridge. Stronger global Mertens
certificates should build on this with tail envelopes.

## Asymptotic Envelopes

For main-term/error-term certificates and transform kernels for summatory
functions, see [Asymptotic Envelope Certificates](ant-asymp.md).

The asymptotic layer builds on the finite ANT machinery but has a different API:
it packages semantic envelopes as `AsympEnv`, then composes them through
Stieltjes-Abel and Dirichlet-hyperbola kernels.
