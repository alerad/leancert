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

This gives the finite Chebyshev-to-Mertens bridge. Stronger global Mertens
certificates should build on this with Abel bounds and tail envelopes.
