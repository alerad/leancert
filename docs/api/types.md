# Result Types

!!! info "Repository split"
    Canonical Python SDK docs now live in **`alerad/leancert-python`**:
    https://github.com/alerad/leancert-python

    Bridge/runtime release docs live in **`alerad/leancert-bridge`**:
    https://github.com/alerad/leancert-bridge

    This page is kept here as reference.

LeanCert returns rich result objects containing both numerical data and verification certificates.

## BoundsResult

Returned by `find_bounds()`.

::: leancert.result.BoundsResult
    options:
      show_root_heading: true

## RootsResult

Returned by `find_roots()`.

::: leancert.result.RootsResult
    options:
      show_root_heading: true

## RootInterval

Represents an isolating interval for a root.

::: leancert.result.RootInterval
    options:
      show_root_heading: true

## UniqueRootResult

Returned by `find_unique_root()`.

::: leancert.result.UniqueRootResult
    options:
      show_root_heading: true

## IntegralResult

Returned by `integrate()`.

::: leancert.result.IntegralResult
    options:
      show_root_heading: true

## Certificate

Contains the verification certificate that can be exported to Lean.

::: leancert.result.Certificate
    options:
      show_root_heading: true
      members:
        - to_lean_tactic
        - save
        - load

## VerifyResult

Returned by `verify_bound()`.

::: leancert.result.VerifyResult
    options:
      show_root_heading: true

## Witness Synthesis Results

These types support auto-witness synthesis for existential proof goals.

### WitnessPoint

A concrete witness point with variable values and function value.

::: leancert.result.WitnessPoint
    options:
      show_root_heading: true

### MinWitnessResult

Returned by `synthesize_min_witness()`. Proves: `âˆƒ m, âˆ€ x âˆˆ I, f(x) â‰¥ m`

::: leancert.result.MinWitnessResult
    options:
      show_root_heading: true

### MaxWitnessResult

Returned by `synthesize_max_witness()`. Proves: `âˆƒ M, âˆ€ x âˆˆ I, f(x) â‰¤ M`

::: leancert.result.MaxWitnessResult
    options:
      show_root_heading: true

### RootWitnessResult

Returned by `synthesize_root_witness()`. Proves: `âˆƒ x âˆˆ I, f(x) = 0`

::: leancert.result.RootWitnessResult
    options:
      show_root_heading: true

### FailureDiagnosis

Returned by `diagnose_bound_failure()`. Used for CEGPR support.

::: leancert.result.FailureDiagnosis
    options:
      show_root_heading: true

## Discovery Results (Lean)

The Lean side provides structured result types for discovery operations.

### VerifiedGlobalMin

Contains the lower bound, the box where it was found, and the formal proof.

```lean
structure VerifiedGlobalMin where
  lowerBound : â„š
  achievingBox : Box
  proof : âˆ€ x âˆˆ domain, f x â‰¥ lowerBound
```

### VerifiedRoot

Contains an isolating interval for a root and the proof of existence (via sign change/IVT).

```lean
structure VerifiedRoot where
  interval : IntervalRat
  proof : âˆƒ x âˆˆ interval, f x = 0
```

### VerifiedEquivalence

Contains the certificate that two neural networks produce outputs within a specific tolerance Îµ.

```lean
structure VerifiedEquivalence where
  tolerance : â„š
  proof : âˆ€ x âˆˆ domain, |teacher x - student x| â‰¤ tolerance
```

