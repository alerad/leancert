# Result Types

LeanBound returns rich result objects containing both numerical data and verification certificates.

## BoundsResult

Returned by `find_bounds()`.

::: leanbound.result.BoundsResult
    options:
      show_root_heading: true

## RootsResult

Returned by `find_roots()`.

::: leanbound.result.RootsResult
    options:
      show_root_heading: true

## RootInterval

Represents an isolating interval for a root.

::: leanbound.result.RootInterval
    options:
      show_root_heading: true

## UniqueRootResult

Returned by `find_unique_root()`.

::: leanbound.result.UniqueRootResult
    options:
      show_root_heading: true

## IntegralResult

Returned by `integrate()`.

::: leanbound.result.IntegralResult
    options:
      show_root_heading: true

## Certificate

Contains the verification certificate that can be exported to Lean.

::: leanbound.result.Certificate
    options:
      show_root_heading: true
      members:
        - to_lean_tactic
        - save
        - load

## VerifyResult

Returned by `verify_bound()`.

::: leanbound.result.VerifyResult
    options:
      show_root_heading: true
