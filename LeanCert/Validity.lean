/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Validity.Bounds
public import LeanCert.Validity.Types
public import LeanCert.Validity.Dyadic
public import LeanCert.Validity.FinSum
public import LeanCert.Validity.Chebyshev
public import LeanCert.Validity.Integration
public import LeanCert.Validity.CertificateIntegration
public import LeanCert.Validity.IntegrationDyadic
public import LeanCert.Validity.AffineBounds
public import LeanCert.Validity.AffineCover
public import LeanCert.Validity.Monotonicity
public import LeanCert.Validity.DirectedLimit
public import LeanCert.Validity.Eventual
public import LeanCert.Validity.RelativeCompleteness
public import LeanCert.Validity.Krawczyk
public import LeanCert.Validity.Algebra
public import LeanCert.Validity.Bernstein

/-!
# Validity Layer

The Validity module contains the "Golden Theorems" that bridge computational
results (Bool) to semantic proofs (Prop).

## Philosophy

This layer embodies the core LeanCert principle: **Certification is the Product**.
The Engine computes numbers; Validity turns them into theorems.

## Main Components

* `Validity.Bounds` - Golden Theorems for interval bounds:
  - `checkUpperBound` (Bool) → `verify_upper_bound` (Prop)
  - `checkLowerBound` (Bool) → `verify_lower_bound` (Prop)

* `Validity.Types` - Certificate structures:
  - `VerifiedGlobalMin` - Proven global minimum
  - `VerifiedGlobalMax` - Proven global maximum
  - `VerifiedRoot` - Proven root existence

* `Validity.Dyadic`, `Validity.FinSum`, `Validity.Chebyshev` - Stable
  forwarding imports for domain-specific bridge theorem families.

* `Validity.RelativeCompleteness` - positive-margin completeness under a
  coordinated refinement schedule whose spatial, rounding, and analytic
  errors all tend to zero.

* `Validity.Krawczyk` - certified existence and uniqueness for square systems
  in the differentiable AD fragment on rational boxes.

* `Validity.Algebra` - exact Bézout certificates for polynomial separability,
  squarefreeness, and simple real roots; discriminant certificates for uniform
  parametric cubic root counts.
-/
