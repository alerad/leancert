/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Bounds
import LeanCert.Validity.Types
import LeanCert.Validity.Dyadic
import LeanCert.Validity.FinSum
import LeanCert.Validity.Chebyshev
import LeanCert.Validity.Integration
import LeanCert.Validity.CertificateIntegration
import LeanCert.Validity.IntegrationDyadic
import LeanCert.Validity.AffineBounds
import LeanCert.Validity.AffineCover
import LeanCert.Validity.Monotonicity
import LeanCert.Validity.DirectedLimit
import LeanCert.Validity.Krawczyk

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

* `Validity.Krawczyk` - certified existence and uniqueness for square systems
  in the differentiable AD fragment on rational boxes.
-/
