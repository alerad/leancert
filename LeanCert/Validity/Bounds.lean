/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Bounds.Basic
import LeanCert.Validity.GlobalOpt
import LeanCert.Validity.RootFinding
import LeanCert.Validity.Integration
import LeanCert.Validity.CertificateIntegration

/-!
# Certificate-Driven Verification

This file provides the infrastructure for certificate-driven verification of
numerical bounds. Instead of Lean searching for a proof, an external agent
(e.g., Python) provides a **Certificate** containing:
- `Expr`: The function f(x)
- `Domain`: The interval I
- `Claim`: E.g., f(I) ⊆ [a, b]
- `ProofParams`: Parameters like Taylor series depth

If the agent determines that exp(x) needs 20 Taylor terms to satisfy a bound,
it passes `taylorDepth := 20` to Lean. Lean runs the computation with that
depth and checks the boolean result via `native_decide`.

## Submodules

### Bounds/
- `Bounds/Core` - Basic boolean checkers and golden theorems for bound verification
- `Bounds/WithInv` - Support for expressions with inverse-like operations (inv, log, atan, etc.)
- `Bounds/Smart` - Monotonicity-aware bounds using derivative information
- `Bounds/Bridge` - Set.Icc bridge theorems and subdivision combinators

### Top-level
- `GlobalOpt` - Global optimization certificates for multivariate boxes
- `RootFinding` - Root finding certificates with Newton iteration and bisection
- `Integration` - Computable integration infrastructure
- `CertificateIntegration` - Certificate-based integration (proof by reflection)

## Usage

Import this module to get access to all certificate-driven verification functionality:

```lean
import LeanCert.Validity.Bounds
```
-/
