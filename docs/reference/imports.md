# Imports Reference

Downstream developments should start with the stable umbrella imports:

```lean
import LeanCert.Tactic
import LeanCert.CertifiedBounds
import LeanCert.ANT
```

Use `import LeanCert` when you intentionally want the full aggregate API.
The narrower implementation-level imports below are useful for advanced
development, but names under `LeanCert.Engine.*` do not carry the same
downstream stability promise.

## Checked Programmatic API

```lean
import LeanCert.API.Eval
import LeanCert.API.Backend
import LeanCert.API.Optimization
import LeanCert.API.Bounds
import LeanCert.API.MatrixPositivity
```

These stable narrow imports expose checked computation, backend-native
results, global bound search, and proof-facing Boolean certificates without
loading tactic elaborators.

`LeanCert.API.MatrixPositivity` exposes exact rational Gram/LDLᵀ checkers,
their real-matrix Golden Theorems, and finite Gram/kernel constructions.

## Advanced Narrow Imports

### Direct Automation

```lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Bound
import LeanCert.Tactic.Extension
import LeanCert.Tactic.EventualBound
import LeanCert.Discovery.Commands
import LeanCert.Tactic.Discovery
```

### Proof Templates

```lean
import LeanCert.Engine.Table
import LeanCert.ANT.Asymp
import LeanCert.ConstantFactory
import LeanCert.ConstantFactory.IntervalBank
import LeanCert.QProduct
import LeanCert.Analysis.ContourShift
```

### Domain Libraries

```lean
import LeanCert.ANT
import LeanCert.Engine.Chebyshev.Psi
import LeanCert.Engine.Chebyshev.Theta
```

### Nonlinear System Roots

```lean
import LeanCert.Validity.Krawczyk
```

### Matrix positive-semidefiniteness and positive-definiteness

```lean
import LeanCert.API.MatrixPositivity
```

For automatic or manual system-root tactics, import the tactic umbrella:

```lean
import LeanCert.Tactic
```

### Fixed-cutoff eventual bounds

```lean
import LeanCert.Validity.Eventual
```

### Algebraic Root Simplicity

```lean
import LeanCert.Validity.Algebra
```

### Domain-aware automatic differentiation

```lean
import LeanCert.Engine.AD.DomainChecked
import LeanCert.Engine.AD.Dyadic        -- bounded-denominator checked AD
import LeanCert.Engine.Optimization.Gradient -- checked full gradients
```

Use `import LeanCert` for the re-exported public names
`derivIntervalChecked`, `gradientIntervalChecked`, the Dyadic counterparts
`derivIntervalDyadicChecked` and `gradientIntervalDyadicChecked`, and their
soundness theorems. See
[Checked Automatic Differentiation](../direct/checked-ad.md) for backend choice,
Rational-input Dyadic wrappers, and Golden-Theorem examples.

### ML Verification

```lean
import LeanCert.ML.Network
import LeanCert.ML.Transformer
import LeanCert.ML.Optimized
```

## Aggregate Import

```lean
import LeanCert
```
