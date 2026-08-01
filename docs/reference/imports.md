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
import LeanCert.API.AD
import LeanCert.API.Integration
import LeanCert.API.Capabilities
import LeanCert.API.Optimization
import LeanCert.API.Bounds
```

These stable narrow imports expose checked computation, backend-native
results, common AD and integration outcomes, the executable capability
registry, global bound search, and proof-facing Boolean certificates without
loading tactic elaborators.

## Advanced Narrow Imports

### Direct Automation

```lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Bound
import LeanCert.Tactic.Extension
import LeanCert.Tactic.Enclosure
import LeanCert.Tactic.EventualBound
import LeanCert.Discovery.Commands
import LeanCert.Tactic.Discovery
```

Use `LeanCert.Tactic.Extension` in the module that declares
`@[leancert_enclosure]` rules. A proof module that executes those rules can add
`LeanCert.Tactic.Enclosure` for `enclosure_bound` / `enclosure_bound?` without
importing the full semantic router.

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
import LeanCert.API.AD
import LeanCert.Engine.AD.DomainChecked
import LeanCert.Engine.AD.Dyadic        -- bounded-denominator checked AD
import LeanCert.Engine.Optimization.Gradient -- checked full gradients
```

Prefer `LeanCert.API.AD` for `evalWithDerivative` and `evalGradient`. Use
`import LeanCert` for the re-exported backend-native names
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
