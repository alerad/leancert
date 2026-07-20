# Imports Reference

Use narrow imports while developing, and `import LeanCert` when you want the
aggregate public API.

## Direct Automation

```lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.DyadicAuto
import LeanCert.Tactic.Bound
import LeanCert.Discovery
```

## Proof Templates

```lean
import LeanCert.Engine.Table
import LeanCert.ANT.Asymp
import LeanCert.ConstantFactory
import LeanCert.ConstantFactory.IntervalBank
import LeanCert.QProduct
import LeanCert.Analysis.ContourShift
```

## Domain Libraries

```lean
import LeanCert.ANT
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta
```

## Nonlinear System Roots

```lean
import LeanCert.Validity.Krawczyk
```

## Domain-aware automatic differentiation

```lean
import LeanCert.Engine.AD.DomainChecked
import LeanCert.Engine.AD.Dyadic        -- bounded-denominator checked AD
import LeanCert.Engine.Optimization.Gradient -- checked full gradients
```

Use `import LeanCert` for the re-exported public names
`derivIntervalChecked`, `gradientIntervalChecked`, the Dyadic counterparts
`derivIntervalDyadicChecked` and `gradientIntervalDyadicChecked`, and their
soundness theorems.

## ML Verification

```lean
import LeanCert.ML.Network
import LeanCert.ML.Transformer
import LeanCert.ML.Optimized
```

## Aggregate Import

```lean
import LeanCert
```
