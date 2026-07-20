# Supported downstream API

LeanCert provides three stable umbrella imports for downstream developments:

```lean
import LeanCert.Tactic
import LeanCert.CertifiedBounds
import LeanCert.ANT
```

`LeanCert.Tactic` exposes supported proof automation, including
`interval_auto`, `interval_decide`, and `interval_bound`.

`LeanCert.CertifiedBounds` exposes pre-verified numerical results under:

- `LeanCert.CertifiedBounds.Li2`;
- `LeanCert.CertifiedBounds.BKLNW`;
- `LeanCert.CertifiedBounds.Chebyshev`.

The Li₂ namespace includes the symmetric integrand and its basic bounds as
well as the certified `li(2)` value and numerical enclosure.

`LeanCert.ANT` exposes reusable analytic-number-theory certificate machinery
and explicit-PNT compiler schemas.

Names under these namespaces carry the downstream stability promise: statement
changes and removals require a compatibility period and must pass the
PrimeNumberTheoremAnd-derived interface and behavioral pattern suites.

Historical `LeanCert.Examples.Li2Bounds` and `LeanCert.Examples.BKLNW_*`
imports continue to compile. Their legacy certificate declarations are
deprecated with machine-readable replacements. Direct `LeanCert.Engine.*`
imports remain available for implementation-level work, but downstream proofs
should prefer the stable certified-bounds aliases where one exists.

## Checked automatic differentiation

The aggregate `LeanCert` import also exposes the checked AD boundary:

- `derivIntervalChecked` and `derivIntervalChecked1` for one coordinate;
- `gradientIntervalChecked` for every coordinate of a list-backed box;
- `evalWithDerivChecked_der_correct` and `derivIntervalChecked_correct` as the
  semantic soundness theorems;
- `gradientIntervalChecked_correct` for coordinate-aligned full-gradient
  soundness;
- `evalWithDerivChecked_differentiableAt` for extracting differentiability.

These APIs support `inv` and `log` when their interval arguments prove the
required domain conditions. They return `EvalResult`; application code should
not substitute the internal total evaluator.
