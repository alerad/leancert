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
