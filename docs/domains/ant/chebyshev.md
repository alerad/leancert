# Chebyshev Certificates

Chebyshev certificates provide specialized finite-range bounds for `ψ` and
`θ`.

Use this page when the theorem is specifically about Chebyshev functions rather
than a generic table or envelope pattern.

Recommended imports:

```lean
import LeanCert.Engine.Chebyshev.Psi
import LeanCert.Engine.Chebyshev.Theta
```

The finite-range checkers compute rational enclosures for logarithmic sums.
Their Golden Theorems produce bounds for `ψ` and `θ` at natural endpoints and,
where provided, on the corresponding real intervals. Projects choose the
range, slope or error target, and Taylor depth; the checker verifies every
retained row.

Detailed API reference:

[Chebyshev Certificates](../../certificates/chebyshev.md)
