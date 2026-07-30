# Compatibility surfaces

Compatibility modules preserve historical downstream imports while directing
new code to a canonical owner. They remain tested, but new declarations should
not be added to them.

| Historical surface | Canonical surface | Status |
| --- | --- | --- |
| `LeanCert.Engine.ChebyshevPsi` | `LeanCert.Engine.Chebyshev.Psi` | forwarding import |
| `LeanCert.Engine.ChebyshevTheta` | `LeanCert.Engine.Chebyshev.Theta` | forwarding import |
| `LeanCert.Examples.BKLNW_a2_bounds` and related `BKLNW_a2_*` declarations | `LeanCert.CertifiedBounds.BKLNW` | downstream compatibility |
| `LeanCert.Examples.Li2Bounds` | `LeanCert.CertifiedBounds.Li2` | lightweight historical interface; see qualification below |
| deprecated tactic and discovery spellings | replacements listed in [Supported Public API](public-api.md#semantic-tactic-api-migration) | deprecated aliases |

## Li₂ qualification

`LeanCert.Examples.Li2Bounds` preserves the historical lightweight
downstream interface. Its two numerical bound statements are the only
allowlisted `sorry` declarations in `LeanCert/`; CI pins their names and exact
types. The separate `Li2Verified` target constructs the checked proofs and
performs statement-identity checks.

This split avoids imposing the expensive verification target on every
downstream import, but importing the lightweight interface alone is not a
placeholder-free trust boundary. New code should use
`LeanCert.CertifiedBounds.Li2` and select the build policy appropriate to the
project. Reconnecting the lightweight statement module directly to the heavy
proof constants remains an explicit roadmap decision.

## Policy

- Compatibility surfaces name their canonical replacement.
- Their behavior is covered by downstream interface or functional tests.
- Removal requires a deprecation period and release note.
- Compatibility modules do not become owners of new APIs or certified facts.
