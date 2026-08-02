# Exceptions

Semantic outcomes such as `Rejected` and `Inconclusive` are values, not
exceptions. Exceptions represent malformed requests, compatibility wrapper
behavior, protocol failures, or unavailable infrastructure.

```python
import leancert as lc
from leancert.exceptions import ProtocolViolation

try:
    result = lc.prove(claim)
except lc.DomainError as exc:
    handle_bad_domain(exc)
except ProtocolViolation as exc:
    quarantine_bridge(exc)
```

All SDK exceptions derive from `LeanCertError`:

- `CompilationError`: legacy expression compilation failed.
- `DomainError`: a domain is invalid or incompatible.
- `VerificationFailed`: a compatibility raising API established failure.
- `VerificationInconclusive`: a compatibility raising API could not decide.
- `VerificationTimeout`: the operation exceeded its time budget.
- `BridgeError`: Bridge launch or communication failed.
  - `ProtocolViolation`: the process contradicted the negotiated wire contract.
  - `BridgeRemoteError`: a structured remote infrastructure error; inspect
    `code` and `data`.
- `ExpressionError`: expression construction or use failed.
  - `UnsupportedExpressionError`
  - `PartialFunctionError`

Import `ProtocolViolation` and `BridgeRemoteError` from `leancert.exceptions`;
do not depend on incidental root-package exposure.

`leancert.ast` exports precise construction and decoding errors, including
`AstValidationError`, `SortMismatch`, `DimensionMismatch`, `InexactFloatError`,
`InvalidDomainError`, `FreeVariableError`, `AstDecodeError`, and capability or
canonicalization errors. Catch the narrowest error your application can repair.

Do not catch `LeanCertError` merely to turn every failure into “unverified.” A
protocol violation and a mathematically inconclusive enclosure have entirely
different operational meanings.
