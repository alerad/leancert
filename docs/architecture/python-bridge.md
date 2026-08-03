# Python Bridge Contract

The Python SDK communicates with `lean_bridge` over a versioned newline-delimited
JSON protocol. It is a typed capability contract, not generic JSON-RPC.

## Handshake

Before checked operations, `get_info` identifies:

- protocol, Bridge, Lean, and LeanCert versions;
- framing and protocol name;
- source revision, source digest, environment digest, and build profile;
- supported operations and expression nodes;
- request, result, and certificate schemas;
- available numerical backends; and
- verification routes.

The SDK refuses to send unadvertised operations and validates that responses
use the authority negotiated for that operation.

## Checked capability families

| Capability | Stable Python outcome | Replay payload |
|---|---|---|
| `check_bound` | `Verified` and typed non-successes | `bound-check/2` |
| `verify_adaptive` | Checked adaptive leaf evidence | `adaptive-bound-check/1` |
| `check_unique_system_root` | `VerifiedSystemRoot` / `CandidateRejected` | `krawczyk-check/1` |
| `check_eventual_bound` | `VerifiedEventualBound` and typed non-successes | `eventual-bound-check/1` |

Adaptive evidence is intentionally distinct from the fixed payload families
currently supported by standalone project export.

## Validation is not re-proving

Python validates exact rationals, requested direction, claim/payload agreement,
certificate schema, checker identity, and verification route. These checks
prevent Python from misrepresenting a Bridge result; they do not prove the
mathematical theorem a second time.

## Failure boundary

Malformed envelopes, mismatched response IDs, contradictory results, and
unknown schemas are protocol failures. Mathematical non-success is represented
by typed operation outcomes such as `Inconclusive`, `Unsupported`, or
`CandidateRejected`.

For the Lean-side checker and Golden-Theorem story, continue to the
[trust model](trust-model.md).
