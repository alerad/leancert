# Result Types

## Semantic proof outcomes

Results from `prove()` have no Boolean truth value. Pattern-match the concrete
type:

```python
import leancert as lc

result = lc.prove(claim)
if isinstance(result, lc.Verified):
    ...
elif isinstance(result, lc.Rejected):
    ...
elif isinstance(result, lc.Inconclusive):
    ...
```

Bound outcomes retain per-check evidence and Bridge provenance. System-root
and eventual-bound outcomes have their own typed families and replayable
certificate payloads. See [Typed Outcomes](../proving/outcomes.md).

## Toolkit numerical results

| Type | Useful members |
|---|---|
| `BoundsResult` | exact `min_bound`/`max_bound`; float conveniences `min_lo`, `min_hi`, `max_lo`, `max_hi`; midpoint estimates `min_value`, `max_value` |
| `RootInterval` | `interval`, `status`, `lo`, `hi`, `value`, `width` |
| `RootsResult` | isolated root intervals and retained certificate |
| `UniqueRootResult` | existence/uniqueness status, root interval, derivative evidence |
| `IntegralResult` | exact enclosure, approximate value, and `error` convenience |
| `LipschitzResult` | derivative enclosures and aggregate Lipschitz bound |
| `WitnessPoint` | candidate coordinates, function value, and verification metadata |
| `FailureDiagnosis` | margins, worst-point candidate, and suggested bounds |

Float convenience properties are for display. Exact `Fraction` endpoints in
the underlying `Interval` are the rigorous values.

## Legacy certificates

`Certificate.save()`, `Certificate.load()`, and `Certificate.hash()` support
legacy JSON persistence. `render_proof_sketch()` is non-authoritative generated
text. For portable kernel evidence, use `export_lean_project()` on a supported
semantic typed outcome and independently rebuild it.

`VerificationReport` contains `ArtifactVerification` entries and exposes
`verified`, `verified_count`, `exit_code`, and `to_dict()`.
