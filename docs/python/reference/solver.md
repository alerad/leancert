# Solver Toolkit Reference

`Solver` owns a Bridge subprocess and provides the lower-level programmatic
interface. Prefer a context manager so the subprocess is always closed.

```python
import leancert as lc

x = lc.var("x")
with lc.Solver() as solver:
    enclosure = solver.eval_interval(x * x, {"x": (-2, 3)})
    bounds = solver.find_bounds(x * x, {"x": (-2, 3)})
```

| Methods | Purpose | Typical result |
|---|---|---|
| `eval_interval`, `find_bounds` | rigorous enclosure and global bounds | `Interval`, `BoundsResult` |
| `verify_bound` | typed checked lower/upper-bound decision | `Verified`, `Rejected`, `Inconclusive`, ... |
| `verify_bound_or_raise` | compatibility exception wrapper | typed result or exception |
| `find_roots`, `find_unique_root` | scalar isolation and uniqueness | `RootsResult`, `UniqueRootResult` |
| `integrate` | verified integral enclosure | `IntegralResult` |
| `compute_lipschitz_bound` | checked derivative enclosure | `LipschitzResult` |
| `diagnose_bound_failure` | candidate explanation and suggested bounds | `FailureDiagnosis` |
| `verify_bound_adaptive` | split-and-check orchestration | `AdaptiveResult` |
| `synthesize_*_witness` | candidate witness search plus retained checks | witness result types |

Method names such as `find_*` may combine untrusted search with checked leaves.
Inspect the result type, its `verified` field where applicable, and retained
certificate/provenance rather than inferring authority from successful return.
Legacy `Certificate.render_proof_sketch()` is not equivalent to a rebuildable
`Verified.export_lean_project()` artifact.

Use the semantic `prove()` interface when you want a closed claim, claim
digest, negotiated capability, and typed proof outcome as one workflow.
