# Configuration Reference

LeanCert has two configuration families because semantic proving and the
legacy numerical toolkit expose different contracts.

## `ProveConfig`

```python
import leancert as lc

config = lc.ProveConfig(
    taylor_depth=14,
    system_root=lc.SystemRootConfig(
        max_iterations=12,
        max_dimension=4,
        precision_bits=28,
    ),
    eventual=lc.EventualConfig(max_checks=2000),
)
```

| Field | Default | Meaning |
|---|---:|---|
| `taylor_depth` | `10` | non-negative checker effort for supported operations |
| `system_root.max_iterations` | `8` | Krawczyk candidate-search refinements |
| `system_root.max_dimension` | `4` | caller ceiling; cannot exceed Bridge capability |
| `system_root.precision_bits` | `20` | candidate rationalization/search precision |
| `system_root.candidate` | `None` | optional explicit `KrawczykCandidate` |
| `eventual.max_checks` | `1000` | cutoff-search check budget |

These settings control effort and candidate search. They do not let a caller
invent a checker capability the Bridge did not advertise.

## Toolkit `Config`

`Config` controls legacy `Solver` operations: `taylor_depth`, `max_iters`,
`tolerance`, `use_monotonicity`, `timeout_sec`, `backend`, backend-specific
configuration, racing, incremental refinement, target bound, and timeout.

Presets include:

- `Config.low_precision()`, `medium_precision()`, `high_precision()`;
- `Config.dyadic()`, `dyadic_fast()`, `dyadic_high_precision()`; and
- `Config.affine()`, `affine_compact()`.

`DyadicConfig` exposes `precision` and the compatibility `round_after_ops`
field, with `ieee_double()`, `high_precision()`, and `fast()` presets.
`AffineConfig` exposes `max_noise_symbols`, with `default()` and `compact()`.

!!! warning "Exact input boundary"
    `ProveConfig` never changes the rule that semantic values must be exact.
    Toolkit configuration may accept floats for heuristic tolerances or search
    inputs; that does not make those floats part of an exact semantic claim.
