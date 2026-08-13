# Adaptive Verification

!!! info "Capability status"
    **Stability:** Experimental · **Authority:** Checked Bridge per accepted
    leaf · **Split selection:** Untrusted heuristic ·
    **Standalone unified replay:** No

Adaptive verification decomposes a difficult box into smaller boxes, checks
each leaf, and records the search tree. The Python scheduler can assign real
Bridge processes to separate workers, so independent leaves can be checked
concurrently.

## A bound that benefits from decomposition

The maximum of `x sin(x)` on `[0, 10]` lies just below `8`, but a coarse
enclosure has to reason across several oscillations. The adaptive driver can
split around useful algebraic regions and check the smaller leaves:

```python
from fractions import Fraction

import leancert as lc

# Adaptive verification currently uses the programmatic expression API.
x = lc.var("x")
expression = x * lc.sin(x)

config = lc.AdaptiveConfig(
    strategy=lc.SplitStrategy.ALGEBRAIC,
    max_splits=64,
    max_depth=12,
    parallel=True,
    max_workers=4,
)

with lc.Solver() as solver:
    result = solver.verify_bound_adaptive(
        expression,
        {"x": (0, 10)},
        upper=Fraction(8),
        adaptive_config=config,
    )

print(result.verified)
print(result.summary())
print(result.tree_visualization(max_depth=3))
```

On the v1.0 release this closes through multiple checked leaves rather than a
single sampled estimate.

## Split strategies

| Strategy | Selection rule |
|---|---|
| `BISECT` | Split the first axis at its midpoint |
| `LARGEST_FIRST` | Split the widest axis |
| `WORST_POINT` | Use optimizer diagnosis to choose an axis/point |
| `GRADIENT_GUIDED` | Estimate midpoint gradients with batched finite differences |
| `ALGEBRAIC` | Score heuristic critical-point, curvature, monotonicity, and dependency candidates |

Checked interval automatic differentiation exists in the numerical toolkit,
but the current gradient-guided splitter uses Python finite differences. Split
choices affect search efficiency, not proof authority.

## Parallel workers

With the normal `LeanClient`, executor threads lazily receive distinct Bridge
processes. A custom or fake client may deliberately retain shared behavior.

## Read `verified` carefully

An accepted leaf is backed by the advertised bound checker or checked adaptive
optimizer. The aggregate `AdaptiveResult.certificate` is currently a legacy
checked-leaf record, and `lean_proof` is a generated proof sketch. Neither is a
standalone replayable v1 export. Use the stable semantic bound route when an
independently rebuildable artifact is required.
