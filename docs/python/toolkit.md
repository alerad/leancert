# Programmatic Numerical Toolkit

The `Solver` API exposes checked numerical operations below the semantic
`prove()` layer. It is useful for exploration, algorithm development, and
advanced control, but most of its legacy result families do not yet provide
the standalone replay contract of v1 semantic claims.

!!! warning "Authority"
    These are rigorous Bridge operations, not ordinary floating-point
    estimates. Nevertheless, a legacy `Certificate` or rendered tactic string
    is not automatically an independently rebuildable Lean theorem.

## Lifecycle

```python
import leancert as lc

x = lc.var("x")
with lc.Solver() as solver:
    enclosure = solver.eval_interval(lc.exp(x), {"x": (0, 1)})
    bounds = solver.find_bounds(x * lc.sin(x), {"x": (0, 10)})
```

The context manager owns one Bridge process and closes it deterministically.

## Operations

| Operation | Purpose |
|---|---|
| `eval_interval` | Enclose an expression on a box |
| `find_bounds` | Compute rigorous global min/max enclosures |
| `find_roots` | Isolate scalar roots and distinguish confirmed/possible regions |
| `find_unique_root` | Check interval-Newton contraction for a scalar root |
| `integrate` | Compute rigorous one-dimensional integral bounds |
| `compute_lipschitz_bound` | Enclose derivatives with checked forward AD |
| `forward_interval` | Propagate intervals through sequential ReLU layers |

## Arithmetic backends

```python
rational = lc.Config(backend=lc.Backend.RATIONAL)
dyadic = lc.Config.dyadic(precision=-80)
affine = lc.Config.affine()
```

- **Rational** uses exact fractions and can experience denominator growth.
- **Dyadic** uses fixed-precision powers of two with outward rounding.
- **Affine** tracks correlations between repeated variables to reduce the
  dependency problem.

The legacy solver can automatically select Affine arithmetic for expressions
with repeated variables when `auto_affine` is enabled. Backend selection here
does not imply that `prove()` exposes arbitrary backend choice; semantic proving
uses the backend advertised by its checked capability.

## Checked automatic differentiation

```python
with lc.Solver() as solver:
    sensitivity = solver.compute_lipschitz_bound(
        x**2,
        {"x": (0, 1)},
    )
    print(sensitivity.gradient_bounds)
```

Derivative intervals are computed by the Bridge. When interpreting a scalar
Lipschitz constant in several variables, document the norm convention used by
the consuming argument.

## Prefer semantic claims for durable proof APIs

Use `lc.prove()` when the mathematical statement fits a stable checked claim
family. It adds exact input discipline, normalized claim identity, typed
non-success, complete provenance, and replayable export.
