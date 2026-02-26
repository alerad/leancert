# Configuration

!!! info "Repository split"
    Canonical Python SDK docs now live in **`alerad/leancert-python`**:
    https://github.com/alerad/leancert-python

    Bridge/runtime release docs live in **`alerad/leancert-bridge`**:
    https://github.com/alerad/leancert-bridge

    This page is kept here as reference.

LeanCert supports multiple arithmetic backends for different performance/precision tradeoffs.

## Backend Selection

```python
import leancert as lc

# Default: Dyadic arithmetic (fast, ~15 decimal digits)
result = lc.find_bounds(expr, domain)

# Explicit Dyadic with custom precision
result = lc.find_bounds(expr, domain, config=lc.Config.dyadic(precision=-100))

# Affine: 50-90% tighter bounds for correlated variables
result = lc.find_bounds(expr, domain, config=lc.Config.affine())

# Rational: Exact arithmetic (slower, use when precision matters)
result = lc.find_bounds(expr, domain, config=lc.Config(backend=lc.Backend.RATIONAL))
```

## Backend Enum

::: leancert.config.Backend
    options:
      show_root_heading: true

### Comparison

| Backend | Speed | Precision | Best For |
|---------|-------|-----------|----------|
| `DYADIC` (default) | 10-100x faster | ~15 decimal digits | Neural networks, deep expressions |
| `AFFINE` | Similar to Rational | Tighter bounds | Repeated variables, LayerNorm |
| `RATIONAL` | Baseline | Exact | When exact precision is required |

## Config Class

::: leancert.config.Config
    options:
      show_root_heading: true
      members:
        - taylor_depth
        - max_iters
        - tolerance
        - use_monotonicity
        - timeout_sec
        - backend
        - dyadic_config
        - affine_config
        - race_strategies
        - incremental_refinement
        - target_bound
        - timeout_ms
        - low_precision
        - medium_precision
        - high_precision
        - dyadic
        - dyadic_fast
        - dyadic_high_precision
        - affine
        - affine_compact

### Factory Methods

```python
# Precision presets
lc.Config.low_precision()     # Fast, ~2 decimal places
lc.Config.medium_precision()  # Default, ~3 decimal places
lc.Config.high_precision()    # Slow, ~5 decimal places

# Backend presets
lc.Config.dyadic()            # IEEE double-like precision
lc.Config.dyadic_fast()       # Lower precision, faster
lc.Config.dyadic_high_precision()  # ~30 decimal digits

lc.Config.affine()            # Affine arithmetic (tight bounds)
lc.Config.affine_compact()    # With noise symbol consolidation
```

## DyadicConfig

::: leancert.config.DyadicConfig
    options:
      show_root_heading: true

### Precision Levels

| Precision | Decimal Digits | Use Case |
|-----------|---------------|----------|
| `-30` | ~9 | Fast prototyping |
| `-53` | ~15 | Default (IEEE double-like) |
| `-100` | ~30 | High-precision verification |

```python
# Custom Dyadic configuration
config = lc.Config(
    backend=lc.Backend.DYADIC,
    dyadic_config=lc.DyadicConfig(precision=-100)
)
```

## AffineConfig

::: leancert.config.AffineConfig
    options:
      show_root_heading: true

### The Dependency Problem

Standard interval arithmetic loses correlations between variables:

```python
x = lc.var('x')

# Interval arithmetic: x - x on [-1, 1] gives [-2, 2]
result_interval = lc.find_bounds(x - x, {'x': (-1, 1)})
print(result_interval.max_hi)  # 2.0 (overapproximation!)

# Affine arithmetic: x - x on [-1, 1] gives [0, 0]
result_affine = lc.find_bounds(x - x, {'x': (-1, 1)}, config=lc.Config.affine())
print(result_affine.max_hi)  # 0.0 (exact!)
```

Affine arithmetic tracks linear correlations, giving tighter bounds for:

- Expressions with repeated variables (`x*x - x*x`)
- LayerNorm in transformers (mean/variance correlation)
- Control systems with rotation matrices

```python
# Custom Affine configuration
config = lc.Config(
    backend=lc.Backend.AFFINE,
    affine_config=lc.AffineConfig(max_noise_symbols=100)
)
```

## Witness Synthesis Options

These options control the behavior of `synthesize_*_witness` methods.

### race_strategies

When `True`, races multiple backends (dyadic, affine, rational) in parallel and uses the first to complete successfully. Useful for unknown expressions where you don't know which backend will perform best.

```python
config = lc.Config(race_strategies=True, timeout_ms=5000)
result = solver.synthesize_min_witness(expr, domain, config=config)
print(result.strategy_used)  # Which backend won
```

### incremental_refinement

When `True`, iteratively refines the bound using binary search to find the tightest provable value. Returns a history of refinement attempts.

```python
config = lc.Config(incremental_refinement=True)
result = solver.synthesize_max_witness(expr, domain, config=config)
print(result.refinement_history)
# [{'bound': 2.8, 'status': 'verified'}, {'bound': 2.75, 'status': 'verified'}, ...]
```

### target_bound

Sets a target bound for incremental refinement. Refinement stops when this bound is proven or exceeded.

```python
config = lc.Config(incremental_refinement=True, target_bound=2.72)
result = solver.synthesize_max_witness(lc.exp(x), {'x': (0, 1)}, config=config)
```

### timeout_ms

Timeout in milliseconds for racing and refinement operations (default: 30000).

```python
config = lc.Config(race_strategies=True, timeout_ms=10000)  # 10 second timeout
```

## Examples

### Neural Network Verification

For neural networks, use Dyadic for speed:

```python
import leancert as lc

# Neural network expression (deep computation graph)
net_output = build_network_expr(weights, biases)

# Dyadic is 10-100x faster than rational for deep expressions
config = lc.Config.dyadic()
result = lc.find_bounds(net_output, input_domain, config=config)
```

### Transformer LayerNorm

For transformers with LayerNorm, use Affine for tight bounds:

```python
import leancert as lc

# LayerNorm has correlated mean/variance computation
layernorm_expr = build_layernorm_expr(x, gamma, beta)

# Affine arithmetic tracks correlations
config = lc.Config.affine()
result = lc.find_bounds(layernorm_expr, input_domain, config=config)
```

### High-Precision Proofs

For formal proofs requiring maximum precision:

```python
import leancert as lc

config = lc.Config.high_precision()
result = lc.find_bounds(expr, domain, config=config)

# Export certificate for Lean verification
result.certificate.save("proof.json")
```

### Custom Configuration

```python
from fractions import Fraction
import leancert as lc

config = lc.Config(
    taylor_depth=15,           # More Taylor terms
    max_iters=2000,            # More optimization iterations
    tolerance=Fraction(1, 10000),  # Tighter tolerance
    use_monotonicity=True,     # Enable monotonicity pruning
    timeout_sec=120.0,         # 2 minute timeout
    backend=lc.Backend.DYADIC,
    dyadic_config=lc.DyadicConfig(precision=-80),
)

result = lc.find_bounds(expr, domain, config=config)
```

### Witness Synthesis with Racing

For complex expressions where you don't know the best backend:

```python
import leancert as lc

x = lc.var('x')
expr = lc.exp(x) * lc.sin(x)  # Unknown which backend is best

with lc.Solver() as solver:
    # Race all backends, use first to succeed
    config = lc.Config(race_strategies=True, timeout_ms=10000)
    result = solver.synthesize_min_witness(expr, {'x': (0, 3)}, config=config)

    print(f"Winner: {result.strategy_used}")
    print(f"Minimum witness: {result.witness_value}")
    print(result.to_lean_tactic())
```

### Incremental Refinement for Tight Bounds

Find the tightest provable bound through iterative refinement:

```python
import leancert as lc

x = lc.var('x')

with lc.Solver() as solver:
    # Find tightest provable upper bound for exp(x) on [0, 1]
    config = lc.Config(incremental_refinement=True)
    result = solver.synthesize_max_witness(lc.exp(x), {'x': (0, 1)}, config=config)

    print(f"Tightest bound: {float(result.witness_value):.6f}")
    print(f"Refinement steps: {len(result.refinement_history)}")
    for step in result.refinement_history:
        print(f"  {step['bound']:.6f} -> {step['status']}")
```

