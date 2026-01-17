# Configuration

LeanCert supports multiple arithmetic backends for different performance/precision tradeoffs.

## Backend Selection

```python
import leancert as lc

# Default: Exact rational arithmetic
result = lc.find_bounds(expr, domain)

# Dyadic: 10-100x faster for deep expressions
result = lc.find_bounds(expr, domain, config=lc.Config.dyadic())

# Affine: 50-90% tighter bounds for correlated variables
result = lc.find_bounds(expr, domain, config=lc.Config.affine())
```

## Backend Enum

::: leancert.config.Backend
    options:
      show_root_heading: true

### Comparison

| Backend | Speed | Precision | Best For |
|---------|-------|-----------|----------|
| `RATIONAL` | Baseline | Exact | Small expressions, proofs |
| `DYADIC` | 10-100x faster | ~15 decimal digits | Neural networks, deep expressions |
| `AFFINE` | Similar to Rational | Tighter bounds | Repeated variables, LayerNorm |

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
