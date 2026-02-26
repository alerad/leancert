# Adaptive Verification

!!! info "Repository split"
    Canonical Python SDK docs now live in **`alerad/leancert-python`**:
    https://github.com/alerad/leancert-python

    Bridge/runtime release docs live in **`alerad/leancert-bridge`**:
    https://github.com/alerad/leancert-bridge

    This page is kept here as reference.

The `adaptive` module provides domain splitting strategies and proof assembly for verifying complex expressions that fail on the full domain.

## Overview

When interval arithmetic over a large domain produces bounds that are too loose, **adaptive verification** splits the domain into smaller regions, verifies each independently, and assembles a combined proof.

```python
import leancert as lc
from leancert.adaptive import verify_bound_adaptive

x = lc.var('x')
with lc.Solver() as solver:
    # May need splitting to prove tight bound
    result = verify_bound_adaptive(
        solver,
        lc.sin(x) * lc.cos(x),
        {'x': (0, 6.28)},
        upper=0.5
    )

    print(result.verified)      # True
    print(result.total_splits)  # Number of domain splits needed
    print(result.lean_proof)    # Combined Lean proof
```

## When to Use Adaptive Verification

Use adaptive verification when:

1. **Tight bounds fail** - The expression's true range is close to the bound you're proving
2. **Large domains** - Interval arithmetic accumulates overestimation over wide intervals
3. **Oscillating functions** - Functions like `sin`, `cos` need subdivision to capture behavior
4. **Near-boundary behavior** - Values approach the bound only in small regions

## Function API

```python
from leancert.adaptive import verify_bound_adaptive, AdaptiveConfig, SplitStrategy

result = verify_bound_adaptive(
    solver,           # lc.Solver instance
    expr,             # Expression to verify
    domain,           # {'x': (lo, hi)} or Box
    upper=None,       # Upper bound to prove
    lower=None,       # Lower bound to prove
    adaptive_config=AdaptiveConfig(),  # Splitting configuration
    solver_config=lc.Config()          # Interval arithmetic config
)
```

## Splitting Strategies

Configure the splitting strategy via `AdaptiveConfig`:

```python
from leancert.adaptive import AdaptiveConfig, SplitStrategy

# Bisection - splits domain in half
config = AdaptiveConfig(strategy=SplitStrategy.BISECT)

# Worst-point guided (default) - splits where bound is nearly violated
config = AdaptiveConfig(strategy=SplitStrategy.WORST_POINT)

# Gradient-guided - uses derivative info to guide splits
config = AdaptiveConfig(strategy=SplitStrategy.GRADIENT_GUIDED)

# Largest-first - splits largest subdomain first
config = AdaptiveConfig(strategy=SplitStrategy.LARGEST_FIRST)

# Algebraic - splits at roots/critical points
config = AdaptiveConfig(strategy=SplitStrategy.ALGEBRAIC)

# Auto - automatically selects best strategy
config = AdaptiveConfig(strategy=SplitStrategy.AUTO)
```

## Configuration

```python
from leancert.adaptive import AdaptiveConfig, SplitStrategy

config = AdaptiveConfig(
    max_splits=64,              # Maximum number of domain splits
    max_depth=10,               # Maximum recursion depth
    strategy=SplitStrategy.WORST_POINT,  # Splitting strategy
    parallel=True,              # Verify subdomains in parallel
    max_workers=None,           # Number of parallel workers (None=auto)
    min_width=1e-10,            # Stop subdividing below this width
    min_volume=None,            # Stop subdividing below this volume
    timeout_per_subdomain_ms=10000,  # Timeout per subdomain
    compute_gradients=False,    # Compute gradients for guided splitting
)

result = verify_bound_adaptive(
    solver, expr, domain, upper=bound,
    adaptive_config=config
)
```

## Multivariate Domains

For multivariate functions, splitting occurs along all dimensions:

```python
x, y = lc.var('x'), lc.var('y')
expr = x**2 + y**2 - x*y

result = verify_bound_adaptive(
    solver,
    expr,
    {'x': (-1, 1), 'y': (-1, 1)},
    upper=3.0
)

print(result.total_splits)  # May split into multiple regions
```

## Result Structure

The `AdaptiveResult` contains:

```python
@dataclass
class AdaptiveResult:
    verified: bool                    # Whether the bound was proven
    subdomains: list[Subdomain]       # All subdomains considered
    results: list[SubdomainResult]    # Results per subdomain
    total_splits: int                 # Total number of splits
    failing_subdomain: Optional[Subdomain]  # First failing region (if any)
    lean_proof: Optional[str]         # Combined Lean proof
    certificate: Optional[Certificate] # Verification certificate
    total_time_ms: float              # Total verification time
    unverified_volume: float          # Volume of unverified regions
```

## Proof Assembly

After verifying all subdomains, proofs are assembled:

```python
result = verify_bound_adaptive(solver, expr, domain, upper=bound)

# Access the combined Lean proof
print(result.lean_proof)
# Output:
# -- CEGAR-generated proof via domain splitting
# -- Expression: ...
# -- Bound: upper â‰¤ ...
# -- Verified in N subdomains
# apply union_bound_of_subdomains
# ...
```

## Convenience Function

For quick use, there's also a module-level function:

```python
import leancert as lc

x = lc.var('x')
result = lc.verify_bound_adaptive(
    solver, lc.exp(x), {'x': (0, 2)}, upper=8.0
)
```

## Performance Tips

1. **Start with low `max_splits`** - Increase only if verification fails
2. **Use `WORST_POINT` strategy** for tight bounds (default)
3. **Use `ALGEBRAIC` strategy** for functions with known critical points
4. **Enable `parallel=True`** for large domains (default)
5. **Check `result.total_splits`** - High counts suggest the bound is too tight

## See Also

- [Quantifier Synthesis](quantifier.md) - High-level synthesis using adaptive verification
- [Solver API](solver.md) - Low-level verification methods
- [Troubleshooting](../troubleshooting.md) - Common verification failures

