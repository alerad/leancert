# LeanBound

**Verified numerical computation and bound certification for Lean 4.**

LeanBound automates proofs of inequalities, global extrema, root existence, and integration bounds using rigorous interval arithmetic and Taylor models. Unlike standard numerical libraries that provide approximations, LeanBound produces **formal proofs**.

## Key Features

- **Rigorous Interval Arithmetic**: Computable bounds with formal correctness proofs
- **Global Optimization**: Branch-and-bound with verified lower/upper bounds
- **Root Finding**: Existence proofs (bisection) and uniqueness proofs (Newton contraction)
- **Integration**: Verified Riemann sum bounds
- **Python SDK**: High-level API with symbolic simplification and false-positive filtering

## Quick Example

### Python

```python
import leanbound as lf

x = lf.var('x')
expr = x**2 + lf.sin(x)

# Find rigorous bounds on [0, 1]
result = lf.find_bounds(expr, {'x': (0, 1)})
print(f"Bounds: [{result.min_bound}, {result.max_bound}]")

# Prove root existence
roots = lf.find_roots(x**2 - 2, {'x': (1, 2)})
```

### Lean

```lean
import LeanBound.Tactic.Interval

-- Prove upper bounds automatically
example : ∀ x ∈ Set.Icc 0 1, x^2 + Real.sin x ≤ 2 := by
  interval_bound

-- Prove root existence (√2)
example : ∃ x ∈ Set.Icc 1 2, x^2 - 2 = 0 := by
  interval_roots

-- Prove root uniqueness via Newton contraction
example : ∃! x ∈ Set.Icc 1 2, x^2 - 2 = 0 := by
  interval_unique_root
```

## Architecture

LeanBound operates on a **certificate-driven architecture**:

1. **Reification**: Mathematical expressions are converted to an AST (`LeanBound.Core.Expr`)
2. **Computation**: Algorithms run on the AST using rational interval arithmetic
3. **Certification**: Golden theorems lift boolean results to semantic proofs about real numbers

This separation allows efficient computation while maintaining full formal verification.

## Installation

### Lean

Add to your `lakefile.toml`:

```toml
[[require]]
name = "leanbound"
git = "https://github.com/yale/leanbound"
rev = "main"
```

### Python

```bash
cd python
pip install -e .
```

## What's Verified?

The core interval arithmetic, Taylor series bounds, global optimization, root finding, and integration are **fully proved** with no `sorry`. See [Verification Status](architecture/verification-status.md) for details.
