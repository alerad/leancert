# LeanBound

Verified numerical computation and bound certification for Lean 4.

LeanBound automates proofs of inequalities, global extrema, root existence, and integration bounds using rigorous interval arithmetic and Taylor models. Unlike standard numerical libraries that provide approximations, LeanBound produces formal proofs.

## Overview

LeanBound operates on a certificate-driven architecture:

1. **Reification**: Mathematical expressions are converted to an AST (`LeanBound.Core.Expr`)
2. **Computation**: Algorithms run on the AST using rational interval arithmetic
3. **Certification**: Golden theorems lift boolean results to semantic proofs about real numbers

This separation allows efficient computation while maintaining full formal verification.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "leanbound"
git = "https://github.com/yale/leanbound"
rev = "main"
```

Then run `lake update`.

## Usage

### Tactics

```lean
import LeanBound.Tactic.Interval

-- Prove upper bounds (dispatches to interval_le, interval_ge, etc.)
example : ∀ x ∈ Set.Icc 0 1, x^2 + Real.sin x ≤ 2 := by
  interval_bound

-- Prove root existence (√2)
example : ∃ x ∈ Set.Icc 1 2, x^2 - 2 = 0 := by
  interval_roots

-- Prove root uniqueness via Newton contraction
example : ∃! x ∈ Set.Icc 1 2, x^2 - 2 = 0 := by
  interval_unique_root
```

### Direct API

```lean
import LeanBound.Numerics.Certificate

-- Using the certificate API directly
theorem exp_bounded : ∀ x ∈ Icc 0 1, Real.exp x ≤ 3 :=
  verify_upper_bound exprExp exprExp_core I01 3 (by native_decide)
```

### Discovery Commands

Interactive commands for exploration (use in editor, not in proofs):

```lean
import LeanBound.Discovery

-- Find global minimum
#minimize (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior
#explore (Expr.cos (Expr.var 0)) on [0, 4]
```

For use in proofs, use the corresponding tactics: `interval_minimize`, `interval_maximize`.

## Architecture

### Expression AST

`LeanBound.Core.Expr` supports:
- Arithmetic: `const`, `var`, `add`, `mul`, `neg`, `inv`
- Transcendentals: `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `atan`, `arsinh`, `atanh`
- Special functions: `sinc`, `erf`

Note: While the AST supports all these operations, automated verification is tiered. Not all functions are supported by all tactics or correctness theorems.

### Computability Tiers

- **`ExprSupportedCore`**: Fully computable subset (`const`, `var`, `add`, `mul`, `neg`, `sin`, `cos`, `exp` via Taylor models). Enables `native_decide` proofs.
- **`ExprSupported`**: Non-computable counterpart to `ExprSupportedCore` that uses `Real.exp` directly for theoretical proofs.
- **`ExprSupportedWithInv`**: Most general predicate, including partial functions (`inv`, `log`, `atan`, `arsinh`, `atanh`, `sinc`, `erf`). Verification requires `evalInterval?` which may fail if domain constraints are not met.

### Golden Theorems

These bridge computation and proof. If the checker returns `true`, the theorem holds.

| Goal | Theorem | Checker |
|------|---------|---------|
| Upper bound | `verify_upper_bound` | `checkUpperBound` |
| Lower bound | `verify_lower_bound` | `checkLowerBound` |
| Root existence | `verify_sign_change` | `checkSignChange` |
| Root uniqueness | `verify_unique_root_core` | `checkNewtonContracts` |
| Integration | `verify_integral_bound` | `checkIntegralBoundsCore` |
| Global minimum | `verify_global_lower_bound` | `checkGlobalLowerBound` |

### Numerics Engine

- `evalIntervalCore`: Interval evaluation with Taylor models
- `globalMinimizeCore`: Branch-and-bound optimization
- `bisectRoot`: Root isolation via sign changes
- `newtonStepTM`: Interval Newton for uniqueness proofs
- `integrateInterval`: Riemann sum bounds

## Python SDK

LeanBound includes a Python SDK for integration with external tools.

### Installation

```bash
cd python
pip install -e .
```

### Usage

```python
import leanbound as lf

# Define expressions with named variables
x = lf.var('x')
expr = x**2 + lf.sin(x)

# Find bounds on an interval
result = lf.find_bounds(expr, {'x': (0, 1)})
print(result.min_bound, result.max_bound)

# Find roots
roots = lf.find_roots(x**2 - 2, {'x': (1, 2)})

# Verify a bound
verified = lf.verify_bound(expr, {'x': (0, 1)}, upper=2)
```

### Features

- **Named symbolic variables**: No De Bruijn indices; use `var('x')` directly
- **Automatic domain inference**: Box constraints derived from expression structure
- **Symbolic simplification**: Mitigates the dependency problem in interval arithmetic (e.g., `x - x` simplifies to `0` before evaluation, avoiding spurious width)
- **Adaptive verification**: `verify_bound(method='adaptive')` uses global optimization and counterexample concretization to filter false positives
- **Certificate generation**: Results include `certificate.to_lean_tactic()` for generating formal Lean proofs from Python

## Lean Bridge

`LeanBound.Bridge` provides a JSON-RPC interface over stdin/stdout:

```json
{"method": "eval_interval", "params": {"expr": "x^2", "box": [[0, 1]]}}
{"method": "global_min", "params": {"expr": "x^2 + sin(x)", "box": [[-2, 2]]}}
```

This enables workflows where Python handles search strategy while Lean provides verified computation.

## Verification Status

### Fully Verified

The following have complete proofs with no `sorry`:

- Interval arithmetic (FTIA) for `+`, `-`, `*`, `/`, `^`
- Transcendental bounds: `exp`, `sin`, `cos`, `log`, `sinh`, `cosh`, `tanh`, `atan`, `arsinh`
- Taylor series remainder bounds for `exp`, `sin`, `cos`
- Forward-mode automatic differentiation
- Global optimization (`globalMinimize_lo_correct`, `globalMaximize_hi_correct`)
- Root finding: bisection (existence) and Newton (uniqueness)
- Integration bounds (`integrateInterval_correct`)

### Incomplete

These work computationally but have proof gaps:

| Component | Issue |
|-----------|-------|
| `atanh` interval | Fallback path uses `sorry`; Taylor model path is verified |
| `atanh` Taylor remainder | `atanh_series_remainder_bound` incomplete |
| `log` Taylor model | `tmLog_correct` incomplete; basic interval verified |
| `sinc`, `erf` derivatives | Missing differentiability proofs in AD |

To find all `sorry` occurrences:

```bash
grep -r "sorry" --include="*.lean" LeanBound/ | grep -v "no sorry"
```

## Contributing

Priority areas:

1. Filling `sorry` gaps (especially `atanh` Taylor remainder, `tmLog_correct`)
2. Additional functions (`asin`, `acos`, real powers)
3. Subdivision strategies for optimization
4. Documentation and examples

Open an issue before starting major work.

## License

Apache 2.0
