# Choosing the Right Tactic

Quick reference for picking the right LeanCert tactic for a direct automation
goal.  For the overall proof-shape chooser, start with
[Choosing A Proof Shape](../choosing-proof-shape.md).

> **Having issues?** See the [Troubleshooting Guide](../direct/troubleshooting.md) for common errors and solutions.

For ordinary mathematical statements, start with `leancert`. The dedicated
tactics below remain useful when you want to force a particular solver, select
engine-specific parameters, or control the verification path.

## Decision Flowchart

```
What do you want to prove?
│
├─► A recognized bound, root, extremum, finite-sum, or integral theorem?
│   └─► leancert
│       └─► Need to inspect the selected solver? ──► leancert?
│
├─► Need explicit control for "∀ x ∈ I, f(x) ≤ c" or "∀ x ∈ I, f(x) ≥ c"?
│   │
│   ├─► Single variable? ──► certify_bound
│   │                        (add `(trust := kernel)` for kernel-only trust)
│   │
│   └─► Multiple variables? ──► multivariate_bound
│
├─► "∀ x ∈ I, f(x) ≠ 0"
│   └─► root_bound
│
├─► "∃ x ∈ I, f(x) = 0"
│   └─► interval_roots
│
├─► "∃! x ∈ I, f(x) = 0"
│   └─► interval_unique_root
│
├─► "∃ m, ∀ x ∈ I, f(x) ≥ m" (certify a global lower bound)
│   │
│   ├─► Single variable? ──► interval_minimize
│   └─► Multiple variables? ──► interval_minimize_mv
│
├─► "∃ M, ∀ x ∈ I, f(x) ≤ M" (certify a global upper bound)
│   │
│   ├─► Single variable? ──► interval_maximize
│   └─► Multiple variables? ──► interval_maximize_mv
│
├─► "∃ x ∈ I, ∀ y ∈ I, f(x) ≤ f(y)" (find argmin)
│   └─► interval_argmin
│
├─► "∃ x ∈ I, ∀ y ∈ I, f(y) ≤ f(x)" (find argmax)
│   └─► interval_argmax
│
├─► Point inequality (π < 3.15, etc.)
│   └─► interval_decide
│
├─► Integral bound
│   └─► leancert
│
├─► "∀ n ≥ N, q / n^k ≤ c" or "∃ N, ∀ n ≥ N, q / n^k ≤ c"
│   └─► leancert
│       └─► Need an explicit cutoff? ──► eventual_bound using N
│
├─► Simplify vector/matrix indexing (![a,b,c] ⟨1,h⟩ → b)
│   └─► vec_simp
│
└─► Expand finite sum (∑ k ∈ Icc 1 3, f k → f 1 + f 2 + f 3)
    └─► finsum_expand
```

## Quick Reference Table

| I want to prove... | Tactic | Example |
|-------------------|--------|---------|
| Any recognized mathematical goal | `leancert` | Bounds, roots, extrema, sums, and integrals |
| Upper bound on interval | `leancert` | `∀ x ∈ Set.Icc 0 1, exp x ≤ 3` |
| Lower bound on interval | `leancert` | `∀ x ∈ Set.Icc 0 1, 0 ≤ exp x` |
| Bound with explicit Taylor depth | `certify_bound` | Same goals, direct interval-engine control |
| Bound with kernel-only trust | `certify_bound (trust := kernel)` | Same solver, kernel-only certificate verification |
| Multivariate bound | `leancert` | `∀ x ∈ I, ∀ y ∈ J, x + y ≤ 2` |
| Function has no roots | `leancert` | `∀ x ∈ I, x² + 1 ≠ 0` |
| Root exists | `leancert` | `∃ x ∈ I, x² - 2 = 0` |
| Unique root exists | `leancert` | `∃! x ∈ I, x² - 2 = 0` |
| Global lower or upper bound exists | `leancert` | Existential bound theorem |
| Find the minimizer or maximizer | `leancert` | Argmin or argmax theorem |
| Point inequality | `leancert` | `π < 3.15` |
| Disprove a bound | `interval_refute` | Find counterexample |
| Simplify vector indexing | `vec_simp` | `![a,b,c] ⟨1, h⟩ = b` |
| Expand finite sums | `finsum_expand` | `∑ k ∈ Icc 1 3, f k = f 1 + f 2 + f 3` |
| Integral equality or inequality | `leancert` | `(∫ x in a..b, f x) ≤ c` |
| Eventual reciprocal-power bound | `leancert` | `∃ N, ∀ n ≥ N, 3 / n^2 ≤ 1/1000` |

## Trust Levels

Solver choice and certificate-verification trust are independent. Most
proof-producing tactics accept the same per-invocation trust item:

| Mode | Example | Verification |
|------|---------|--------------|
| `native` (repository default) | `certify_bound (trust := native)` | `native_decide`; trusts the compiler/runtime |
| `kernel` | `certify_bound (trust := kernel)` | `decide +kernel`; never silently falls back |
| `auto` | `certify_bound (trust := auto)` | Kernel first for suitably sized certificates; reported native fallback |

The effective default is the scoped `leancert.trust` option, whose repository
default is `native`. Use `set_option leancert.trust "kernel"` to select a mode
for a whole section or file. A per-invocation `(trust := ...)` item takes
precedence.

## Common Patterns

### "My bound is too tight and fails"

```lean
-- Try 1: Increase Taylor depth
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by certify_bound 20

-- Try 2: Use subdivision
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by interval_bound_subdiv 15 3

-- Try 3: Increase depth while requiring kernel-only certificate verification
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound 20 (trust := kernel)
```

### "I don't know what bound to use"

Use discovery tactics to find bounds first:

```lean
-- Discover and certify global lower/upper bounds
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + Real.sin x ≥ m := by
  interval_minimize
example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + Real.sin x ≤ M := by
  interval_maximize
```

Or use interactive commands:

```lean
import LeanCert.Discovery.Commands

#find_min (fun x => x^2 + Real.sin x) on [0, 1]
#find_max (fun x => x^2 + Real.sin x) on [0, 1]
```

### "I want to prove both upper and lower bounds"

Prove them separately and combine:

```lean
theorem exp_lower : ∀ x ∈ Set.Icc (0:ℝ) 1, 1 ≤ Real.exp x := by leancert
theorem exp_upper : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ 3 := by leancert

theorem exp_bounded : ∀ x ∈ Set.Icc (0:ℝ) 1, 1 ≤ Real.exp x ∧ Real.exp x ≤ 3 :=
  fun x hx => ⟨exp_lower x hx, exp_upper x hx⟩
```

### "Dedicated tactic syntax vs Expr AST"

When selecting a dedicated tactic directly, most support native syntax, but
some also expose or require the reflected Expr AST:

| Tactic | Native Syntax | Expr AST |
|--------|---------------|----------|
| `certify_bound` | ✓ Recommended | ✓ Supported |
| `multivariate_bound` | ✓ Recommended | ✓ Supported |
| `interval_minimize/maximize` | ✓ Recommended | ✓ Supported |
| `interval_roots` | ✓ Supported | ✓ Works well |
| `root_bound` | ✓ Supported | ✓ Works well |
| `interval_le/ge` (low-level) | ✗ | ✓ Required |

**Native syntax (recommended when it works):**
```lean
example : ∀ x ∈ Set.Icc (0:ℝ) 1, x * x ≤ 1 := by certify_bound
example : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ 3 := by certify_bound 15
```

**Expr AST syntax (more control, always works):**
```lean
open LeanCert.Core in
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

open LeanCert.Core in
example : ∀ x ∈ I01, Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ≤ (1 : ℚ) := by
  certify_bound
```

**When native syntax fails:** If you get unification errors with complex expressions (especially with numeric coefficients like `2 * x * x`), switch to Expr AST. See [Troubleshooting](../direct/troubleshooting.md) for details.

### "I have a sum over vectors/matrices"

Chain simplification tactics to reduce structured expressions before proving bounds:

```lean
-- Expand finite sum, simplify vector indexing, then close with ring
example (a : Fin 3 → ℝ) :
    ∑ k : Fin 3, (![a 0, a 1, a 2] : Fin 3 → ℝ) k =
    a 0 + a 1 + a 2 := by
  finsum_expand
```

Common combinations:
- `finsum_expand; ring` — expand sum, simplify arithmetic
- `finsum_expand; vec_simp; ring` — expand sum, reduce vector indexing, simplify
- `vec_simp; leancert` — simplify indexing, then prove the resulting mathematical goal
