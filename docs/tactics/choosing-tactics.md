# Choosing the Right Tactic

Quick reference for picking the right LeanCert tactic for a direct automation
goal.  For the overall proof-shape chooser, start with
[Choosing A Proof Shape](../choosing-proof-shape.md).

> **Having issues?** See the [Troubleshooting Guide](troubleshooting.md) for common errors and solutions.

## Decision Flowchart

```
What do you want to prove?
│
├─► "∀ x ∈ I, f(x) ≤ c" or "∀ x ∈ I, f(x) ≥ c"
│   │
│   ├─► Single variable? ──► certify_bound
│   │                        (or certify_kernel for kernel-only trust)
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
├─► "∃ m, ∀ x ∈ I, f(x) ≥ m" (find minimum)
│   │
│   ├─► Single variable? ──► interval_minimize
│   └─► Multiple variables? ──► interval_minimize_mv
│
├─► "∃ M, ∀ x ∈ I, f(x) ≤ M" (find maximum)
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
│   └─► interval_integrate
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
| Upper bound on interval | `certify_bound` | `∀ x ∈ Set.Icc 0 1, exp x ≤ 3` |
| Lower bound on interval | `certify_bound` | `∀ x ∈ Set.Icc 0 1, 0 ≤ exp x` |
| Bound with kernel-only trust | `certify_kernel` | Same goals, higher trust |
| Multivariate bound | `multivariate_bound` | `∀ x ∈ I, ∀ y ∈ J, x + y ≤ 2` |
| Function has no roots | `root_bound` | `∀ x ∈ I, x² + 1 ≠ 0` |
| Root exists | `interval_roots` | `∃ x ∈ I, x² - 2 = 0` |
| Unique root exists | `interval_unique_root` | `∃! x ∈ I, x² - 2 = 0` |
| Minimum exists | `interval_minimize` | `∃ m, ∀ x ∈ I, f x ≥ m` |
| Maximum exists | `interval_maximize` | `∃ M, ∀ x ∈ I, f x ≤ M` |
| Find the minimizer | `interval_argmin` | `∃ x ∈ I, ∀ y ∈ I, f x ≤ f y` |
| Find the maximizer | `interval_argmax` | `∃ x ∈ I, ∀ y ∈ I, f y ≤ f x` |
| Point inequality | `interval_decide` | `π < 3.15` |
| Disprove a bound | `interval_refute` | Find counterexample |
| Simplify vector indexing | `vec_simp` | `![a,b,c] ⟨1, h⟩ = b` |
| Expand finite sums | `finsum_expand` | `∑ k ∈ Icc 1 3, f k = f 1 + f 2 + f 3` |
| Integral bound | `interval_integrate` | `∫ x in a..b, f x ∈ I` |

## Trust Levels

| Tactic | Verification | When to use |
|--------|--------------|-------------|
| `certify_kernel` | `decide` (kernel-only) | Maximum trust, slower |
| `certify_bound` | `native_decide` | Good balance of trust/speed |
| `certify_kernel_quick` | `decide` (30 bits) | Fast, lower precision |
| `certify_kernel_precise` | `decide` (100 bits) | Tight bounds needed |

## Common Patterns

### "My bound is too tight and fails"

```lean
-- Try 1: Increase Taylor depth
example : ∀ x ∈ Set.Icc 0 1, exp x ≤ 2.72 := by certify_bound 20

-- Try 2: Use subdivision
example : ∀ x ∈ Set.Icc 0 1, exp x ≤ 2.72 := by interval_bound_subdiv 15 3

-- Try 3: Use higher precision dyadic
example : ∀ x ∈ Set.Icc 0 1, exp x ≤ 2.72 := by certify_kernel_precise
```

### "I don't know what bound to use"

Use discovery tactics to find bounds first:

```lean
-- Find the actual minimum/maximum
example : ∃ m, ∀ x ∈ Set.Icc 0 1, x^2 + sin x ≥ m := by interval_minimize
example : ∃ M, ∀ x ∈ Set.Icc 0 1, x^2 + sin x ≤ M := by interval_maximize
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
theorem exp_lower : ∀ x ∈ Set.Icc (0:ℝ) 1, 1 ≤ Real.exp x := by certify_bound
theorem exp_upper : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ 3 := by certify_bound

theorem exp_bounded : ∀ x ∈ Set.Icc (0:ℝ) 1, 1 ≤ Real.exp x ∧ Real.exp x ≤ 3 :=
  fun x hx => ⟨exp_lower x hx, exp_upper x hx⟩
```

### "Native syntax vs Expr AST"

Most tactics support native syntax, but some require Expr AST:

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

**When native syntax fails:** If you get unification errors with complex expressions (especially with numeric coefficients like `2 * x * x`), switch to Expr AST. See [Troubleshooting](troubleshooting.md) for details.

### "I have a sum over vectors/matrices"

Chain simplification tactics to reduce structured expressions before proving bounds:

```lean
-- Expand finite sum, simplify vector indexing, then close with ring
example (a : Fin 3 → ℝ) :
    ∑ k ∈ Finset.Icc 0 2, (![a 0, a 1, a 2] : Fin 3 → ℝ) ⟨k, by omega⟩ =
    a 0 + a 1 + a 2 := by
  finsum_expand; vec_simp
```

Common combinations:
- `finsum_expand; ring` — expand sum, simplify arithmetic
- `finsum_expand; vec_simp; ring` — expand sum, reduce vector indexing, simplify
- `vec_simp; certify_bound` — simplify indexing, then prove bounds
