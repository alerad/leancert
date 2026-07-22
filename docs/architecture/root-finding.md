# Root Finding Algorithms

LeanCert provides verified root finding with proofs of existence and uniqueness.

## Overview

| Algorithm | Proves | Method | Tactic |
|-----------|--------|--------|--------|
| Bisection | Existence | Sign change + IVT | `interval_roots` |
| Newton Contraction | Uniqueness | Fixed-point theorem | `interval_unique_root` |
| Norm-form Krawczyk | Existence + uniqueness for square differentiable systems | Interval Jacobian + Banach | certificate API |
| Bézout derivative | Global simplicity of all roots of a rational polynomial | Exact identity `A P + B P' = c ≠ 0` | certificate API |
| Discriminant count | Uniform 1-or-3 real-root count for cubic coefficient families | Interval sign of leading coefficient and discriminant, with adaptive subdivision | certificate API |

The Bézout layer is algebraic rather than isolating: it proves that roots are
simple globally. Its `QPoly.toExpr` bridge lets that fact compose with the
interval algorithms below. See
[Algebraic Root Certificates](../certificates/algebraic-roots.md).

The discriminant layer is global rather than isolating. Its coefficients may
be `Expr` families over a parameter box, and its subdivision checker resolves
interval dependency by proving the same strict sign on every child box.

## Nonlinear Systems (Krawczyk)

For a square system `F : Fin n → Expr` in LeanCert's `ADSupported` fragment,
LeanCert can check an untrusted rational center `m` and rational preconditioner
`Y`. It computes an interval Jacobian on the box, bounds the infinity operator
norm of `I - Y J(X)`, and checks a strict self-map enclosure. A successful check
certifies exactly one real root in the box.

```lean
import LeanCert.Validity.Krawczyk

open LeanCert.Core LeanCert.Engine LeanCert.Validity

example (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (cert : KrawczykCert n)
    (h : krawczykCheck F X cert = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  exact verify_unique_system_root F X cert {} h
```

`KrawczykCert` is dimension-safe: malformed vector and matrix shapes cannot be
constructed. The checker accepts constants, variables, addition,
multiplication, negation, `sin`, `cos`, and `exp`. It uses a strong norm-form
condition, which is sometimes more conservative than the componentwise
textbook Krawczyk operator but gives a direct Banach proof.

Three golden theorems expose the same successful check in the common goal
shapes: `verify_system_root_exists`, `verify_system_root_unique`, and
`verify_unique_system_root`.

### Current limits

- Systems must be square and use the `ADSupported` expression fragment.
- Boxes, centers, and preconditioners use exact rational data.
- The norm-form enclosure is intentionally conservative; a rejected
  certificate is inconclusive.
- LeanCert checks but does not currently generate the approximate center or
  inverse-Jacobian preconditioner. Those remain untrusted frontend/CAS data.
- The theorem is over real boxes. Complex systems must first be represented as
  coupled real and imaginary coordinates.

## Bisection (Existence)

### How It Works

1. Evaluate f at interval endpoints
2. If signs differ, IVT guarantees a root exists
3. Recursively bisect to narrow the interval

```
f(a) < 0                    f(b) > 0
  ●━━━━━━━━━━━━━━━━━━━━━━━━━●
  a          root          b
             somewhere
             in here
```

### The Theorem

```lean
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (hcont : ContinuousOn (Expr.eval e) (Set.Icc I.lo I.hi))
    (I : IntervalRat) (cfg : EvalConfig)
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0
```

**Key insight**: The checker `checkSignChange` is computable (runs via `native_decide`), while the conclusion is a semantic statement about real numbers.

### Usage

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Prove √2 exists (root of x² - 2)
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Algorithm Details

```
bisectRoot(f, [a, b], depth):
  if depth = 0:
    return [a, b] if sign_change(f, a, b) else ∅

  mid = (a + b) / 2
  roots = []

  if sign_change(f, a, mid):
    roots += bisectRoot(f, [a, mid], depth - 1)

  if sign_change(f, mid, b):
    roots += bisectRoot(f, [mid, b], depth - 1)

  return roots
```

### Limitations

- Only finds roots where sign changes (misses tangent roots like x² at 0)
- Requires continuity (cannot handle discontinuous functions)
- Multiple roots in interval returns multiple candidate intervals

---

## Newton Contraction (Uniqueness)

### How It Works

The Newton operator is:

\\[
N(x) = x - \frac{f(x)}{f'(x)}
\\]

If we can show:
1. N maps interval I into itself: N(I) ⊆ I
2. N is a contraction: |N'(x)| < 1 for all x ∈ I

Then Banach fixed-point theorem guarantees exactly one root in I.

### The Theorem

```lean
theorem newton_contraction_unique_root (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_maps_into : newtonInterval e I cfg ⊆ I)
    (h_contracts : ∀ x ∈ I, |newtonDerivative e x cfg| < 1) :
    ∃! x ∈ I, Expr.eval (fun _ => x) e = 0
```

### Usage

```lean
import LeanCert.Tactic.Discovery

-- Prove x² - 2 has exactly one root in [1, 2]
example : ∃! x ∈ I12, Expr.eval (fun _ => x) expr_x2_minus_2 = 0 := by
  interval_unique_root
```

### Contraction Verification

To verify contraction, we bound |N'(x)|:

\\[
N'(x) = 1 - \frac{f'(x)^2 - f(x) \cdot f''(x)}{f'(x)^2} = \frac{f(x) \cdot f''(x)}{f'(x)^2}
\\]

Using interval arithmetic:
1. Compute interval bounds on f(I), f'(I), f''(I)
2. Check if |f(I) · f''(I)| / |f'(I)|² < 1

### Algorithm Details

```
checkNewtonContracts(f, I):
  # Compute function and derivatives on interval
  f_I   = evalInterval(f, I)
  f'_I  = evalInterval(derivative(f), I)
  f''_I = evalInterval(derivative(derivative(f)), I)

  # Check f' doesn't contain 0 (otherwise N undefined)
  if 0 ∈ f'_I:
    return false

  # Compute Newton image
  N_I = I - f_I / f'_I

  # Check maps into
  if not (N_I ⊆ I):
    return false

  # Check contraction (|N'| < 1)
  N'_bound = |f_I * f''_I| / (f'_I)²
  return N'_bound.hi < 1
```

### Refinement

Once uniqueness is established, Newton iteration refines the root location:

```lean
def newtonRefine (e : Expr) (I : IntervalRat) (n : ℕ) : IntervalRat :=
  match n with
  | 0 => I
  | n + 1 => newtonRefine e (newtonStep e I) n
```

Each iteration roughly doubles the number of correct digits.

---

## Comparison

| Aspect | Bisection | Newton |
|--------|-----------|--------|
| Proves | Existence | Uniqueness |
| Requires | Sign change | f' ≠ 0, contraction |
| Convergence | Linear | Quadratic |
| Multiple roots | Finds all (with sign change) | Finds one |
| Tangent roots | Misses | Can verify if f' ≠ 0 nearby |

## Combined Workflow

For full root verification:

```lean
-- 1. First prove existence
have h_exists : ∃ x ∈ I, f x = 0 := by interval_roots

-- 2. Then prove uniqueness (if needed)
have h_unique : ∃! x ∈ I, f x = 0 := by interval_unique_root

-- 3. Optionally refine location
-- The unique root is in a very narrow interval
```

## Mean Value Theorem Bounds

The `MVTBounds` module provides additional tools:

```lean
-- If f' is bounded on [a,b], then f(b) - f(a) is bounded
theorem mvt_bound (f : ℝ → ℝ) (a b : ℝ) (M : ℝ)
    (h_diff : DifferentiableOn ℝ f (Set.Icc a b))
    (h_bound : ∀ x ∈ Set.Icc a b, |f' x| ≤ M) :
    |f b - f a| ≤ M * |b - a|
```

This is used internally for:
- Bounding how much f can change between sample points
- Verifying monotonicity
- Lipschitz constant estimation

## Files

| File | Description |
|------|-------------|
| `Engine/RootFinding/Basic.lean` | Core predicates (`signChange`, `excludesZero`) |
| `Engine/RootFinding/Bisection.lean` | Bisection algorithm |
| `Engine/RootFinding/Contraction.lean` | Newton contraction verification |
| `Engine/RootFinding/MVTBounds.lean` | Mean value theorem utilities |
| `Engine/RootFinding/Krawczyk.lean` | Nonlinear-system checker and soundness bridge |
| `Validity/Krawczyk.lean` | Stable golden theorem |
| `Tactic/Discovery.lean` | `interval_roots`, `interval_unique_root` tactics |
