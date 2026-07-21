# Checked Automatic Differentiation

LeanCert can compute certified interval enclosures for partial derivatives of
`Expr` programs. The checked APIs validate expression support, analytic domain
conditions, and backend configuration before returning an enclosure. A
successful result therefore needs no separate support or domain hypothesis in
the corresponding Golden Theorem.

```lean
import LeanCert

open LeanCert
open LeanCert.Core LeanCert.Engine

def input : IntervalRat := ⟨1, 2, by norm_num⟩
def rho : Nat → IntervalRat := fun _ => input

-- x ↦ log (1 / (x + 1))
def f : Expr := .log (.inv (.add (.var 0) (.const 1)))

-- Constructor arguments: precision, then Taylor depth.
def dyadicAD : DyadicConfig := .mk (-53) 10

#eval derivIntervalChecked f rho 0
#eval derivIntervalDyadicCheckedOfRat f rho 0 dyadicAD
```

Both calls return `EvalResult`: `.ok enclosure` means the derivative is
certified to lie in that interval, while `.error reason` explains why no
certificate was produced. The Dyadic result has type `IntervalDyadic`; use
`result.toIntervalRat` when rational endpoints are more convenient for display
or downstream code.

## Choosing an entry point

Checked AD currently uses explicit backend entry points. The backend selector
in `EvalOptions` applies to ordinary interval evaluation and does not select an
AD backend.

| Need | Entry point | Result |
|---|---|---|
| One partial, Rational input and arithmetic | `derivIntervalChecked` | `IntervalRat` |
| One-variable shorthand, Rational arithmetic | `derivIntervalChecked1` | `IntervalRat` |
| Value and one partial, Rational arithmetic | `evalWithDerivChecked` | `DualInterval` |
| All coordinates of a list-backed Rational box | `gradientIntervalChecked` | `List IntervalRat` |
| One partial, native Dyadic input | `derivIntervalDyadicChecked` | `IntervalDyadic` |
| One-variable shorthand, native Dyadic input | `derivIntervalDyadicChecked1` | `IntervalDyadic` |
| One partial, Rational input converted outward | `derivIntervalDyadicCheckedOfRat` | `IntervalDyadic` |
| One-variable Rational-input shorthand using Dyadic arithmetic | `derivIntervalDyadicChecked1OfRat` | `IntervalDyadic` |
| First `n` partials using Dyadic arithmetic | `gradientIntervalDyadicChecked` or `gradientIntervalDyadicCheckedOfRat` | `List IntervalDyadic` |
| Value and one partial, Dyadic arithmetic | `evalWithDerivDyadicChecked` | `DualIntervalDyadic` |

For `deriv... e rho idx`, `idx` is the variable coordinate being
differentiated. `gradientIntervalDyadicChecked... e rho n` computes coordinates
`0, …, n - 1`; the Golden Theorem preserves that alignment with `List.Forall₂`.
The Rational `gradientIntervalChecked` instead takes a list-backed `Box` and
uses its length.

Use Rational AD for small or shallow expressions and when a rational result is
the most useful boundary. Use Dyadic AD for deeper arithmetic expressions where
exact rational denominators grow. Dyadic addition and multiplication round
outward after each operation, bounding endpoint denominator size. Its
transcendental enclosures still use LeanCert's verified Rational Taylor kernels
before conversion back to Dyadic endpoints.

The `OfRat` functions are usually the easiest Dyadic boundary. They convert the
input box outward at `cfg.precision`, and that containment proof is already
included in their Golden Theorems. Native Dyadic environments are useful when a
larger pipeline already uses `IntervalDyadic`.

## Using the Golden Theorem

The computational equality is the certificate. The theorem below turns any
successful Rational-input Dyadic computation into a statement about the real
derivative:

```lean
import LeanCert

open LeanCert
open LeanCert.Core LeanCert.Engine

def input : IntervalRat := ⟨1, 2, by norm_num⟩
def rho : Nat → IntervalRat := fun _ => input
def f : Expr := .log (.inv (.add (.var 0) (.const 1)))
def cfg : DyadicConfig := .mk (-53) 10

example (dI : IntervalDyadic) (x : ℝ) (hx : x ∈ input)
    (hok : derivIntervalDyadicCheckedOfRat f rho 0 cfg = .ok dI) :
    deriv (Expr.evalAlong f (fun _ => x) 0) x ∈ dI := by
  apply derivIntervalDyadicCheckedOfRat_correct
    f (fun _ => x) rho 0 cfg dI x hx
  · intro i
    exact hx
  · exact hok
```

There are matching Golden Theorems for each boundary:

- `derivIntervalChecked_correct` and
  `derivIntervalDyadicChecked_correct` for one partial;
- `gradientIntervalChecked_correct` and
  `gradientIntervalDyadicChecked_correct` for gradients;
- `derivIntervalDyadicCheckedOfRat_correct` and
  `gradientIntervalDyadicCheckedOfRat_correct` for Rational-input Dyadic calls;
- `evalWithDerivChecked_differentiableAt` and
  `evalWithDerivDyadicChecked_differentiableAt` when the differentiability fact
  itself is needed;
- `evalWithDerivChecked_der_correct` and
  `evalWithDerivDyadicChecked_der_correct` when both value and derivative
  enclosures are retained.

## Domains, errors, and supported syntax

Checked AD supports:

```text
const, var, add, mul, neg, inv, exp, sin, cos, log
```

Support is recursive, so these operations may be nested. `inv a` is accepted
only when interval evaluation proves that `a` excludes zero. `log a` is
accepted only when it proves that `a` is strictly positive. These checks apply
to the whole input box, not just to a sampled point.

Failures are structured `EvalError` values. In particular:

- reciprocal domains containing zero return `reciprocalContainsZero`;
- nonpositive logarithm domains return `logNonpositive`;
- a failure inside another operation is reported as `nestedFailure`;
- syntax outside the fragment returns `unsupportedFeature`;
- Dyadic `precision > 0` returns `invalidConfiguration`.

The rejected result is not a weak or unbounded certificate. Callers must refine
the input box, choose supported syntax, or handle the error explicitly.

The Dyadic `precision` is a binary exponent and must be nonpositive. More
negative values retain finer outward-rounded endpoints. `taylorDepth` controls
the verified transcendental approximations; increasing it may tighten results
at additional cost.

## Measuring the crossover

Backend performance depends on expression shape and depth. LeanCert's compiled
AD benchmark contains checked Rational and Dyadic cases for both a small
`inv`/`log` expression and a depth-60 denominator-growth workload:

```sh
lake build leancert-bench
lake exe leancert-bench --suite ad --samples 15 --warmups 3 --format markdown
```

Tiny expressions can favor Rational arithmetic because Dyadic conversion and
rounding have fixed overhead. The deep case is the useful regression for the
bounded-denominator backend; benchmark the workload that resembles the target
application rather than relying on a universal cutoff.
