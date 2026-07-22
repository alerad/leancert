# Algebraic Root Certificates

LeanCert can check an exact Bézout identity

$$
A P + B P' = c, \qquad c \ne 0,
$$

and conclude that the rational polynomial $P$ is separable. Consequently,
$P$ is squarefree, is coprime to its derivative, and every real root of $P$
is simple.

This is a global algebraic certificate. It does not require a search interval
or approximate roots, and it complements the interval Newton and Krawczyk
APIs. This first algebraic layer certifies simplicity; it does not yet count
or isolate roots.

## Executable representation

The checker uses `QPoly`, an exact executable polynomial represented by an
`Array ℚ` in ascending coefficient order:

```lean
def cubic : QPoly := ⟨#[-2, 0, 0, 1]⟩  -- x³ - 2
```

Mathlib's `Polynomial ℚ` remains the semantic representation. The one-way
lemmas `QPoly.toPoly_add`, `toPoly_mul`, `toPoly_derivative`, and
`toPoly_trim` transport a successful array computation to Mathlib. No
injectivity or normalization theorem is trusted by the checker.

## Complete example

For $P=x^3-2$, the integer-coefficient identity

$$
3P-xP'=-6
$$

gives a compact certificate:

```lean
import LeanCert.Validity.Algebra

open LeanCert.Engine
open LeanCert.Validity.Algebra

def cubic : QPoly := ⟨#[-2, 0, 0, 1]⟩

def cubicCert : BezoutCert where
  A := ⟨#[3]⟩
  B := ⟨#[0, -1]⟩
  c := -6

example : cubic.toPoly.Separable := by
  exact verify_separable cubic cubicCert (by native_decide)

example (x : ℝ) (hx : Polynomial.aeval x cubic.toPoly = 0) :
    Polynomial.aeval x cubic.toPoly.derivative ≠ 0 := by
  exact verify_real_roots_simple cubic cubicCert (by native_decide) x hx
```

The nonzero scalar is intentional. A CAS may clear denominators and retain
integer coefficients instead of rescaling the identity to $1$.

## Composition with `Expr`

`QPoly.toExpr` produces a Horner expression in variable `0`. Theorems
`QPoly.eval_toExpr` and `QPoly.deriv_eval_toExpr` connect it to polynomial
evaluation and differentiation. Thus the same certificate can discharge the
simple-root condition in the analytic layer:

```lean
example (x : ℝ)
    (hx : LeanCert.Core.Expr.eval (fun _ => x) cubic.toExpr = 0) :
    deriv (fun t : ℝ =>
      LeanCert.Core.Expr.eval (fun _ => t) cubic.toExpr) x ≠ 0 := by
  exact verify_toExpr_roots_simple cubic cubicCert (by native_decide) x hx
```

## Trust and certificate generation

`BezoutCert` is untrusted input. `bezoutCheck` performs exact rational
addition, multiplication, differentiation, trimming, and array equality in
Lean. A malformed cofactor or incorrect scalar is rejected; rejection is
inconclusive rather than unsound.

The optional `scripts/bezout_cert.py` frontend uses SymPy to discover
cofactors, clears denominators, and prints a Lean `BezoutCert` term:

```sh
python scripts/bezout_cert.py --coeffs=-2,0,0,1
```

SymPy is not in the trusted proof path. LeanCert always replays the identity
with `bezoutCheck`.

## Stable theorem surface

All wrappers consume the same hypothesis `bezoutCheck P cert = true`:

| Goal | Golden theorem |
|---|---|
| Separability | `verify_separable` |
| Squarefreeness | `verify_squarefree` |
| Coprimality of $P$ and $P'$ | `verify_coprime_deriv` |
| Every real root is simple | `verify_real_roots_simple` |
| Simple roots in the `Expr` layer | `verify_toExpr_roots_simple` |
