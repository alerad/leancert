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
APIs. LeanCert also certifies exact real-root counts for quadratic and cubic
polynomials from the sign of the discriminant.

## Global and parametric cubic counts

`CubicFamily` stores four `Expr` coefficients in a parameter environment.
`cubicCountCheckBox` proves that the leading coefficient excludes zero and
that the cubic discriminant is strictly negative or positive throughout a
rational parameter box:

| Certified sign | Number of distinct real roots |
|---|---:|
| `discr < 0` | 1 |
| `0 < discr` | 3 |

The result is **fiberwise and uniform**: every parameter assignment in the
box has the same root count. A zero-containing discriminant interval is
inconclusive, because the zero-discriminant wall contains repeated roots.

```lean
import LeanCert.Validity.Algebra

open LeanCert.Core LeanCert.Engine LeanCert.Engine.Optimization
open LeanCert.Validity.Algebra

def t : Expr := .var 0

-- x³ + x + t has discriminant -4 - 27t².
def family : CubicFamily where
  a := .const 1
  b := .const 0
  c := .const 1
  d := t

def parameters : Box := [⟨-1, 1, by norm_num⟩]

example : ∀ rho : Nat → ℝ, parameters.envMem rho →
    (∀ i, i ≥ parameters.length → rho i = 0) →
    (Engine.Algebra.cubicZeroSet (family.at rho)).ncard = 1 := by
  exact verify_cubic_root_count_subdiv family parameters .one 4 {}
    (by native_decide)
```

The padding condition matches LeanCert's other box APIs: variables beyond the
box dimension evaluate to zero.

### Dependency and automatic subdivision

The discriminant repeats coefficient expressions, so ordinary interval
evaluation may lose correlations. `cubicCountCheckSubdiv` first tries the
whole box; if that is inconclusive, it bisects the widest parameter interval
and requires both children to succeed, recursively up to `maxDepth`.
Subdivision changes completeness, never soundness. A `false` result means only
that the requested depth and evaluator precision did not prove a strict sign.
Increase the depth, narrow the parameter box, or simplify the coefficient
expressions. The worst-case number of leaves is `2^maxDepth`.

The checker is pure Lean and calls no external CAS or script. Certificate
discovery helpers belong in downstream tooling such as `leancert-python`.

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

Certificate discovery belongs in a downstream frontend such as
`leancert-python`, not in this pure-Lean repository. Such a frontend may use a
CAS to discover cofactors and clear denominators, but its output remains
untrusted: LeanCert always replays the identity with `bezoutCheck`.

## Stable theorem surface

All wrappers consume the same hypothesis `bezoutCheck P cert = true`:

| Goal | Golden theorem |
|---|---|
| Separability | `verify_separable` |
| Squarefreeness | `verify_squarefree` |
| Coprimality of $P$ and $P'$ | `verify_coprime_deriv` |
| Every real root is simple | `verify_real_roots_simple` |
| Simple roots in the `Expr` layer | `verify_toExpr_roots_simple` |
| Uniform cubic count on one parameter box | `verify_cubic_root_count` |
| Uniform cubic count with subdivision | `verify_cubic_root_count_subdiv` |
| Scale-aware gap lower bound for three named roots | `cubic_root_gap_gt_of_discr_bound` |
| Pairwise gaps from a common root radius | `cubic_roots_pairwise_gap_gt_of_discr_bound_and_radius` |

## Root separation and its scale hypotheses

A nonzero discriminant proves that roots are distinct, but its magnitude alone
does not give a scale-free lower bound on every root gap. A useful separation
certificate must also bound the leading coefficient and the size of the other
root gaps (usually through a certified root-radius or coefficient-height
bound).

`cubic_root_gap_gt_of_discr_bound` exposes the sound theorem-level core. Given
the three roots `x`, `y`, `z`, a lower bound `d ≤ |discr|`, bounds
`|a| ≤ A`, `|x-z| ≤ M`, `|y-z| ≤ M`, and
`A⁴ M⁴ eps² < d`, it concludes `eps < |x-y|`. The root ordering can be
permuted to bound any pair.

`cubic_roots_pairwise_gap_gt_of_discr_bound_and_radius` is the convenient
all-pairs form. If all three roots satisfy `|r| ≤ R`, the two unused gaps are
at most `2R`; the single threshold `A⁴(2R)⁴eps² < d` then proves all three
pairwise gaps exceed `eps`.

Automating the `M` premise is a later certificate layer: it should combine a
Cauchy root-radius checker with this theorem, rather than hide an unstated
scale assumption in the discriminant API.
