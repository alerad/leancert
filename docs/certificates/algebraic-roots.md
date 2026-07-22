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

## Complete cubic isolation

For an exact rational cubic, `CubicIsolationCert` combines the algebraic and
analytic layers in one executable check:

1. `QCubic.threeRootCountCheck` proves globally that the discriminant is
   positive, hence there are exactly three real roots.
2. Three `checkNewtonContractsCore` calls prove a unique root in each rational
   interval.
3. `intervalsOrdered` proves the intervals pairwise disjoint.
4. Finite-cardinality exhaustion proves that every real root is in their
   union.

```lean
def p : QCubic := ⟨1, 0, -1, 0⟩ -- x³ - x

def isolation : CubicIsolationCert where
  left := ⟨-11 / 10, -9 / 10, by norm_num⟩
  middle := ⟨-1 / 10, 1 / 10, by norm_num⟩
  right := ⟨9 / 10, 11 / 10, by norm_num⟩

example : cubicIsolationCheck p isolation = true := by native_decide

example : Engine.Algebra.cubicZeroSet p.toReal ⊆
    intervalSet isolation.left ∪ intervalSet isolation.middle ∪
      intervalSet isolation.right := by
  exact (verify_complete_cubic_isolation p isolation (by native_decide)).2.2.2
```

The full Golden Theorem also returns one `∃!` statement for each interval.
This API intentionally handles fixed `QCubic` coefficients. Uniform root
counts for parameter families remain available through `CubicFamily`; tracking
three moving isolating intervals over a parameter box is a distinct problem.

The executable `QCubic` representation has explicit `toQPoly` and
`toCubicRat` bridges in addition to `toReal` and `toExpr`. The interval data
and algebraic exhaustion lemmas live in the Engine layer; the combined Newton
checker and its soundness theorem live in `Validity.Algebra`, preserving the
Engine-to-Validity dependency direction.

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

The stable wrappers expose each successful executable check in its common
semantic goal shape:

| Goal | Golden theorem |
|---|---|
| Separability | `verify_separable` |
| Squarefreeness | `verify_squarefree` |
| Coprimality of $P$ and $P'$ | `verify_coprime_deriv` |
| Every real root is simple | `verify_real_roots_simple` |
| Simple roots in the `Expr` layer | `verify_toExpr_roots_simple` |
| Uniform cubic count on one parameter box | `verify_cubic_root_count` |
| Uniform cubic count with subdivision | `verify_cubic_root_count_subdiv` |
| Three unique roots and global exhaustion | `verify_complete_cubic_isolation` |
| Cauchy radius for every real root | `verify_cubic_root_radius` |
| Pairwise separation from an exact mesh check | `verify_cubic_separation_mesh` |
| Separation of any two distinct real roots | `verify_cubic_distinct_roots_separated` |
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

`QCubic.cauchyRadius` now supplies the common radius automatically using exact
rational coefficient arithmetic. `separationMeshCheck P eps` checks
`|a|⁴(2R)⁴eps² < |discr|`; on success,
`verify_cubic_separation_mesh` proves that all three pairwise root gaps exceed
`eps`. `automaticSeparationMesh` supplies a deterministic rational candidate,
and `automaticSeparationMesh_check` proves that this candidate always passes
when the leading coefficient and discriminant are nonzero. The Boolean checker
remains the source of truth for user-provided mesh widths.

`verify_cubic_distinct_roots_separated` is the high-level semantic form: given
the three-root count, a successful mesh check, and two distinct members of the
real zero set, it proves their distance exceeds the mesh width. Users need not
construct or reorder a `Cubic.roots` multiset identity.
