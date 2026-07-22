# Roots And No-Root Proofs

Use this path for root existence, uniqueness, and no-root goals over an
interval.

For square multivariate systems in LeanCert's differentiable AD fragment, use the certificate API
`KrawczykCert`, `krawczykCheck`, and `verify_unique_system_root`. See the
[system architecture and examples](../architecture/root-finding.md#nonlinear-systems-krawczyk).
A tactic front end is not required: the intended proof is one checker theorem
followed by `native_decide`.

Typical goals:

```lean
∃ x ∈ I, f x = 0
∃! x ∈ I, f x = 0
∀ x ∈ I, f x ≠ 0
```

Main tools:

```lean
interval_roots
interval_unique_root
root_bound
```

## Global algebraic simplicity and counts

For an exact rational polynomial, `BezoutCert` checks an identity
`A * P + B * P' = c` with `c ≠ 0`. One successful exact check proves that the
polynomial is separable and squarefree and that every real root is simple,
without choosing a bounding interval. `QPoly.toExpr` connects that result to
the expression used by the interval root pipeline.

See [Algebraic Root Certificates](../certificates/algebraic-roots.md) for the
checker, Golden Theorems, and complete examples. `CubicFamily` additionally
supports uniform one-or-three real-root counts over parameter boxes.
`cubicCountCheckSubdiv` automatically bisects boxes when dependency makes a
direct discriminant enclosure inconclusive. For a fixed exact rational cubic,
`cubicIsolationCheck` composes a global three-root count with three ordered
Newton certificates and proves exhaustion: one unique root per interval and
no roots elsewhere. `QCubic.cauchyRadius` and `separationMeshCheck` additionally
provide an executable a-priori radius and pairwise root-gap bound.

Minimal root-existence example:

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := { lo := 1, hi := 2, le := by norm_num }

example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

Architecture background for how the certified root pipeline works is in
[Root Finding](../architecture/root-finding.md).

For tactic details, see [Reference → Tactics](../reference/tactics.md).
