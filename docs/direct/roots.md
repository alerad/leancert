# Roots And No-Root Proofs

For ordinary root existence, uniqueness, and no-root goals, start with
[`leancert`](leancert.md). Use this page when you need the dedicated root
controls or programmatic certificate APIs.

For square multivariate systems in LeanCert's differentiable AD fragment, use
`system_unique_root`. It generates an untrusted rational center and approximate
inverse Jacobian, then accepts it only after the existing `krawczykCheck`
succeeds and the `verify_unique_system_root` Golden Theorem produces the
requested proof. Use `system_unique_root using cert` to pin an explicit
candidate. See the
[system architecture and examples](../architecture/root-finding.md#nonlinear-systems-krawczyk).

Typical goals:

```text
∃ x ∈ I, f x = 0
∃! x ∈ I, f x = 0
∀ x ∈ I, f x ≠ 0
```
Primary workflow:

```text
leancert
leancert?
```

Advanced controls:

```text
interval_roots
interval_unique_root
root_bound
system_unique_root using cert
system_unique_root
```

## Nonlinear systems with Krawczyk certificates

The exact recognized goal is:

```text
∃! x : Fin n → ℝ, FinBoxMem x X ∧ SystemZero F x
```

The conjunction may also be written in the opposite order.

```lean
import LeanCert.Examples.Krawczyk
import LeanCert.Tactic

open LeanCert.Core LeanCert.Engine LeanCert.Validity
open LeanCert.Examples.Krawczyk

example : ∃! x, FinBoxMem x box ∧ SystemZero system x := by
  system_unique_root (trust := kernel)
```

Automatic search starts at the box midpoint, constructs a preconditioner from
a singleton checked-AD Jacobian, and performs bounded interval-Newton center
refinements when needed. Candidate values are dyadically rounded to control
denominator growth, then checked exactly.

Use `system_unique_root?` for attempts, refinements, generated center and
preconditioner, checked contraction bound, checker, verifier, and effective
verification route:

```text
system_unique_root? (maxIterations := 8) (taylorDepth := 12) (trust := auto)
```

The manual I1 path remains available:

```lean
import LeanCert.Examples.Krawczyk
import LeanCert.Tactic

open LeanCert.Core LeanCert.Engine
open LeanCert.Examples.Krawczyk

example : ∃! x, FinBoxMem x box ∧ SystemZero system x := by
  system_unique_root using certificate (trust := kernel)
```

A rejected certificate is inconclusive, not evidence that the system lacks a
unique root. Diagnostics distinguish an unsupported AD expression, a center
outside the box, a singular preconditioner, a contraction bound not strictly
below one, and failure of the strict self-map check. Every failure restores the
original tactic state.

Automatic I2 candidates and manual I1 certificates pass through the same
Boolean checker and Golden Theorem. Centers and preconditioners may still come
from a separate numerical program; no external or search computation enters
the trusted proof.

Automatic generation defaults to dimensions at most four. Manual certificates
remain dimension-generic. Automatic box subdivision is intentionally excluded:
certifying one sub-box would not prove uniqueness over the original box.

The scalar dedicated tactics use typed, transactional certificate boundaries.
A checker result of `false` is an ordinary rejected candidate; malformed
input is unsupported; verifier or proof-transport failures remain terminal.
Every non-success restores the complete caller tactic state. The retained
success report records the actual checker, Golden Theorem, verification route,
and Taylor depth without rerunning the certificate.

The corresponding programmatic entry points are:

```text
intervalRootsCoreTyped
intervalUniqueRootCoreTyped
rootBoundCoreTyped
```

Dedicated tactic syntax translates these typed failures into user-facing
diagnostics at the elaborator boundary.

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
