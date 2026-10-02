# Certificate API Reference

This page maps the detailed certificate APIs. For a conceptual starting point, use
[Proof Templates](../proof-templates/overview.md) or
[Domain Libraries](../domains/overview.md) unless you already know the API
family name.

LeanCert certificate APIs share the same basic pattern:

```text
computable certificate data
+ a boolean or exact checker
+ a Golden Theorem
= a semantic theorem over real numbers
```

Use this page when you already know the family name and want the detailed API
reference.

## Families

| Certificate family | Use when you need |
|---|---|
| [Chebyshev](chebyshev.md) | finite-range bounds for the Chebyshev functions `ψ` and `θ` |
| [ANT finite bridges](ant.md) | step sums, Abel transforms, Euler products, log products, Dirichlet truncations, prime-power extensionality, and explicit-PNT compiler schemas |
| [ANT asymptotic envelopes](ant-asymp.md) | main-term plus error-term certificates for summatory functions, pointwise estimates, dyadic slab inequalities, and transforms |
| [Contour Shift](contour-shift.md) | finite rectangle identities, horizontal-side vanishing, vertical-line limits, and residue-sum shift identities |

## Imports

Most certificate families can be imported directly:

```lean
import LeanCert.ANT
import LeanCert.ANT.Asymp
import LeanCert.Analysis.ContourShift
import LeanCert.Engine.Chebyshev.Psi
import LeanCert.Engine.Chebyshev.Theta
```

or through the aggregate API:

```lean
import LeanCert
```

## Choosing A Family

Use finite ANT certificates when your theorem is an exact finite statement:
finite sums, products, truncations, and Abel transforms over explicit endpoints.

Use asymptotic envelope certificates when the theorem is naturally stated as a
summatory main term plus an error term from some cutoff onward.

Use Chebyshev certificates for specialized `ψ` and `θ` finite-range bounds.
These can feed into ANT and asymptotic envelope arguments.

QProduct and ConstantFactory certificates (exact product-integral identities,
prime-limit sandwiches, observer perturbations) live in the downstream
**leancert-qproduct** package; see the [migration guide](../qproduct-migration.md).

Use contour-shift certificates when the analytic work has been decomposed into
finite rectangle identities, horizontal decay, vertical-line convergence, and a
stable finite residue sum.  The current API centralizes the orientation and
limit algebra; residue-theorem constructors can be layered on top.
