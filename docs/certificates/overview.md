# Certificate APIs

LeanCert has several domain-specific certificate families.  They share the same
basic pattern:

```text
computable certificate data
+ a boolean or exact checker
+ a Golden Theorem
= a semantic theorem over real numbers
```

Use this page as the map for choosing the right certificate API.

## Families

| Certificate family | Use when you need |
|---|---|
| [Chebyshev](chebyshev.md) | finite-range bounds for the Chebyshev functions `ψ` and `θ` |
| [ANT finite bridges](ant.md) | step sums, Abel transforms, Euler products, log products, Dirichlet truncations, and Mertens-style finite sums |
| [ANT asymptotic envelopes](ant-asymp.md) | main-term plus error-term certificates for summatory functions and transforms |
| [QProduct](qproduct.md) | exact finite q-product integrals and prime-limit sandwich certificates |
| [ConstantFactory](constants.md) | exact observer-generated q-product constants from perturbation sums and reusable moment kernels |

## Imports

Most certificate families can be imported directly:

```lean
import LeanCert.ANT
import LeanCert.ANT.Asymp
import LeanCert.QProduct
import LeanCert.ConstantFactory
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta
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

Use QProduct certificates for exact product-integral identities and finite
prime-limit sandwich arguments.

Use ConstantFactory certificates when a q-product constant is best proved by
holding a base kernel bank fixed and verifying finite observer perturbations
around it.
