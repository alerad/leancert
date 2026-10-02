# QProduct extraction

QProduct and ConstantFactory now live in a separate **leancert-qproduct**
Lake project. LeanCert no longer imports, re-exports, builds, or tests that
application. Its mathematical proofs and certificate audits move with it.

## Import and namespace changes

| Previous module | Downstream module |
| --- | --- |
| `LeanCert.QProduct` | `QProduct.LeanCert` (full former surface) |
| mathematical `LeanCert.QProduct.*` modules | `QProduct.*` |
| `LeanCert.QProduct.LimitCert` | `QProduct.LeanCert.LimitCert` |
| `LeanCert.QProduct.Sparse` | `QProduct.LeanCert.Sparse` |
| `LeanCert.ConstantFactory` | `QProduct.ConstantFactory` |
| `LeanCert.ConstantFactory.IntervalBank` | `QProduct.LeanCert.IntervalBank` |

Use `QProduct` for the Mathlib-only mathematical import surface; use
`QProduct.LeanCert` to opt into LeanCert-backed certificates. Declaration
names move from `LeanCert.QProduct.*` to `QProduct.*` and from
`LeanCert.ConstantFactory.*` to `QProduct.ConstantFactory.*`.
Aliases formerly re-exported directly under `LeanCert` are no longer provided.

Add the downstream package as a dependency before changing imports. Existing
applications cannot obtain these declarations from `import LeanCert` alone.
The new package's README documents the local two-checkout setup; a remote
package revision must be pinned when the extracted repository is published.

## Ownership

The extracted project owns prime-lambda digit certificates, sparse q-product
regressions, ConstantFactory examples, and their trust audits. It depends on
LeanCert, never the reverse. Generic rational polynomials, Bernstein bounds,
interval arithmetic, and `LeanCert.Validity.DirectedLimit` remain here.
