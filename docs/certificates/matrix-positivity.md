# Matrix Positivity Certificates

LeanCert certifies positive-semidefinite and positive-definite finite real
matrices from exact rational data. Candidate discovery is untrusted; an
executable Boolean checker validates the retained factorization before a
kernel-clean Golden Theorem produces Mathlib's `Matrix.PosSemidef` or
`Matrix.PosDef` proposition.

## Automatic tactics

The initial automatic front end accepts a closed rational square matrix cast
exactly to the reals with `ratCastMatrix`:

```lean
import LeanCert.Tactic

open LeanCert.Engine

def A : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 2]

example : (ratCastMatrix A).PosDef := by
  matrix_posdef

example : (ratCastMatrix A).PosSemidef := by
  matrix_psd
```

`matrix_posdef?` and `matrix_psd?` retain and display the selected exact
certificate route and pivot counts. The semantic `leancert` front door routes
the same goal family through the same typed core.

Automatic and query forms accept `(maxDimension := n)`. All forms accept an
inline `(trust := kernel|native|auto)` selection.

Discovery performs one exact rational LDLᵀ decomposition. It neither rounds
entries nor runs the checker as a preflight. The retained candidate is closed
once through the configured `kernel`, `native`, or `auto` verification route.

## Explicit certificates

Positive-semidefinite claims accept either an exact Gram certificate or an
LDLᵀ certificate. Positive-definite claims use LDLᵀ data with strictly
positive diagonal entries and an invertible lower factor.

```lean
def cert : LDLTCertificate 2 where
  lower := !![1, 0; 1 / 2, 1]
  diagonal := ![2, 3 / 2]

example : (ratCastMatrix A).PosDef := by
  matrix_posdef using cert
```

The stable programmatic import is:

```lean
import LeanCert.API.MatrixPositivity
```

It exposes `matrixPSDCheck`, `matrixPosDefCheck`,
`verify_matrix_posSemidef`, and `verify_matrix_posDef`.

## Finite feature maps and kernels

For a finite real feature table, `gramMatrix feature` is positive
semidefinite. Adding a pointwise-positive diagonal ridge produces a positive
definite matrix:

```lean
#check LeanCert.gramMatrix_posSemidef
#check LeanCert.regularizedGramMatrix_posDef
```

This is an exact structural kernel result. Interval-valued entries,
approximate factorization residuals, quantitative eigenvalue bounds, and
uniform positivity over parameter boxes are outside the current claim.

## Failure behavior

- Unsupported or symbolic matrices are typed as unsupported and may fall
  through to another `leancert` strategy.
- The automatic dimension limit is an inconclusive search outcome.
- A false or malformed certificate is a resumable rejection.
- Verification, proof transport, and unexpected infrastructure failures are
  terminal.
- Every non-success restores goals, assignments, environment changes, and
  messages.
