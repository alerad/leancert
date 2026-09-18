# Hadamard support sources

Adapted from the 35-module import closure of
`PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order`.
Original copyright/author headers and Apache 2.0 license are preserved.
Source hashes and original module names are recorded in
`docs/audits/dbn-hadamard-imports.json`.

Imports are relocated from `PrimeNumberTheoremAnd.Mathlib` to
`LeanCert.Analysis.HadamardSupport`; existing mathematical namespaces are
preserved. This is source reuse, not an additional Lake dependency. Do not
import the original project alongside this copy (declaration names overlap).
Compatibility edits for the current pinned Mathlib are documented below.

The initial source audit used Lean 4.32.2. This copy now builds on this project's Lean 4.34.0 and passes the transitive
axiom audits in `LeanCert.Test.DBNHadamard` (standard axioms only).

## Compatibility changes

* `Analysis/Complex/HadamardFactorization/Summability.lean`: replaced the removed
  `Ne.elim hA0 h` helper with direct application `hA0 h`. The target is False;
  the mathematical argument and statement are unchanged.
* `Analysis/Complex/CartanProductBound.lean`: use `Finset.prod_le_prod₀` for
  the product inequality with nonnegative factors.
* `Analysis/Complex/CanonicalProduct.lean`: use `logDeriv_fun_mul` for the
  logarithmic derivative of a pointwise product.
* `Analysis/Complex/CartanBound.lean`: discharge the generalized `-1 ≤ x`
  hypothesis of `Real.posLog_le_posLog` from nonnegativity.
* Updated deprecated Mathlib lemma names and simplified local instance
  declarations as recommended by the Lean 4.34 linters.
* All 35 import paths are relocated as described above.

`provenance.json` records original and adapted source hashes, including these
compatibility edits. Adapted Lean sources use LF line endings, enforced
by `.gitattributes`, so the adapted hashes also verify in a fresh checkout.
Pre-normalization hashes retain the original adaptation evidence where line
endings changed. The neighboring source checkout was not modified.
