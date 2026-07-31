# Removed APIs and migration

LeanCert removes deprecated aliases once downstream users have had a release
cycle to migrate. The aliases on this page are no longer provided; this page is
the durable map from historical names to their canonical replacements.

The compatibility surfaces retired by PR #96 are removed in `v4.32.2.2`.
Removing the shims does not change the underlying certificate semantics.

## Tactics and imports

| Removed surface | Replacement |
| --- | --- |
| `interval_bound` | `certify_bound`, or `leancert` for portfolio routing |
| `certify_kernel [prec]` | `certify_bound (trust := kernel)` |
| `certify_kernel_fallback [prec]` | `certify_bound (trust := auto)` |
| `certify_kernel_precise` | `certify_bound 20 (trust := kernel)` |
| `certify_kernel_precise_fallback` | `certify_bound 20 (trust := auto)` |
| `certify_kernel_quick` | `certify_bound 5 (trust := kernel)` |
| `certify_kernel_quick_fallback` | `certify_bound 5 (trust := auto)` |
| `import LeanCert.Tactic.DyadicAuto` | `import LeanCert.Tactic.IntervalAuto`, or import the required validity API directly |
| `import LeanCert.Tactic.Bound.Lemmas` | `import LeanCert.Engine.Bounds.Lemmas` |
| `import LeanCert.Engine.ChebyshevPsi` | `import LeanCert.Engine.Chebyshev.Psi` |
| `import LeanCert.Engine.ChebyshevTheta` | `import LeanCert.Engine.Chebyshev.Theta` |
| `import LeanCert.Examples.Li2Bounds` | `import LeanCert.CertifiedBounds.Li2` |
| `import LeanCert.Examples.BKLNW_a2_bounds` and related `BKLNW_a2_*` modules | `import LeanCert.CertifiedBounds.BKLNW` |
| `lake build examples` | `lake build Examples` |

The Li₂ replacement is a lightweight statement interface. Its two
allowlisted placeholder theorems have statement-identical proofs built by the
separate `Li2Verified` target, but the public constants are not kernel-linked
to those proof terms. See [Verification Status](../architecture/verification-status.md)
for the precise trust boundary.

## Earlier semantic-API migrations

These older removals remain listed because error messages and downstream source
trees may still contain their historical names.

| Removed surface | Replacement |
| --- | --- |
| `fast_bound*` | `certify_bound` with the desired trust mode and explicit depth |
| `interval_integrate` | State an ordinary integral equality or inequality and use `leancert` |
| `#minimize`, `#maximize` | `#find_min`, `#find_max` |
| `import LeanCert.Discovery.Types` | `import LeanCert.Validity.Types` |
| `LeanCert.Meta.reify` | `LeanCert.Meta.reifyWithReport` |
| `LeanCert.Meta.toRat?` and related numeric aliases | `LeanCert.Meta.Numeral.toRat?` and the corresponding `Numeral` function |
| `LeanCert.Tactic.LeanCert.Types` and `LeanCert.Tactic.LeanCert.Transaction` | `LeanCert.Tactic.LeanCert.Solver.Protocol` for solver extensions |

New APIs should have one canonical owner. Migration entries belong here rather
than in permanent forwarding modules.
