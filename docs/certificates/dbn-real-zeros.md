# Real zeros of the DBN heat integral at time one half

```lean
import LeanCert.Analysis.DBN.RealZeros

open LeanCert.Analysis.DBN

example (z : ℂ) (hz : H (1/2) z = 0) : z.im = 0 :=
  H_half_real_zeros z hz
```

This is an unconditional theorem about the actual integral

```text
H t z = ∫ u > 0, exp(t*u²) * Phi(u) * cos(z*u) du
Phi(u) = Σ n ≥ 1, (2π²n⁴ exp(9u) - 3πn² exp(5u)) exp(-πn² exp(4u)).
```

The kernel normalization and integral are defined in `DBN.HeatKernel` and
`DBN.HeatFlow`. `H_half_ne_zero_of_im_ne_zero` is the corresponding
nonvanishing interface. Both are exported by `LeanCert.Analysis.DBN` and
the root `LeanCert` import.

## Proof and suggested review order

1. **Analytic foundations.** `HeatKernel`, `HeatFlow`, `HeatRegularity`, and
   the theta/xi modules prove integrability, entireness, symmetry, positivity
   at the origin, the xi identity, and the initial unit-strip bound.
2. **Polynomial contraction.** `StripShift` and `StripIteration` prove that
   averaging at imaginary shifts contracts polynomial root strips, retaining
   multiplicities. A total squared-shift budget of one gives real-only roots.
3. **Actual polynomial approximation.** `HeatGrowth`, `Hadamard`, and
   `CanonicalProduct` supply the normalized factorization of `H 0`.
   `PolynomialApproximation` exhausts the actual divisor by finite radius
   cutoffs, retaining multiplicity labels and negation/conjugation symmetry.
   The resulting real polynomials converge locally uniformly to `H 0` and
   have unit-strip roots, including the empty-cutoff case.
4. **Zero preservation.** `ZeroLimit` combines isolated zeros, a compact
   sphere minimum, and the reciprocal maximum principle. A nontrivial entire
   locally uniform limit cannot acquire zeros in an open zero-free region.
5. **First limit.** `ShiftLimit` transfers polynomial contraction to finite
   shifts of `H 0`. A strictly positive integral at zero excludes the
   identically-zero alternative.
6. **Heat limit and endpoint.** `HeatShift` identifies the finite integrals.
   `HeatLimit` proves dominated convergence with a moving complex argument,
   and hence locally uniform convergence to `H (1/2)`, not just pointwise
   convergence. `RealZeros` applies zero preservation again.

## Provenance and trust

The 35-module Hadamard source adaptation is isolated under
`LeanCert/Analysis/HadamardSupport`, with preserved Apache 2.0 licensing,
original and adapted source hashes, and documented compatibility changes.
See its [README on GitHub](https://github.com/alerad/leancert/blob/main/LeanCert/Analysis/HadamardSupport/README.md).
This introduces no new Lake dependency and does not change toolchain or
Mathlib pins. The adapted sources use LF line endings for stable hashes.

`LeanCert.Test.DBNRealZeros` guards the exact transitive axiom sets of the
endpoint and its main bridges. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. `Tests/TrustManifest.lean` also pins the exported endpoint
as kernel-trusted. No numerical certificate or assumed approximation theorem
is used in this chain.

## Reproduction

In the project's pinned Lean 4.33.1 / Mathlib v4.33.1 environment:

```powershell
lean-runtime build LeanCert.Test.DBNRealZeros LeanCert.Analysis.DBN
lean-runtime check LeanCert/Test/DBNRealZeros.lean
lean-runtime build
```

All DBN regression modules are wired into `FunctionalTests`; the regular
soundness-guard workflow checks the exported trust manifest.

## Scope

This proves the real-zero endpoint, not the separate threshold/infimum
foundations needed to state a bound for a real-valued de Bruijn–Newman
constant. It does not assert the general time-dependent strip theorem,
finite-height RH verification, or sharper numerical bounds. Numerical
mollifier research is deliberately outside this change.
