# Real zeros of the DBN heat integral at time one half

**The full classical threshold certificate is now proved.** See
[dbn-threshold.md](dbn-threshold.md) for the bad-time argument, finite threshold,
exact zero characterization, and the unconditional bound `Lambda ≤ 1/2`.
This page details the endpoint and forward-contraction components.

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

The endpoint theorem alone proves real-only zeros at time one half. The
forward-contraction component described below proves the general time-dependent
strip theorem; `Threshold.lean` adds the finite real threshold and the bound
`Lambda ≤ 1/2`. These results do not assert finite-height RH verification or
sharper numerical bounds. Numerical mollifier research is separate.

## Toward the threshold: closed real-zero times

`LeanCert.Analysis.DBN.RealZeroTimes` now defines

```text
realZeroTimes : Set ℝ := {t | ∀ z : ℂ, H t z = 0 → z.im = 0}
```

and proves **unconditionally** that this set is closed and nonempty. The proof
upgrades joint continuity of `H` to locally uniform convergence in space as time
converges, then applies `entire_limit_ne_zero` on the open nonreal region.
`H_zero_ne_zero t` rules out the identically zero limit. No numerical input is
needed. The convergence interface supports arbitrary nontrivial index filters,
not just sequences.

The module also provides explicitly **conditional** interfaces:

- `realZeroTimes_isLeast_sInf`: lower-boundedness gives an attained infimum;
- `realZeroTimes_sInf_le_half`: with that same hypothesis, the infimum is at most
  one half;
- `realZeroTimes_eq_Ici`: lower-boundedness **and forward preservation** identify
  the set with the closed upper ray starting at its infimum;
- `realZeroTimes_bddBelow_of_bad_time`: forward preservation plus one time with a
  nonreal zero supplies lower-boundedness.

This foundational interface keeps lower-boundedness explicit; the downstream
`Threshold` module now constructs the unconditional real-valued DBN constant.
A nonempty set need not be bounded below, and Lean's total `sInf` operation is
not a substitute for proving this hypothesis. In particular, one bad time alone
does not bound every good time without preservation.

### Finite-threshold requirement

The independent bad-time obligation is now discharged by
`exists_bad_negative_square` in `BadTime.lean`. Together with `realZeroTimes_forward`,
it supplies `realZeroTimes_bddBelow`; `dbn_certificate` in `Threshold.lean` packages the
result without analytic hypotheses.

Regression and transitive axiom checks live in `LeanCert.Test.DBNRealZeroTimes`
and are included in `FunctionalTests`. Reproduce with:

```sh
lean-runtime build LeanCert.Test.DBNRealZeroTimes LeanCert.Test.DBNRealZeros LeanCert.Analysis.DBN
lean-runtime check --using . Tests/TrustManifest.lean
```

## Reusable polynomial-to-heat transfer

`LeanCert.Analysis.DBN.PolynomialHeatTransfer` separates the reusable zero-control
argument from the particular DBN endpoint. Its statements do not assume a DBN
kernel or a fixed starting time.

`StripPolynomialApproximation f b` packages a sequence of nonzero polynomials,
conjugation symmetry, squared zero-strip bound `b²`, and locally uniform
convergence to `f`. It does **not** simply assume the desired heat-flow zero
conclusion. Evenness is useful in constructing DBN cutoffs but is not required
by this transfer interface.

The API has three layers:

- `shift_strip`: polynomial contraction passes through the first limit, giving
  squared strip bound `max (b² - n*a²) 0` for `shiftIter a n f`;
- `heat_limit_strip`: a second locally uniform limit inherits a common target
  strip bound, with arbitrary positive amplitudes and natural-number counts;
- `heat_limit_real`: a squared budget covering `b²` specializes the target strip
  to the real axis. This includes an initial zero-width strip.

Both limits must be entire and nontrivial. These hypotheses are explicit:
nonzero approximants can otherwise converge to the identically zero function.
The API does not identify a limit with a desired heat integral merely from its
name; callers must prove that convergence.

### Arbitrary-time analytic inputs

The following are now unconditional for **every real `t`**, including negative
times:

- `H_norm_le_exp_order` and `H_order`: subquadratic spatial growth of order at
  most `3/2`;
- `H_hadamard`: genus-one factorization with a polynomial exponent of degree at
  most one;
- `H_inverse_square_summable` and `H_canonicalProduct_convergence`: summability
  and locally uniform canonical-product convergence;
- `H_eq_normalized_canonicalProduct`: evenness removes the linear exponential
  prefactor, giving `H t z = H t 0 * divisorCanonicalProduct 1 (H t) univ z`;
- `shiftIter_H_ne_zero`: positivity at the origin supplies nontriviality of
  every finite shift, for arbitrary real amplitudes and natural-number counts.

The growth proof absorbs the temporal quadratic term into the kernel decay:

```text
t*u² + y*u - kernelScale u ≤ t² + y*sqrt(y) + 2 - u²    (u,y ≥ 0).
```

This isolates time in a constant instead of weakening the spatial exponent to
quadratic growth. The previous time-zero growth and factorization declarations
remain as specializations, with unchanged statements.

### Integration and trust

`H_zero_stripApproximation` constructs the interface from the existing actual
DBN cutoffs. `H_half_real_zeros` now uses `heat_limit_real`, exercising both
limits through this abstraction rather than leaving it unused.

`LeanCert.Test.DBNHeatTransfer` checks arbitrary-time statements, negative time,
zero shifts/iterations, a zero-width strip, general strip transfer, and exact
transitive axiom sets. The new results remain kernel-trusted, using only
`propext`, `Classical.choice`, and `Quot.sound`. No new axioms, numerical
certificates, dependency versions, or toolchain changes are involved.

```sh
lean-runtime build LeanCert.Test.DBNHeatTransfer LeanCert.Test.DBNHadamard \
  LeanCert.Test.DBNCanonicalProduct LeanCert.Test.DBNRealZeros \
  LeanCert.Test.DBNRealZeroTimes LeanCert
lean-runtime check --using . Tests/TrustManifest.lean
```

## Forward strip contraction

`LeanCert.Analysis.DBN.ForwardPreservation` proves the full contraction law for
the actual integral, at arbitrary real starting time:

```text
δ ≥ 0
(∀ z, H t z = 0 → (Im z)² ≤ b²)
⇒ (∀ z, H (t+δ) z = 0 → (Im z)² ≤ max (b²−2δ) 0).
```

`H_forward_strip` includes zero elapsed time. Its analytic inputs are:

- `TimeApproximation.HZeroPolynomial_convergence`: symmetric, multiplicity-
  preserving radius cutoffs converge locally uniformly at every real time;
- `H_stripApproximation`: those cutoffs inherit any known starting strip;
- `timeShift_convergence`: shifts of amplitude
  `sqrt(2δ) * sqrt(1/(n+1))`, iterated `n+1` times, converge locally uniformly
  to `H (t+δ)`. Gaussian domination handles moving complex arguments.

`H_forward_real` specializes to a zero-width strip, and
`realZeroTimes_forward` states upward closure in ordered-time form.
In particular:

```lean
import LeanCert.Analysis.DBN.ForwardPreservation

open LeanCert.Analysis.DBN

example {t : ℝ} (ht : (1/2 : ℝ) ≤ t)
    (z : ℂ) (hz : H t z = 0) : z.im = 0 :=
  H_real_zeros_of_half_le ht z hz
```

This component proves real-only zeros for every time at least one half.
Finiteness of the infimum comes separately from `BadTime`; the complete
real-valued characterization is in `Threshold`.

`LeanCert.Test.DBNForwardPreservation` covers negative starting times, zero
increments, zero strip width, recovery of the one-half endpoint, later times,
and exact transitive axiom guards.

```sh
lean-runtime build LeanCert.Test.DBNForwardPreservation LeanCert
lean-runtime check --using . Tests/TrustManifest.lean
```
