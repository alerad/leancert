# DBN lower-bound route: Phase 2 completed

**Completion update:** the full lower bound `0 ≤ Lambda` is now proved in
`DBN/DobnerLimit.lean`. See [the final theorem](dbn-nonnegative.md).
Descriptions of remaining work below record the earlier stage of development.


**Status: complete.** The recurrence, local zero-transfer, coordinate geometry,
and saddle-point approximation now yield the unconditional theorem
`Lambda_nonneg : 0 ≤ Lambda`.

## Proved: zeros at arbitrarily large heights

```lean
import LeanCert.Analysis.DirichletGaussian.Recurrence

open LeanCert.Analysis.DirichletGaussian

example {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, ∀ B : ℝ, ∃ s : ℂ,
      |s.re-c| < 1 ∧ B < s.im ∧ series a s = 0 :=
  zeros_at_arbitrary_height ha
```

`exists_phase_returns` applies compactness to the countable product of unit
circles. If `φ` indexes a convergent subsequence, the return times
`τ(n) = φ(2*n)-φ(n)` satisfy `τ(n) ≥ n`, and every phase tends to one.

`translation_error_bound` controls the error throughout a left-bounded
half-plane by one summable scalar series. Dominated convergence then proves
`exists_vertical_recurrence`: `D_a(s+i*τ(n)) → D_a(s)` locally uniformly.
The Phase 1 zero and the local zero-transfer theorem produce high zeros
in a **fixed** vertical strip. No numerical zero search is involved.

## Proved: local zero transfer

`eventually_exists_zero_of_locally_uniform` proves that every neighborhood
of a zero of a nontrivial entire limit eventually contains an approximant
zero. The approximants need only be holomorphic on each compact set
**eventually**, rather than entire globally. This accommodates translated
logarithmic charts and future normalized Gamma factors.

The proof uses an isolated zero, a positive minimum on a surrounding circle,
and the reciprocal maximum principle. It reuses `DBN.disk_lower_bound`;
no unproved Rouché or Hurwitz principle is assumed.

## Proved: normalization and geometry

```lean
import LeanCert.Analysis.DBN.DobnerGeometry

open LeanCert.Analysis.DBN

example (s : ℂ) : xiHeat 0 s = riemannXi s := xiHeat_zero s

example {a R : ℝ} (ha : 0 < a) {s : ℂ} (hs : -R ≤ s.re)
    (hh : 2*Real.pi*Real.exp ((R+1)/a) ≤ |s.im|) :
    (1/2 : ℝ) < (dobnerMap a s).re :=
  dobnerMap_re_gt_half ha hs hh
```

The exact definitions are:

```text
heatCoordinate(s) = (2*s-1)/i
xiHeat(t,s) = 8*H(t,heatCoordinate(s))
J_a(s) = s + a*Log(s/(2*pi)),  a=-t/4>0
```

`heatCoordinate_im` proves the imaginary part is `1-2*Re(s)`.
`eventually_dobnerMap_right_on_compact` proves that upward translations
of a fixed compact set eventually map strictly right of the critical line.
Thus a zero there gives a genuine nonreal zero of the repository's `H`.

## Actual analytic representation now available

[Analytic bridge progress](dbn-dobner-analytic.md) proves the actual Gamma
normalization and its holomorphy, an exact Gaussian representation on every
fixed vertical line, and a justified infinite Dirichlet expansion. It reduces
the connector inputs to one concrete uniform-approximation proposition.
That proposition is now proved by `normalizedHeatApproximation` in
`DobnerLimit.lean`.

## Conditional helper lemmas used by the unconditional proof

`nonreal_zero_of_dobner_limit` concludes a nonreal zero of `H t`, for `t<0`,
from these **explicit inputs**:

- unbounded upward translations `τ(n)`;
- functions `F(n,s)` holomorphic on each compact set eventually;
- locally uniform convergence `F(n,s) → D_{-t/4}(s)`;
- an eventual identity on each compact set:
  `xiHeat(t,J_{-t/4}(s+i*τ(n))) = G(n,s)*F(n,s)`.

These hypotheses are not constructed by that theorem. There is no axiom,
`sorry`, or instance supplying them. In particular, the entire-function
result for `D_a` says nothing by itself about the normalized heat functions.
If `F` is defined by division by a Gamma factor, its nonvanishing and local
holomorphy must also be proved; the completed analytic bridge supplies these proofs.

`Lambda_nonneg_of_negative_time_zeros` checks the final logical implication
from a nonreal heat zero for every negative time to `0 ≤ Lambda`.
This helper retains its premise. The completed theorem `Lambda_nonneg` supplies
that premise and states the lower bound unconditionally.

## Completed approximation

The normalized contour bounds and both limit interchanges are now proved.
See [Newman nonnegativity](dbn-nonnegative.md) for the implementation and audits.

The concrete approximation proposition is `NormalizedHeatApproximation a`,
documented in the [analytic progress page](dbn-dobner-analytic.md). It is now proved
for every positive damping, closing the existing chain to `0 ≤ Lambda`.
Closing this analytic gap required uniform contour estimates and limit
interchanges, not merely running a numerical certificate.

Regression tests: `LeanCert/Test/DBNDobner.lean`. Public results, including
the clearly conditional connectors, are pinned in `Tests/TrustManifest.lean`.
