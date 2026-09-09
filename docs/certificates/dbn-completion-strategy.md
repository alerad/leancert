# DBN ≥ 0: repository-audited completion strategy

**Status: completed.** The [linear-cutoff route](dbn-linear-cutoff-completion.md)
was implemented through the unconditional theorem `Lambda_nonneg : 0 ≤ Lambda`.
See [the final result](dbn-nonnegative.md). The material below is the historical
library audit and pre-completion plan, not a list of currently open obligations.

## Historical decision and exact finish line

The decision was to keep the specialized Dobner route rather than restart zero
theory, build another conditional final connector, or attempt to certify
infinitely many heights by sampling. The critical new mathematics was a
**relative complex Gamma estimate** and **uniform normalized contour bounds**.

For each fixed `a>0` and `M≥0`, write `s=x+iy`, `|x|≤M`,
`L=log(k+1)`, `T_k(s)=normalizedContourTerm a s k`, and
`m_k(s)=DirichletGaussian.term a s k`. Prove:

```text
A. For every fixed k and epsilon>0, eventually in y,
   forall |x|≤M, |T_k(x+iy)-m_k(x+iy)| < epsilon.

B. There are Y,C,c>0, depending only on a,M, such that
   forall y≥Y, forall |x|≤M, forall k,
   |T_k(x+iy)| ≤ C exp(-c log(k+1)^2).
```

The single `Y` in B must work for ALL indices. In A the height threshold may
also depend on k and epsilon. Neither condition requires constants uniform as
`a→0`. The plan required absolute errors, not a relative error uniformly over all k.

A+B imply `NormalizedHeatApproximation a`. The existing
`Lambda_nonneg_of_normalizedHeatApproximation` then supplies the final bound.
No additional numerical zero certificate is needed.

## What the historical audit found

Paths below are relative to `LeanCert/` unless prefixed by `Mathlib/`.

| Asset checked in source | Reuse | What it does NOT prove |
|---|---|---|
| `Analysis/IntegralTail.lean`: `IntegralTail.of_gaussian`, `remainder_eq` | Complex-valued improper tail norms once a majorant is supplied; translate/reflect to cover both ends | The majorant itself or uniformity in external parameters |
| `Analysis/PolynomialDecay.lean`: `pow_mul_exp_neg_le` | Absorb polynomial factors while retaining exponential decay | Gamma asymptotics |
| `Analysis/GaussianMoments.lean`: `integrableOn_gaussian_moment` and imported Gaussian calculus | Integrate polynomial-weighted errors; scale and translate existing formulas | A relative-error bound on the Gamma factor |
| `Analysis/SeriesTail.lean`: `SeriesTail.of_majorant` | Tail norm for complex series from a scalar summable majorant | An envelope for the actual contour terms |
| `Analysis/DirichletGaussian.lean`: `norm_term_le`, `envelope_hasSum`, `tail_bound` | Already handles log-Gaussian decay and a telescoping majorant with tail `2/(N+1)` | The heat-integral approximation |
| `Analysis/DirichletGaussian/Recurrence.lean`: `translate_convergence` | Reuse its scalar-error dominated-convergence proof pattern | It bounds translations of D, not the new heat error |
| Mathlib `FunctionSeries.lean` and `tendsto_tsum_of_dominated_convergence` | Uniform series control and limit/sum interchange | Missing domination hypotheses |
| `Analysis/ContourShift/Decay.lean`, `DBN/DobnerContourShift.lean` | Actual positive-line shifts, saddle-line coefficient identity, exact cancellation | Uniform moving-center/index tail control |
| `DBN/DobnerGammaReciprocal.lean` | Division by the normalization costs at most `C exp(pi*y/2)` | Relative Gamma ratios |
| `Analysis/GammaRatio.lean`, `DBN/DobnerGammaRatio.lean` | Proved uniform quadratic relative Gamma/xi-Gamma estimates; actual normalized contour pointwise bound | Remote tails, integrated convergence, all-index domination |
| Mathlib `Complex/LogBounds.lean`: `Complex.norm_log_sub_logTaylor_le` | Certified complex-log Taylor remainders for small `u/s` | A Gamma or log-Gamma expansion |
| Mathlib `Gamma/Beta.lean`: `GammaSeq_tendsto_Gamma`; `Gamma/Digamma.lean` | Euler-limit foundation, nonvanishing, recurrence, logarithmic derivative | The required sectorial remainder; the source search found no ready-made theorem |

### Attractive names that are not shortcuts

- `AsympEnv` and `PointwiseEnvelope` store an **already-proved** real error
  inequality. Their algebra can package scalar estimates later, but cannot
  produce the complex Gamma estimate. Pointwise envelopes are `ℝ→ℝ`, not a
  ready-made complex, multi-parameter uniform approximation interface.
- `SlabTailCert.tailBound` is supplied as a proof. Finite interval checks do
  not establish its infinite tail. `eventual_bound` currently supports a
  narrow reciprocal-power family on natural indices, not these real-height
  logarithmic/exponential estimates.
- `DirectedLimitCert` concerns ordered real limits with rational truncation
  bounds. The oscillatory complex contour series is not a direct instance.
- `Analysis/GaussianTail.lean` bounds **discrete** `exp(-c*k^2)` tails. Our
  index envelope is `exp(-c*log(k+1)^2)`; use `DirichletGaussian` instead.
- `Engine/DirichletGaussian.lean` certifies tails of D for rational parameters;
  it neither evaluates the finite complex head nor bounds the heat error.
- `ParametricIntegral` may support an integral representation of a remainder,
  but its continuity theorem is local; it is not convergence at infinite height.
- Borel–Carathéodory needs analytic and real-part bounds already in hand.
  It does not supply the then-missing Gamma asymptotic for free.
- The earlier `simplicalcomplex/MATH.md` connection is a conceptual analogy,
  not an analytic estimate or a formal bridge for the gap identified at that stage.

## Historical dependency-ordered execution plan

> The instructions and exit criteria below record the pre-completion plan.
> The final implementation used the [linear-cutoff route](dbn-linear-cutoff-completion.md),
> not the proposed fractional-power split in step 3. All obligations needed
> for `Lambda_nonneg` are now discharged; these proposed intermediate bounds
> are not claims about the exact statements ultimately formalized.

### 1. Gamma-ratio foundation — now proved

Implemented in `Analysis/GammaRatio.lean` and
`Analysis/DBN/DobnerGammaRatio.lean`. See the
[proved bounds and derivation](dbn-gamma-ratio.md).

The actual Gamma ratio is controlled by a quadratic exponential with explicit
error `exp(8r/y + 4r²/y² + 8r³/y²)-1`, for `y≥2`, `Re(s)≥-y/2`,
`r=|u|≤y/2`. The actual xi-Gamma version, for `y≥4`, is

```text
|xiGamma(s+u)/(xiGamma(s) exp(ell*u/2+u²/(4s))) - 1|
  ≤ (1+r/y)² exp(8r/y+4r²/y²+4r³/y²)-1,
ell = Log(s/(2pi)).
```

This region covers every fixed vertical strip at sufficiently large height.
There is both a proved growing-radius Gamma bound (`y≥h⁵`, `r≤h³`,
error at most `exp(20/h)-1`) and proved uniform bounded-displacement xi-Gamma
convergence. No Stirling hypothesis is assumed: finite Euler factors,
justified logarithmic telescoping, explicit Taylor remainders, and the actual
GammaSeq limit provide the proof.

`saddleIntegrand_quadratic_relative_error_bound` now connects this to the
actual normalized contour integrand. This is a **pointwise** bound; at the
stage of this audit, the integrated uniform bounds had not yet been proved.
They were subsequently supplied by the centered-kernel and limit proofs.

**Exit criterion achieved:** compiled relative estimates for the actual Gamma
and xi-Gamma factors on a region covering the required strips, with explicit
uniform constants. No numerical checks or new axioms stand in for this step.

### 2. Derive centered quantitative contour bounds

Reuse the now-proved contour identities; do not reprove their bookkeeping.
Choose the pole-free line
`Re(z)=max(2, x+2aL)`, or justify a further local deformation explicitly.
Use `saddleIntegrand_normalized_factorization` to expose the Gamma ratio.

A key correction to our earlier attempts: **center the real integration
variable near Im(s)** before bounding tails. The existing fixed-parameter
majorant can contain an `exp(O(y^2))` constant. Its mere integrability cannot
prove the required asymptotic. We need explicit parameter dependence so that
the Gaussian tail beats the normalization loss.

Prove the central and remote bounds separately. Use polynomial absorption,
Gaussian moments, and `IntegralTail.of_gaussian` AFTER proving the normalized
majorants. For far tails, an exponent such as `-c*y^(4/3)+C*y+o(y^(4/3))`
would suffice; a hidden positive `C*y^2` would not.

**Exit criterion:** actual integral error inequalities with every dependence
on a, M, y, and L visible, not just an existential constant for fixed w,L.

### 3. Close fixed-index convergence and all-index domination

For fixed k, combine the local Gamma estimate, the exact Gaussian main
integral, and the remote tails to prove A uniformly in x.

For B, retain a medium/large index split rather than seeking global relative
convergence. [Dobner's Lemma 4](https://arxiv.org/html/2005.05142v2#S4) supplies
an established contour-estimate architecture; specialize it to zeta and our
`b=4a` normalization, rather than formalizing the extended Selberg class.
At that stage, the exponents and constants still needed checked translation
into our conventions; the final implementation instead used linear cutoffs.

A sufficient target is:

```text
medium: L ≤ y^(3/5)/(4a)
        |T_k(s)| ≤ C exp(-a L^2/2 + M L)

large:  L > y^(3/5)/(4a)
        |T_k(s)| ≤ C exp(C0*y - 2a L^2/5).
```

The reciprocal-normalization theorem supplies the permitted linear-height
loss in the second estimate. Since `L^2 > y^(6/5)/(16a^2)`, that loss is
eventually absorbed into a portion of the log-Gaussian decay. Completing the
square absorbs `M L` in the first estimate. Both then yield B, for example
with `c=a/10` after enlarging constants and thresholds.

**Exit criterion:** one majorant and one height threshold valid for all k.
The proposed unnormalized large-index and medium-index relative bounds
required new mathematics at that stage. The displayed targets describe the
original plan, not the exact bounds used in the completed linear-cutoff proof.

### 4. Reuse the existing telescoping tail and finish the limit

Convert the log-Gaussian envelope in B to a constant multiple of
`DirichletGaussian.envelope`. The completing-square argument in `norm_term_le`
already provides this mechanism; apply it with damping c and real part zero.
Use the same envelope for the main terms, with their fixed-strip constant.

The sum of both residual tails is then at most `K*2/(N+1)`, uniformly in x and
all sufficiently large y. Choose N first. Apply A to its finite head second.
This proves uniform convergence on each fixed strip and hence on upward
translates of every compact set. The `translate_convergence` proof supplies a
working model for this assembly; no new general-purpose limit engine is needed.

### 5. Apply the existing endpoint and audit

Prove `NormalizedHeatApproximation a` for every real a>0, apply
`Lambda_nonneg_of_normalizedHeatApproximation`, and export an unconditional
`Lambda_nonneg : 0 ≤ Lambda`.

Completion means:

- the final theorem mentions no approximation or envelope premise;
- it concerns the existing actual `H` and `Lambda` definitions;
- library and DBN tests compile through `lean-runtime`;
- the theorem's full axiom set is pinned to standard kernel axioms;
- trust, test wiring, and docs checks pass;
- docs distinguish `Lambda≥0` from the additional RH-side claim `Lambda≤0`.

## Historical work discipline

The priority was Gamma-ratio analysis rather than more certificate packaging,
with reuse of existing tail adapters and contour proofs. Interval checkers
were reserved for finite scalar inequalities after analytic reductions;
explicit cutoffs were optional because qualitative convergence sufficed.
At the time of this audit, the Gamma remainder had been proved, but the
uniform integrated estimates and limit assembly still required substantial
formal-analysis work. That work is now completed in `DobnerCenteredKernel.lean`
and `DobnerLimit.lean`.
