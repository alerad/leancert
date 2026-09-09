# DBN analytic bridge: exact representation and asymptotics proved

**Completion update:** the full lower bound `0 ≤ Lambda` is now proved in
`DBN/DobnerLimit.lean`. See [the final theorem](dbn-nonnegative.md).
Descriptions of remaining work below record the earlier stage of development.


Earlier stages established the actual normalization, Gaussian contour
representation, justified Dirichlet expansion, and reciprocal Gamma bounds.
The subsequent linear-cutoff argument now proves the uniform approximation
and the unconditional lower bound. This page documents the reusable exact
representation; [the final proof](dbn-nonnegative.md) documents its completion.

## Actual Gamma normalization

`DobnerNormalization.lean` defines:

```text
xiGamma(s) = s*(s-1)*GammaReal(s)/2
GammaReal(s) = pi^(-s/2)*Gamma(s/2)
dobnerGamma(a,s) = xiGamma(s)*exp((s-J_a(s))^2/(4*a))
normalizedHeat(a,s) = xiHeat(-4*a,J_a(s))/dobnerGamma(a,s)
```

These are actual functions, not abstract witnesses supplied to a connector.
The denominator is nonzero and the quotient is holomorphic on `Im(s)>0`.
The exact multiplication identity is proved there. At zero damping, the
normalization recovers `riemannZeta`—a useful normalization regression test.

## Exact Gaussian representation

```lean
import LeanCert.Analysis.DBN.BackwardContour

open LeanCert.Analysis.DBN MeasureTheory

example {b : ℝ} (hb : 0 < b) (s : ℂ) :
    Integrable (verticalGaussianIntegrand b 2 s) :=
  verticalGaussianIntegral_integrable b hb 2 s

example {b : ℝ} (hb : 0 < b) (s : ℂ) :
    (∫ x : ℝ, verticalGaussianIntegrand b 2 s x) =
      (Real.sqrt Real.pi : ℂ)*xiHeat (-b) s :=
  verticalGaussianIntegral b hb 2 s
```

Here the real-parameter integrand is

```text
exp((s-(sigma+i*sqrt(b)*x))^2/b) * riemannXi(sigma+i*sqrt(b)*x).
```

The theorem works for **every real sigma**, not only 2. A complex-centered
Gaussian identity and Fubini give the result directly from `H`'s defining
integral. This avoids a separate contour-shift proof at this stage. Joint
absolute integrability and absolute integrability of the resulting contour
are separately proved.

## Justified infinite Dirichlet expansion

`DobnerGammaBounds.lean` proves an absolute Gamma bound from Euler's integral
and a polynomial prefactor bound on `Re(s)=2`. Together with Gaussian decay,
these prove `gammaContourWeight_integrable`.

`hasSum_integral_zeta_vertical` then justifies termwise integration against
any integrable weight on that line. Its proof controls the sum of the
integrals of the term norms; it does not infer interchange from pointwise
summability alone.

`DobnerDirichlet.lean` defines the actual contour terms, proves their
summability and their exact heat-function sum, and specializes to the
logarithmic evaluation chart:

```lean
import LeanCert.Analysis.DBN.DobnerDirichlet

open LeanCert.Analysis.DBN

example (a : ℝ) (s : ℂ) : Summable (normalizedContourTerm a s) :=
  normalizedContourTerm_summable a s

example {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (∑' k, normalizedContourTerm a s k) = normalizedHeat a s :=
  normalizedContourTerm_tsum ha s
```

This series is **not** the Gaussian Dirichlet main term. The exact distinction
is exposed by `normalizedHeat_sub_series`:

```text
normalizedHeat(a,s) - D_a(s)
  = sum_k (normalizedContourTerm(a,s,k) - DirichletGaussian.term(a,s,k)).
```

## Reciprocal normalization growth (now proved)

`DobnerGammaReciprocal.lean` proves, for every fixed `a>0` and strip width
`M≥0`, the unconditional bound

```text
|1/dobnerGamma(a,s)| ≤ C(a,M) exp(pi Im(s)/2)
  whenever |Re(s)| ≤ M and Im(s) ≥ 2.
```

```lean
import LeanCert.Analysis.DBN.DobnerGammaReciprocal

open LeanCert.Analysis.DBN

example (a : ℝ) (ha : 0 < a) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 2 ≤ s.im →
      ‖(dobnerGamma a s)⁻¹‖ ≤ C * Real.exp (Real.pi*s.im/2) :=
  norm_inv_dobnerGamma_le_exp_on_strip a ha M hM
```

The proof does not use complex Stirling. Euler reflection gives a reciprocal
Gamma bound in a left half-plane from the already-proved absolute Euler
integral bound. Recurrence extends this to each fixed strip: a unit shift
right cannot increase the reciprocal norm when `|Im(s)|≥1`. Compactness
bounds the remaining real Gamma factors. Finally, the chart correction
satisfies

```text
|1/dobnerGamma(a,s)| ≤ |1/xiGamma(s)| exp(a pi^2/4),
```

because `|Im(Log z)|≤pi`. Thus division by the normalization costs at most
exponential growth in height, which a sufficiently strong large-index
Gaussian tail can absorb.

**This is not a relative Gamma expansion.** The unnormalized large-index
tail and fixed-/medium-index saddle estimates required separate proofs, now
supplied by the completed contour analysis. No
saddle-point approximation hypothesis was used to prove this reciprocal bound.

## Exact approximation target — now proved

`NormalizedHeatApproximation a` is a proposition defining the
locally uniform limit

```text
normalizedHeat(a,s+i*y) - D_a(s+i*y) → 0, as real y → +infinity.
```

This definition is a proposition, not an axiom or an automatically supplied
instance. The theorem `normalizedHeatApproximation` now proves it.
`Lambda_nonneg_of_normalizedHeatApproximation` proves that establishing this
proposition for every `a>0` yields the unconditional nonnegative bound.
The actual normalization, eventual holomorphy, multiplication identity,
recurrence, zero transfer, and final threshold argument are already connected.

**The integrated uniform error control is now proved.** The relative
Gamma bounds, joint contour/index majorant, and two dominated-convergence
steps establish the actual heat approximation in `DobnerLimit.lean`.
Neither the exact residual identity alone nor a finite numerical certificate
would have sufficed; the additional analytic estimates are proved separately.

Tests: `LeanCert/Test/DBNDobnerAnalytic.lean`; trust and axiom pins are in
`Tests/TrustManifest.lean` and `Tests/AxiomAudit.lean`.

## Subsequent contour-analysis progress

[DBN contour shifts and saddle cancellation](dbn-dobner-contour-shift.md)
now proves termwise shifts between arbitrary positive vertical lines and the
exact normalized-integrand factorization. It supplies actual finite-parameter
horizontal decay and absolute integrability through the contour certificate
engine. The subsequent centered-kernel and limit proofs establish the
uniform moving-center/index estimates and the unconditional endpoint.
