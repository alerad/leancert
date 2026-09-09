# DBN nonnegative bound: experimental strategy audit

**Completion update:** the full lower bound `0 ≤ Lambda` is now proved in
`DBN/DobnerLimit.lean`. See [the final theorem](dbn-nonnegative.md).
Descriptions of remaining work below record the earlier stage of development.


For the historical dependency-ordered implementation plan, see the
[repository-audited completion strategy](dbn-completion-strategy.md).

**Historical scope: experimental strategy, not itself a proof of `0 ≤ Lambda`.** The numerical exploration
added no Lean theorem. A subsequent implementation proved the coarse
reciprocal-normalization bound below. At that stage the analytic bridge was
conditional; the [final proof](dbn-nonnegative.md) has since discharged its premises.

Reproduce the numerical diagnostics with:

```sh
python3 scripts/experiments/dbn_saddle.py
```

Dependencies: SymPy and mpmath (tested with 1.14.0 and 1.3.0).
These are floating-point, finite-window contour integrals, not certified
quadrature. Stability under precision, window, and contour changes does not
prove a tail bound or an asymptotic statement.

## 1. Calculation in the repository's normalization

Fix `a > 0`, write `s=x+iy`, `L=log n`, and set

```text
gamma(s) = s(s-1) pi^(-s/2) Gamma(s/2)/2
ell = Log(s/(2 pi))
J_a(s) = s+a ell
A_a(s) = xiHeat(-4a, J_a(s)) / [gamma(s) exp(a ell^2/4)]
m_n(s) = exp(-a L^2-s L)
```

Let `T_n(s)` denote the actual normalized contour coefficient (Lean index
`k=n-1`). The exact series identity already established is
`A_a(s) = sum_n T_n(s)`, not `A_a(s) = sum_n m_n(s)`.

For a displacement `u=z-s`, SymPy verifies the exact cancellation

```text
[(a ell-u)^2-(a ell)^2]/(4a) + ell u/2 = u^2/(4a).
```

The formal Stirling expansion for this particular prefactor gives

```text
(log gamma)'(s) = ell/2 + 3/(2s) + 5/(6s^2) + ...
log gamma(s+u)-log gamma(s)-ell u/2
  = (3u/2+u^2/4)/s + O_u(s^(-2)).
```

The error assertion here is a mathematical target, not something SymPy
certifies. Integrating the displayed correction against the shifted Gaussian
predicts, for fixed `a,n` and bounded `x`,

```text
T_n(s)/m_n(s) = 1 + P_a(L)/s + O_{a,n,M}(|s|^(-2))
P_a(L) = a^2 L^2 + 3a L - a/2.
```

The `3aL` term matters: keeping only the leading quadratic Gamma approximation
would miss it. We do NOT need this first-order rate for the final proof.

At `a=1/4`, `x=2`, `n=10`, the experiment gives:

| y | estimated abs(T_n/m_n - 1) |
|---:|---:|
| 40 | 0.0482920 |
| 160 | 0.0120825 |
| 640 | 0.00302078 |

This is consistent with the predicted fixed-index asymptotic, not a proof.
The script also tests negative real parts, `n=1`, a larger damping value,
and compares the first-order residual. Evaluating Gamma through analytic
logarithms avoids the very small absolute scale of the normalization.

**Do not target relative convergence uniformly over all n.** The quadratic
approximation has relative factor

```text
(1+a/s)^(-1/2) exp(a^2 L^2/(s+a)).
```

When `L` grows like `sqrt(y)/a`, this factor tends to `exp(-i)`, not 1.
The script probes this scaling with real `L` (not rounded integer indices).
This is a warning from the asymptotic model, not a certified counterexample.
The absolute main term is already extremely small in that range.

## 2. A weaker sufficient interface

For each fixed `a>0` and `M≥0`, it is enough to prove:

1. For each fixed integer `n≥1`,
   `sup_{|x|≤M} |T_n(x+iy)-m_n(x+iy)| → 0` as `y→∞`.
2. There exist `Y,C,c>0` such that for ALL `n≥1`, `y≥Y`, `|x|≤M`,
   `|T_n(x+iy)| ≤ C exp(-c(log n)^2)`.

The second bound is summable. The main terms also have a summable envelope,
since `|m_n(x+iy)| ≤ exp(-a(log n)^2+M log n)`.
Choose a finite cutoff from these two envelopes, then use (1) on the finite
head. This proves uniform convergence of the difference on every fixed
vertical strip, hence the existing `NormalizedHeatApproximation a` target.
A compact set's imaginary coordinates are bounded, so upward compact
translations eventually lie above the strip estimate's height threshold.

This is an elementary finite-head/infinite-tail argument. It avoids needing a
sharp rate uniform over a growing range of n. It does NOT avoid proving (2).
No uniformity as `a→0` is needed: all constants may depend on fixed `a,M`.

## 3. A known route to the difficult envelope

[Dobner, Lemma 4](https://arxiv.org/html/2005.05142v2#S4) supplies small-,
medium-, and large-index contour estimates. Specializing its parameters to
our zeta normalization suggests retaining its medium/large estimates and
using only fixed-index convergence from the small-index argument. These
estimates had not been formalized at that stage. The completed proof instead
uses the [linear-cutoff bounds](dbn-linear-cutoff-completion.md); it does not
require these exact proposed estimates.

Here is our envelope assembly, conditional on those estimates. With
`L=log n`, the medium range `L≤y^(3/5)/(4a)` gives

```text
|T_n(s)| ≤ C exp(-a L^2/2+M L).
```

The large range gives an unnormalized estimate with exponent `-2a L^2/5`.
The now-proved theorem `norm_inv_dobnerGamma_le_exp_on_strip` supplies
`1/|gamma_a(s)| ≤ C1 exp(pi y/2)`. Absorbing the constant into an
eventual bound `exp(C0 y)` yields

```text
|T_n(s)| ≤ C exp(C0 y-2a L^2/5).
```

In the large range, `L^2 > y^(6/5)/(16a^2)`, so eventually
`C0 y ≤ a L^2/5`. Thus this range is bounded by `C exp(-a L^2/5)`.
In the medium range, completing the square absorbs `M L`; both ranges admit
an envelope `C' exp(-a L^2/10)` independent of n and y.
This explains why the proposed interface is sufficient; it does not supply
the contour estimates that were missing at that stage. The Gamma reciprocal bound itself is now
proved in `DobnerGammaReciprocal.lean`.

## 4. Historical implementation order and stop conditions

> This is the original plan, not a list of open obligations. The final proof
> uses linear cutoffs and dominated convergence in place of parts of this plan.

1. **Gamma analytic foundation first.** Establish a complex Gamma ratio
   estimate with a proved remainder in the relevant upper-half-plane sector,
   with the coarse reciprocal-prefactor bound **now completed without
   Stirling**. Audit the available Euler limit,
   recurrence, reflection, and Euler–Maclaurin infrastructure before choosing
   a derivation. The local Mathlib Gamma directory has digamma definitions and
   recurrence, but the search did not identify the required sectorial theorem.
   This is substantial new analysis, not a missing `simp` call.
2. **Fixed-index contour asymptotics.** Use the exact cancellation, compact
   displacement control, and separately bounded contour tails. Contour changes
   require proof: gamma itself has poles even though xi is entire. Do not
   move a full contour through the negative real poles without residues.
   The numerical script keeps its full vertical contours at real part ≥2;
   that does not eliminate the need for remote-tail estimates.
3. **All-index envelope.** Prove the medium/large bounds, including the
   division by the small Gamma normalization. This is the critical milestone.
4. **Assemble and audit.** Prove the finite-head/infinite-tail limit, apply
   `Lambda_nonneg_of_normalizedHeatApproximation`, compile the actual theorem,
   and inspect its axioms. Then run the existing DBN, trust, and docs checks.

A reusable Gamma-ratio/remainder component would be valuable. A finite
interval-certificate engine alone cannot discharge these unbounded-height,
unbounded-index quantifiers; it would need analytic tail theorems behind it.

**Decision:** continue on this specialized fixed-strip route, not a new
numerical zero search or more conditional connector layers. Success means an
unconditional Lean theorem about the actual heat integral. It would establish
`Lambda≥0`, not `Lambda=0` (the latter would also need the RH-side upper bound).

## Implemented follow-up: contour shifts

`DobnerContourShift.lean` now proves the positive-line contour shifts, their
connection to the original normalized coefficients, and exact saddle
cancellation. The detailed [contour-analysis status](dbn-dobner-contour-shift.md)
distinguishes these contour identities from the uniform relative/tail
estimates supplied by the subsequent completed proof.
