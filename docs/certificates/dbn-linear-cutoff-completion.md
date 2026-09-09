# Completing the DBN lower bound with a linear cutoff

**Status: implemented and proved in Lean.** The actual joint majorant,
integral and series limits, `normalizedHeatApproximation`, and unconditional
`Lambda_nonneg : 0 ≤ Lambda` are now in the repository. See
[the theorem and verification details](dbn-nonnegative.md).

The derivation below records the mathematical design. The implementation
uses a strip filter and two dominated-convergence steps rather than manual
finite-head/truncation arguments; it establishes the same uniform statement.

## Research and change of strategy

Reviewed Dobner's [paper, version 2](https://arxiv.org/html/2005.05142v2),
especially §4 (Lemma 4 and its proof), §4.1, and Lemmas 5–7. Its argument
separates accurate local asymptotics from remote and large-index bounds.
For small/medium indices it uses a five-piece contour and a quadratic saddle;
large indices are treated on a positive vertical line with a weak Gamma
growth bound. Those techniques establish a stronger varying-parameter result.

**The specialization derived here is different:** keep our already-proved
full positive vertical line, fix `a>0` and the strip width `M≥0`, and use a
linear cutoff in `L=log(n)`. Our quantitative Gamma estimate need not have
small relative error throughout that whole region: its modulus growth can
be absorbed into the original Gaussian. This is enough for domination.
Convergence is needed only for each fixed index on bounded integration
intervals. No fractional powers or complex moving Gaussian saddle are needed.

The discussion below is a proposed specialization derived from the current
repository estimates, not a claim that this linear-cutoff proof is in Dobner's
paper. The two quadratic identities below were also checked with SymPy;
that check is not a Lean proof of the estimates or the final theorem.

## 1. Exact setup and the one majorant to prove

Fix `a>0`, `M≥0`. All constants and height thresholds may depend on `a,M`,
but not on `x,y,L,v`. Initially let `L` be ANY nonnegative real, not only
`log(n)`. Write

```text
s = x + i*y,       |x| ≤ M,
D = M+2,
sigma = max(2, x+2aL),
e = sigma-x-2aL,   0 ≤ e ≤ D,
d = sigma-x = 2aL+e,
u = d+i*v,
ell = Log(s/(2*pi)) = l+i*theta.
```

Thus `s+u = sigma+i*(y+v)` and `sigma≥2`. The full contour stays strictly to
the right of all Gamma poles, even when `x<0`. Also
`sigma ≤ 2aL+D`. For `y≥2*pi`, `l≥0` and `|theta|≤pi`.

Define the actual normalized kernel, without its fixed integration constant:

```text
K(s,L,v) = saddleIntegrand(4a, J_a(s), L, s+u) / dobnerGamma(a,s).
```

The proved factorization gives

```text
K = [xiGamma(s+u)/xiGamma(s) * exp(-ell*u/2)]
      * exp(-s*L + u²/(4a) - u*L).                         (1)
```

The existing positive-line contour identity, followed by translation of the
real integration variable, gives for `L=log(k+1)`:

```text
T_k(s) = (1/(2*sqrt(a)*sqrt(pi))) * integral_v K(s,L,v).     (2)
```

**Central new target:** there exist `C>0,Y>0` such that

```text
forall y≥Y, |x|≤M, L≥0, v in R,
  |K(x+i*y,L,v)| ≤ C * exp(-a*L²/4) * exp(-v²/(32a)).      (J)
```

This simultaneously supplies an integrable contour envelope and a summable
index envelope. The proof below accounts for every index and every part of
the integration line.

## 2. Elementary positive-half-plane Gamma growth

First prove the following deliberately weak bound:

```text
forall epsilon>0, exists C_epsilon>0,
forall sigma≥2, tau in R,
  |xiGamma(sigma+i*tau)|
    ≤ C_epsilon * (1+tau²) * exp(epsilon*sigma²).           (G)
```

No new complex Stirling theorem is needed:

1. The existing `norm_Gamma_le_real_Gamma` bounds
   `|Gamma((sigma+i*tau)/2)|` by `Real.Gamma(sigma/2)`.
2. For every `eta>0`, prove `Gamma(q)≤C_eta exp(eta*q²)` for `q≥1`.
   Set `n=ceil(q)`. Positivity, recurrence, and monotonicity give
   `Gamma(q)≤Gamma(q+1)≤Gamma(n+1)=n!≤n^n`, with `n≤2q`.
   Put `delta=eta/8` and `A=|1+log(delta)|`. The elementary tangent bound
   gives `log(n)≤delta*n+A`; completing the square then yields
   `n log(n)≤eta*q²+2A²/eta`. Thus take `C_eta=exp(2A²/eta)`.
   No Stirling limit or compactness argument is needed.
3. `pi^(-sigma/2)≤1`. Bound the polynomial factor by a constant times
   `(1+sigma²)(1+tau²)` and absorb `1+sigma²` into an arbitrarily small
   extra Gaussian in `sigma`.

Source-checked Mathlib APIs: `Real.Gamma_strictMonoOn_Ici` in
`Gamma/BohrMollerup.lean`, `Real.Gamma_nat_eq_factorial` in `Gamma/Basic.lean`,
and `Nat.factorial_le_pow`. The epsilon-growth conclusion is now proved in `DobnerLinearBounds.lean`;
the implementation uses a scaled tangent bound for log instead of a limit.

Also export the following consequence of the **existing proof** in
`DobnerGammaReciprocal.lean`:

```text
|1/xiGamma(x+i*y)| ≤ C_M exp(pi*y/2),  |x|≤M, y≥2.         (I)
```

The current `norm_inv_dobnerGamma_le_exp_on_strip` proof already establishes
the ingredients of (I), using `norm_inv_xiGamma_le` and the half-argument
Gamma strip bound. Export it before adding the Dobner exponential correction.
This avoids an unnecessary `log²(y)` loss below.

## 3. A coarse global kernel bound

Take the modulus of (1), using (G) and (I), but **do not** take a crude modulus
of `exp(-ell*u/2)` before combining its exponent. The exact real exponent is

```text
Re(u²/(4a) - ell*u/2 - (s+u)*L)
 = -aL² - xL + e²/(4a) - v²/(4a)
   - (aL+e/2)*l + theta*v/2.                             (3)
```

Since `l,L,e≥0`, the logarithmic contribution is nonpositive and can simply
be discarded. This is why there is **no hidden positive y² or log²(y) loss**.
Also

```text
-v²/(4a) + theta*v/2 ≤ -v²/(8a) + a*pi²/2.
```

Use (G) with `epsilon=1/(32a)`. Since
`sigma²≤8a²L²+2D²`, its growth costs at most `aL²/4` plus a constant.
Use `ML≤aL²/4+M²/a`. Combining all these estimates leaves `-aL²/2`.
Finally, for `tau=y+v`, absorb `1+tau²` into a constant times
`exp(y)*exp(v²/(16a))`, retaining Gaussian decay in `v`.

We obtain constants `C>0` and `c0=pi/2+1` such that, for all sufficiently
large `y`, **all** `L≥0`, and **all** `v`,

```text
|K(s,L,v)| ≤ C exp(c0*y - aL²/2 - v²/(16a)).              (C)
```

This estimate alone is not a uniform majorant near small `L,v`. It is used
only in the two regions where its positive linear-height loss is absorbed.

## 4. Local bound from the already-proved Gamma estimate

Let `r=|u|`. The proved xi-Gamma theorem bounds its quadratic relative error by

```text
(1+r/y)² exp(delta)-1,
delta = 8r/y + 4r²/y² + 4r³/y²,
```

provided `y≥4`, `x≥-y/2`, `r≤y/2`. Thus the norm of the quadratic-normalized
ratio is at most `(1+r/y)² exp(delta)`.

On `r≤y/2`,

```text
(1+r/y)² ≤ 9/4,
delta ≤ 5+2r²/y,
|exp(u²/(4s))| ≤ exp(r²/(4y)).
```

Consequently the **linear-normalized** ratio in brackets in (1) satisfies

```text
|xiGamma(s+u)/xiGamma(s) * exp(-ell*u/2)|
  ≤ (9/4)*exp(5)*exp(9r²/(4y)).                          (R)
```

Notice what this does NOT say: the relative error is not uniformly small for
`r` comparable to `y`. Only its growth is controlled, and that is sufficient.

Now restrict to

```text
L ≤ y/(16a),       |v| ≤ y/4.
```

If `y≥8D`, then `d≤y/4` and hence `r≤y/2`. If also `y≥2M`, the sector
condition holds. The other exact exponent identity is

```text
Re(-sL+u²/(4a)-uL)
  = -aL²-xL+e²/(4a)-v²/(4a).                            (4)
```

Using `r²=d²+v²≤8a²L²+2D²+v²`, (R) costs at most
`18a²L²/y + 9v²/(4y)` plus a constant. For `y≥72a`, these costs are at most
`aL²/4 + v²/(8a)`. Absorb `ML` as above. We get

```text
|K(s,L,v)| ≤ C exp(-aL²/2 - v²/(8a))                     (L)
```

throughout this local region, with constants independent of `L,x,y,v`.

## 5. Cover the remaining two regions: proof of (J)

### Remote integration variable

If `|v|≥y/4` and `y≥512a*c0`, then
`c0*y≤v²/(32a)`. Thus (C) gives

```text
|K| ≤ C exp(-aL²/2 - v²/(32a)).                          (V)
```

This works for every `L`, not just fixed indices.

### Large index

If `L>y/(16a)` and `y≥1024a*c0`, then
`c0*y≤aL²/4`. Thus (C) gives

```text
|K| ≤ C exp(-aL²/4 - v²/(16a)).                          (N)
```

This works for every `v`, including the center.

The three regions (L), (V), and (N) cover all `L≥0,v∈R`. Enlarge the constant
and take one common height threshold. This proves (J) on paper. One can take
that threshold above the coarse-bound threshold and

```text
max(4, 2*pi, 2*M, 8*(M+2), 72*a, 1024*a*(pi/2+1)).
```

In particular, integrating (J) proves the required all-index estimate
`|T_k(s)|≤C' exp(-a*log(k+1)²/4)`.

## 6. Fixed-index convergence without a complex saddle

For fixed `L`, define the exact Gaussian comparison kernel

```text
Q(s,L,v) = exp(-sL-aL²) * exp((e+i*v)²/(4a)).
```

Equation (1) says `K=R_linear*Q`. On every fixed bounded `v` interval, `u`
is bounded uniformly in `x`, because `e≤D`. The proved
`xiGamma_relative_error_eventually`, together with
`|u²/(4s)|≤|u|²/(4y)`, shows `R_linear→1` uniformly in `x` and those `v`.

The pure Gaussian identity is

```text
integral_v exp((e+i*v)²/(4a)) = 2*sqrt(a)*sqrt(pi),
```

so the normalized integral of `Q` is exactly `exp(-sL-aL²)`.
Use Mathlib's `integral_cexp_quadratic` with
`b=-1/(4a)`, `c=i*e/(2a)`, `d=e²/(4a)`; the exponential correction cancels.
The private `gaussian_exp_integral` in `BackwardContour.lean` is a useful
implementation example. **Do not confuse this with `verticalGaussianIntegral`,
which includes the xi function and is a different theorem.**

The norm of `Q` is bounded by
`exp(ML-aL²+D²/(4a))*exp(-v²/(4a))`. Together with (J), this supplies integrable
tails independent of `x,y`. Choose a fixed truncation interval first, use
uniform convergence on that interval second, and bound both tails. This
proves uniform fixed-index convergence on each strip.

Neither `K` nor `Q` needs to converge individually: the phase `exp(-i*y*L)`
oscillates. Apply convergence to the **difference** `K-Q`.

## 7. Sum, transfer zeros, and finish

1. Apply the existing log-Gaussian/telescoping majorant to
   `exp(-a*log(k+1)²/4)`, and also bound the main terms on the fixed strip.
2. Choose the series truncation first, then use fixed-index convergence on
   the finite head. This gives uniform convergence for all `|x|≤M`, `y≥Y`.
3. Every compact set has bounded real and imaginary parts, so this implies
   `NormalizedHeatApproximation a` for upward translates of every compact set.
4. Apply the existing `Lambda_nonneg_of_normalizedHeatApproximation` for
   every `a>0`. No new zero-location theorem or numerical certificate is needed.

## Concrete Lean implementation order

Implementation map (all listed proof stages are now discharged):

| Order | New proof | Inputs already available |
|---|---|---|
| 1 | `real_Gamma_le_exp_sq`, `norm_xiGamma_le_exp_sq` | Euler norm bound, real Gamma recurrence/monotonicity, factorial and log bounds |
| 2 | `norm_inv_xiGamma_le_exp_on_strip` | Export intermediate estimate from `DobnerGammaReciprocal` |
| 3 | `norm_xiGamma_linearRatio_le` | `xiGamma_relative_error_bound`, elementary scalar absorption |
| 4 | `centeredKernel_coarse_bound` | Exact normalized factorization, (G), (I), identity (3) |
| 5 | `centeredKernel_joint_majorant` | Local bound (L), remote absorption (V), index absorption (N) |
| 6 | `normalizedContourTerm_tendsto` | Positive-line identity, translation, pure Gaussian integral, compact/tail split |
| 7 | `normalizedHeatApproximation`, unconditional `Lambda_nonneg` | Existing sum identity, envelope, zero-transfer and threshold connector |

**Recommendation:** implement this fixed-parameter linear-cutoff route rather
than porting all of Dobner's sharper estimates. No new certificate engine is
needed. The mathematical reductions above are now implemented. The final theorem
is regression-tested and pinned by the trust and axiom audits.
