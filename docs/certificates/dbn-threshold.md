# Classical de Bruijn–Newman certificate

The classical threshold certificate for the **actual DBN heat integral** is
unconditional and kernel-checked:

```lean
import LeanCert.Analysis.DBN.Threshold

open LeanCert.Analysis.DBN

example : ∃ a : ℝ, a ≤ (1/2 : ℝ) ∧
    ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t :=
  dbn_certificate
```

Here the normalization is

```text
H t z = ∫ u > 0, exp(t*u²) * Phi(u) * cos(z*u) du
Phi(u) = Σ n ≥ 1, (2π²n⁴ exp(9u) − 3πn² exp(5u)) exp(−πn² exp(4u)).
```

## Public conclusions

- `Lambda : ℝ` is the infimum of the real-zero times. Nonemptiness and
  lower-boundedness are proved, not supplied by callers.
- `Lambda_isLeast`: the infimum is attained.
- `real_zeros_iff_Lambda_le`: all zeros of `H t` are real **iff** `Lambda ≤ t`.
- `H_Lambda_real_zeros`: the threshold itself has real-only zeros.
- `nonreal_zero_of_lt_Lambda`: every strictly earlier time has a nonreal zero.
- `Lambda_unique`: the zero characterization uniquely determines the threshold.
- `Lambda_le_half`: the threshold is at most one half.
- `dbn_certificate`: the existential, assumption-free packaged statement.

This is a **qualitative classical certificate**. It does not assert the Riemann
hypothesis, a nonnegative lower bound, or an upper bound sharper than one half.
The bad-time proof does not calculate a specific bad-time index or locate a
particular nonreal zero.

## Proof chain

The endpoint and forward half of the argument are described in
[the real-zero and contraction certificate](dbn-real-zeros.md).
`RealZeroTimes` proves closedness and nonemptiness; `ForwardPreservation`
proves upward closure. The new bad-time argument supplies lower-boundedness.

### 1. A four-point inequality from real zeros

`H_four_point_normSq` in `FourPoint.lean` uses the actual arbitrary-time polynomial
cutoffs, retaining zero multiplicities. For each real root, the relevant
squared norm factor has the form `1 + q*a` with `a ≥ 0`.

The elementary inequality

```text
(1 + 4a)^6 ≤ (1 + 9a)(1 + a)^15
```

is proved by expanding the difference into a polynomial with nonnegative
coefficients. Multiplication over each finite cutoff and locally uniform
convergence give

```text
normSq(H t 0)^10 * normSq(H t (2y i))^6
  ≤ normSq(H t (3y i)) * normSq(H t (y i))^15
```

whenever `t` is a real-zero time. The weights at squared arguments
`0, 1, 4, 9` cancel constant, linear, and quadratic polynomials in that
squared argument.

### 2. Gaussian recovery of the kernel

`KernelRegularity` proves continuity of the defining series and an integrable
Gaussian bound for its even extension `evenPhi u = Phi |u|`.

`BackwardGaussian` defines

```text
gaussianAverage c x = ∫ v, exp(−v²) * evenPhi(x + v/c) dv
```

and proves both:

```text
gaussianAverage (n+1) x → sqrt(π) * evenPhi x
gaussianAverage c x =
  2c * exp(−c²x²) * Re(H (−c²) (2c²x i))       (c > 0).
```

The first is dominated convergence, including at the origin. The second is
an exact change of variables, reflection of the negative half-line, and the
cosh identity for imaginary spatial arguments.

### 3. A strict obstruction in the actual kernel

`Phi_four_point_obstruction` in `KernelObstruction.lean` proves

```text
Phi(3) * Phi(1)^15 < Phi(0)^10 * Phi(2)^6.
```

The lower estimates use the first positive summand of the actual series;
the upper estimates use the proved series envelope. Coarse Taylor lower
bounds on the exponential suffice. There is no numerical quadrature, floating
point oracle, or native evaluation.

### 4. A bad time and a finite threshold

If every time `−(n+1)²` were good, step 1 would give the opposite inequality
for the Gaussian averages. The common Gaussian factors cancel exactly.
Step 2 passes the inequality to `Phi`, contradicting step 3.

Thus `exists_bad_negative_square` proves a genuinely bad time.
`realZeroTimes_bddBelow` follows from this and forward preservation.
Closedness then gives the attained infimum and all conclusions in
`Threshold.lean`.

The argument uses a finite-product obstruction rather than importing or
assuming Newman's full classification theorem.

## Verification and trust

`LeanCert.Test.DBNThreshold` checks the obstruction, Gaussian recovery
(including zero and negative centers), existence of nonreal zeros, the finite
threshold, uniqueness, and its endpoint. It includes `assert_no_sorry` and
exact transitive axiom guards.

The final theorem depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

The public conclusions are also pinned as `kernel` in
`Tests/TrustManifest.lean`. No custom axioms, admitted analytic hypotheses,
native-decide trust, dependency changes, or toolchain changes are used.

From the repository root:

```sh
lean-runtime build LeanCert.Test.DBNThreshold LeanCert.Test.DBNForwardPreservation \
  LeanCert.Test.DBNRealZeroTimes LeanCert.Test.DBNRealZeros LeanCert
lean-runtime check --using . Tests/TrustManifest.lean Tests/AxiomAudit.lean
python3 scripts/check_test_wiring.py
```

## Nonnegative lower bound — now proved

[Newman nonnegativity](dbn-nonnegative.md) proves the unconditional
`Lambda_nonneg : 0 ≤ Lambda`. Together with `Lambda_le_half`, the existing
actual threshold satisfies `0 ≤ Lambda ≤ 1/2`.

The Gaussian Dirichlet series, recurrence, zero transfer, normalized contour
approximation, and final threshold argument are all connected. This does not
prove the RH-side inequality `Lambda ≤ 0`.
