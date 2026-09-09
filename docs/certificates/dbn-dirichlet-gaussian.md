# DBN lower-bound route: Phase 1

**Proved:** the Gaussian-damped Dirichlet series is entire, has an explicit
order-at-most-two growth bound, and has a complex zero for every positive
damping parameter. These Phase 1 results alone do not prove `0 ≤ Lambda`. The full bound is
now proved by `Lambda_nonneg`; see [the completed proof](dbn-nonnegative.md).

For `a > 0`, define

```text
D_a(s) = sum over n ≥ 1 of exp(-a*(log n)^2 - s*log n).
```

`term a s k` indexes the integer `k+1`. `partialSum a N s` contains integers
`1,...,N`, so its omitted tail starts at `N+1`. The negative-time
normalization is `a = -t/4`.

## Symbolic analytic results

```lean
import LeanCert.Analysis.DirichletGaussian

open LeanCert.Analysis.DirichletGaussian

example {a : ℝ} (ha : 0 < a) : Differentiable ℂ (series a) :=
  entire_series ha

example {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ‖series a s‖ ≤ Real.exp ((2+1/a)*(1+‖s‖)^2) :=
  growth_bound ha s

example {t : ℝ} (ht : t < 0) : ∃ s : ℂ, series (-t/4) s = 0 :=
  negative_time_exists_zero ht
```

The proof is uniform in the parameter, not a collection of numerical examples:

1. Completing the square bounds each term by an exponential constant times
   the telescoping majorant `2*(1/(k+1) - 1/(k+2))`.
2. This proves absolute convergence and uniform convergence on every
   half-plane `Re(s) ≥ -R`, hence entire dependence on `s`.
3. Summing the majorant yields the displayed quadratic-exponential growth bound.
4. If the entire series had no zeros, the existing zero-free growth theorem
   would express it as `exp(P(s))`, with `degree(P) ≤ 2`.
5. Dominated convergence gives `D_a(x) → 1` as real `x → +∞`. Consequently,
   the real polynomial `Re(P(x)) = log |D_a(x)|` tends to zero and must vanish.
   But `D_a(0)` is real and strictly greater than one, a contradiction.

## Executable tail certificates

`LeanCert.Engine.DirichletGaussian.checkTail a R N precision` evaluates a
sufficient cutoff test using rational arithmetic and a certified lower bound
on `log(N+1)`. Successful checking proves

```text
R + 2 ≤ a*log(N+1)
⇒ |D_a(s) - partialSum a N s| ≤ 2/(N+1), for Re(s) ≥ -R.
```

```lean
import LeanCert.Engine.DirichletGaussian

open LeanCert.Analysis.DirichletGaussian
open LeanCert.Engine.DirichletGaussian

example {s : ℂ} (hs : 0 ≤ s.re) :
    ‖series 1 s - partialSum 1 15 s‖ ≤ 1/8 := by
  have h := certified_tail (a := 1) (R := 0) (N := 15) (precision := 4)
    (by decide +kernel) (s := s) (by simpa using hs)
  norm_num at h ⊢
  exact h
```

`certified_disk` composes this tail error with a **separately proved** disk
bound for the finite head. The engine does not yet evaluate that complex
head, isolate zeros, or certify a contour winding number. A failed check
means only that this sufficient test did not succeed; it does not disprove
a tail bound. The simple cutoff can be very large when damping is small.

## Phase 2 status

[Phase 2 progress](dbn-dobner-route.md) now proves vertical recurrence,
zeros at arbitrarily large heights in a fixed strip, local zero transfer,
and the logarithmic coordinate geometry. The analytic approximation is also
proved in `DobnerLimit.lean`, completing the unconditional bound.

### Full bridge — now completed

The zeros above belong to `D_a`, not the DBN heat integral `H`. The completed
bridge combines vertical recurrence, a uniform approximation of an
appropriately transformed/normalized heat integral by this series, and a
zero-transfer argument with the correct location. It proves a nonreal zero
of `H t` for **every** `t < 0`, so the existing threshold characterization
yields `0 ≤ Lambda`.

The key analytic and checker theorems are pinned as kernel-trusted in
`Tests/TrustManifest.lean`. Regression tests include successful and rejected
rational cutoffs and a genuine certified tail bound, using `decide +kernel`, not
`native_decide`.
