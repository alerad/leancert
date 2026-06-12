# Directed-Limit Certificates

Module: `LeanCert.Validity.DirectedLimit`

Use this template when a real limit object — an infinite series, an infinite
product integral, a directed `sInf`/`sSup` — is approximated by computable
rational truncations with a computable tail majorant:

```text
x ≤ approx N                 (every truncation bounds the limit from above)
approx N - tail N ≤ x        (tail-corrected truncation bounds it from below)
```

Given these two inequality families (supplied once, as mathematics), any
two-sided rational enclosure of `x` becomes a single boolean evaluation:

```lean
theorem verify_limit_interval {x : ℝ} {approx tail : ℕ → ℚ}
    (hupper : ∀ N, x ≤ (approx N : ℝ))
    (hlower : ∀ N, (approx N : ℝ) - (tail N : ℝ) ≤ x)
    (N : ℕ) (lo hi : ℚ)
    (hcheck : checkLimitInterval approx tail N lo hi = true) :
    (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)
```

Tightening a bound is a change of the index `N` and the endpoints — no new
mathematics at the use site.

`DirectedLimitCert` packages the two families as a structure, and
`DirectedLimitCert.approx_tendsto_limit` derives convergence of the
truncations to the limit whenever the tails vanish.

## Worked instance: the prime q-product limit

`LeanCert.QProduct.LimitCert` packages the prime sandwich
(`primeLambda_sandwich`) as `primeLambdaLimitCert`, with shifted truncations
`approx N = primeFRat (N + 2)` and tails
`tail N = primeSandwichErrorRat (N + 2) (oddAbove (N + 2))`, so all side
conditions (truncation size, tail parity, tail dominance) are discharged
uniformly. Bounds then read:

```lean
example : ((19 / 36 : ℚ) : ℝ) ≤ primeLambda ∧ primeLambda ≤ ((7 / 12 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval
    primeLambda_le_shiftedTrunc
    shiftedTrunc_sub_tail_le_primeLambda
    1 (19 / 36) (7 / 12)
    (by native_decide)
```

Compare `LeanCert.QProduct.verify_primeLambda_interval_of_forall`, which
requires a per-use `∀ M` tail hypothesis: this template factors that
hypothesis out into the certificate, once.

## The analytic bridge

For any decidable exponent predicate, the directed limit of the q-product
truncation integrals is the integral of the infinite product
(`LeanCert.QProduct.sInf_F_filter_eq_integral_tprod`); the prime instance
identifies `primeLambda` with the integral of the infinite prime product
(`primeLambda_eq_integral_tprod`), and the positive-exponent instance gives
Sandham's integral (OEIS A258232). Certified enclosures of these directed
limits are therefore enclosures of the analytic constants.

## Tail majorants from the difference calculus

`LeanCert.QProduct.Differences` provides the tail collapse: with a retained
exponent `1` (or `2`), the gap between a truncation and any finer truncation
is at most one computable moment, `F S - F T <= moment (S.erase 1) m`
(respectively `<= 2 * moment (S.erase 2) m`), where `m` bounds the missing
exponents from below. These are ready-made `tail` functions for certificates
over arbitrary exponent systems.

## Other candidate instances

The Li2 tail-interval decomposition and the BKLNW tail bounds follow the same
truncation-plus-tail shape and can be repackaged as `DirectedLimitCert`
values; the monotone-from-below variant is obtained by negation.
