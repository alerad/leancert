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
#check LeanCert.Validity.verify_limit_interval
```
Tightening a bound is a change of the index `N` and the endpoints — no new
mathematics at the use site.

`DirectedLimitCert` packages the two families as a structure, and
`DirectedLimitCert.approx_tendsto_limit` derives convergence of the
truncations to the limit whenever the tails vanish.

## Downstream instances

The prime q-product instance, its convergence proofs, and difference-calculus
tail majorants now live in **leancert-qproduct**, under
`QProduct.LeanCert.LimitCert` and `QProduct.LeanCert.Sparse`.
See the [migration guide](../qproduct-migration.md).

The generic checker and `DirectedLimitCert` remain in LeanCert. Applications
supply their own truncations and tail proofs; LeanCert need not import them.
