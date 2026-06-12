# Wall Quotients (Removable Singularities)

Module: `LeanCert.Analysis.WallQuotient`

Interval evaluation degenerates at a point `w` where an expression has the
form `num/den` with `num w = den w = 0`: the order-0 data is `0/0` and a naive
enclosure is vacuous. The information lives one jet order up. The order-1
enclosure is the Cauchy mean value theorem in certificate form:

```lean
theorem quotient_mem_of_deriv_ratio_bounds
    {num den num' den' : ℝ → ℝ} {w b lo hi : ℝ}
    (hnum0 : num w = 0) (hden0 : den w = 0)
    -- continuity on [w, b], HasDerivAt on (w, b), den' > 0 on (w, b)
    (hlo : ∀ x ∈ Ioo w b, lo * den' x ≤ num' x)
    (hhi : ∀ x ∈ Ioo w b, num' x ≤ hi * den' x)
    {t : ℝ} (ht : t ∈ Ioo w b) :
    num t / den t ∈ Icc lo hi
```

The derivative-ratio bounds `lo · den′ ≤ num′ ≤ hi · den′` are ordinary,
wall-free interval-evaluation targets, so the theorem converts a singular
enclosure problem into a regular one.

Model instance (`expm1_div_self_mem`): `(eˣ − 1)/x ∈ [1, e]` on `(0, 1)`,
with the wall at `x = 0` and the regular data `1 ≤ eˣ ≤ e`.

## Status and roadmap

This is the order-1 core. Planned extensions:

* order-`k` walls (numerator and denominator vanishing to higher order), via
  iterated Cauchy MVT or Taylor remainders — the case needed by integrands
  like the symmetric log combination in the Li2 development, whose wall data
  currently uses bespoke tail lemmas;
* a left-of-wall variant and a two-sided wrapper;
* engine hookup: a wall-aware partition step for `interval_integrate` that
  evaluates jets at singular endpoints and the standard interval engine
  elsewhere.
