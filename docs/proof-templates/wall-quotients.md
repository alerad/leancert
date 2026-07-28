# Wall Quotients (Removable Singularities)

Module: `LeanCert.Analysis.WallQuotient`

Interval evaluation degenerates at a point `w` where an expression has the
form `num/den` with `num w = den w = 0`: the order-0 data is `0/0` and a naive
enclosure is vacuous. The information lives one jet order up. The order-1
enclosure is the Cauchy mean value theorem in certificate form:

```lean
#check LeanCert.Analysis.WallQuotient.quotient_mem_of_deriv_ratio_bounds
```
The derivative-ratio bounds `lo · den′ ≤ num′ ≤ hi · den′` are ordinary,
wall-free interval-evaluation targets, so the theorem converts a singular
enclosure problem into a regular one.

Model instance (`expm1_div_self_mem`): `(eˣ − 1)/x ∈ [1, e]` on `(0, 1)`,
with the wall at `x = 0` and the regular data `1 ≤ eˣ ≤ e`.

## Order-k walls

For numerator and denominator vanishing to order `k`, the derivative data is
packaged as a `DerivLadder k w b`: explicit functions `f 0, …, f k` with each
`f (i+1)` the derivative of `f i` on `(w, b)`, all levels below the top
vanishing at the wall. `quotient_mem_of_derivLadder` traps the bottom-level
quotient by ratio bounds on the top level, by induction through the order-1
core; positivity propagates down the denominator ladder by the mean value
theorem (`DerivLadder.pos_of_top`).

Order-2 model instance (`expm1_sub_self_div_sq_mem`):
`(eᵗ − t − 1)/t² ∈ [1/2, e/2]` on `(0, 1)`.

## Variants

`quotient_mem_of_deriv_ratio_bounds_left` handles walls at the right
endpoint, and `quotient_mem_of_deriv_ratio_bounds_two_sided` traps the
quotient on a punctured interval around an interior wall.

## Status and roadmap

Remaining extensions:

* ladders for the symmetric log integrand of the Li2 development (an order-2
  wall at `t = 0`), replacing its bespoke tail lemmas;
* engine hookup: a wall-aware partition step for integral certification that
  evaluates jets at singular endpoints and the standard interval engine
  elsewhere.
