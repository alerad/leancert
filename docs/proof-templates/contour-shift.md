# Contour-Shift Certificates

Use `ContourShiftCert` when a contour-shift proof has already been decomposed
into reusable analytic pieces:

```text
finite rectangle identity
+ horizontal side vanishing
+ vertical-line convergence
+ stable residue data
= infinite contour-shift identity
```

Core APIs:

```text
RectangleShiftCert
HorizontalVanishCert
HorizontalBoundCert
ContourShiftCert
ContourShiftCert.shift_identity'
```
Important scope note: this template centralizes orientation and limit-passing
algebra.  It does not yet automate residue calculation, meromorphic-region
construction, or infinite pole exhaustion.

Detailed API reference: [Contour-Shift Certificates](../certificates/contour-shift.md).

## Holomorphic strips with integrable vertical lines

Import `LeanCert.Analysis.ContourShift.Decay` for:

```text
RectangleShiftCert.ofHolomorphicStrip
horizontalBoundOfStrip
integral_vertical_eq_of_holomorphic_of_vanish
```

These construct zero-residue certificates, derive horizontal vanishing from
strip bounds, and connect the limiting identity to actual integrable vertical
lines. They still require proofs of holomorphy and decay.

A concrete application is the [DBN Gaussian-Gamma contour shift](../certificates/dbn-dobner-contour-shift.md),
which proves those hypotheses for each fixed set of parameters.
