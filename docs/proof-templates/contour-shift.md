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
