# Contour-Shift Certificates

`LeanCert.Analysis.ContourShift` packages reusable contour-shift bookkeeping for
complex-analysis arguments.

The current layer is intentionally a certificate engine, not an automatic
residue calculator.  It centralizes:

- named rectangle side integrals;
- the rectangle boundary orientation convention;
- finite rectangle shift identities;
- horizontal-side vanishing from norm bounds;
- vertical-line limit passing;
- stable finite residue sums.

## Import

```lean
import LeanCert.Analysis.ContourShift
```

or through the aggregate API:

```lean
import LeanCert
```

## Rectangle Side API

For rectangle corners `z w : ℂ`, the named side integrals are:

```text
bottomIntegral
topIntegral
rightIntegral
leftIntegral
rectBoundary
```
The boundary convention is:

```text
bottom - top + I * right - I * left
```

The holomorphic rectangle theorem is exposed in this notation:

```text
rectBoundary_eq_zero_of_continuousOn_of_differentiableOn
```
This is a wrapper around mathlib's rectangle Cauchy-Goursat theorem.

## Finite Vertical Shift Certificates

`VerticalShiftCert` stores a boundary identity:

```text
rectBoundary f z w = (2 * Real.pi * Complex.I) * residueSum
```
Its soundness theorem rearranges this into the vertical-shift identity:

```lean
#check LeanCert.Analysis.ContourShift.VerticalShiftCert.vertical_shift
```
For holomorphic rectangles with no residue contribution, use:

```lean
#check LeanCert.Analysis.ContourShift.VerticalShiftCert.ofHolomorphicRectangle
```
## Shift-Oriented Segment Integrals

For analytic-number-theory contour shifts, the symmetric vertical-line notation
is often more convenient:

```text
verticalIntegral F σ T
topHorizontalIntegral F σ₀ σ₁ T
bottomHorizontalIntegral F σ₀ σ₁ T
```
Here `verticalIntegral F σ T` is the upward integral over
`σ + it`, `-T <= t <= T`.

## Finite Rectangle Shift Certificates

`RectangleShiftCert F σ₀ σ₁ T` stores the finite identity:

```text
verticalIntegral F σ₀ T =
  verticalIntegral F σ₁ T
    - topHorizontalIntegral F σ₀ σ₁ T
    - bottomHorizontalIntegral F σ₀ σ₁ T
    + (2 * Real.pi * Complex.I) * residueSum
```
The residue theorem is not baked into this structure.  Projects can supply the
finite rectangle identity from a residue theorem, from a specialized local
calculation, or from a future LeanCert residue constructor.

With the residue term as written, the identity matches the positively-oriented
rectangle residue theorem when `σ₁ < σ₀` (a leftward shift). For `σ₀ < σ₁` the
positively-oriented residue theorem yields the opposite sign on the residue
term, so a constructor for that case must negate the residues it stores.

## Horizontal Vanishing

For limit-passing shifts, horizontal sides can be supplied directly:

```text
HorizontalVanishCert
```
or derived from explicit norm bounds:

```text
HorizontalBoundCert
HorizontalBoundCert.toVanishCert
```
The bound certificate stores a nonnegative bound tending to zero and proves both
horizontal side norms are bounded by it.

## Infinite Contour-Shift Certificates

`ContourShiftCert F σ₀ σ₁` is the main limit-passing certificate.  It stores:

- a height sequence `T : Nat -> ℝ`;
- finite rectangle certificates at each height;
- stable pole and residue data;
- left and right vertical-line limits;
- horizontal vanishing.

The chosen outputs are:

```lean
#check LeanCert.Analysis.ContourShift.ContourShiftCert.leftValue
#check LeanCert.Analysis.ContourShift.ContourShiftCert.rightValue
#check LeanCert.Analysis.ContourShift.ContourShiftCert.residueSum
```
The main soundness theorem is:

```text
ContourShiftCert.shift_identity'
```
which proves:

```text
leftValue =
  rightValue + (2 * Real.pi * Complex.I) * residueSum
```

There is also an existential version:

```lean
#check LeanCert.Analysis.ContourShift.ContourShiftCert.shift_identity
```
## Intended Workflow

Use this layer when the analytic proof has already been decomposed as:

```text
finite rectangle identity
+ horizontal side vanishing
+ vertical-line convergence
+ stable residue data
= contour shift identity
```

A project should prove the residue identities and analytic decay estimates in
project-specific files, then package them into `RectangleShiftCert`,
`HorizontalBoundCert`, and `ContourShiftCert`.

## Current Scope

This layer does not yet automate:

- residue discovery;
- meromorphic-on-region hypotheses;
- infinite pole exhaustion;
- Laurent or simple-pole residue calculation.

Those are natural future constructors.  The current API is the reusable
orientation and limit algebra that those constructors should target.
