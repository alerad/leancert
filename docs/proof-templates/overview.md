# Proof Templates

Proof templates are reusable certificate strategies.  Use them when your theorem
is not just one interval inequality, but has a repeatable proof shape:
generated rows, main/error envelopes, perturbations of a base object,
product-integral identities, or contour-shift bookkeeping.

A proof template usually has this form:

```text
structured certificate data
+ a checker or reusable soundness theorem
+ project-specific side conditions
= semantic theorem in Lean
```

Unlike direct tactics, proof templates do not always close a theorem from a raw
expression.  Some have executable checkers; others organize proof obligations
that must be supplied by project-specific mathematics.

| Template | Use when you have... |
|---|---|
| [Checker-to-theorem](checker-to-theorem.md) | a boolean checker and a theorem explaining what success means |
| [Table certificates](table-certificates.md) | many generated finite rows with one row checker |
| [Asymptotic envelopes](asymptotic-envelopes.md) | a summatory function, main term, and nonnegative error term |
| [Pointwise envelopes](pointwise-envelopes.md) | a real-variable approximation and an error radius |
| [ConstantFactory](constant-factory.md) | a base object with reusable moments and finite perturbations |
| [QProduct finite integrals](qproduct-finite-integrals.md) | exact finite product-integral identities |
| [Contour-shift certificates](contour-shift.md) | rectangle identities, horizontal vanishing, vertical limits, and residue data |
| [Directed-limit certificates](directed-limits.md) | a limit object enclosed by computable truncations with a computable tail majorant |
| [Wall quotients](wall-quotients.md) | a `0/0` removable singularity whose enclosure must come from derivative data |
