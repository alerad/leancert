# Domain Libraries

Domain libraries package specialized mathematics on top of LeanCert's direct
automation, proof templates, and checker architecture.

Start here when your theorem is not just a raw numerical goal, but belongs to a
recognizable mathematical domain with reusable definitions and certificate
families.

| Domain | Use when you have... |
|---|---|
| [Analytic Number Theory](ant/overview.md) | Chebyshev functions, Abel sums, Euler products, Dirichlet sums, Mertens sums, or explicit-PNT transfer schemas |

Domain pages should usually point back to the proof template they build on.  For
example, ANT asymptotic certificates use the reusable `AsympEnv` and
`PointwiseEnvelope` templates.
