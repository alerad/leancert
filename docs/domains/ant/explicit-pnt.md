# Explicit-PNT Transfer Schemas

Explicit-PNT transfer schemas package the reusable inequality algebra behind:

```text
ψ-bound -> θ-bound -> π-bound
```

Core theorem schemas:

```text
psi_to_theta_bound
theta_to_pi_bound_of_decomposition
theta_to_pi_bound
```
These theorems are project-agnostic.  They do not define `ψ`, `θ`, `π`, or
`Li`; project files supply those definitions and the partial-summation
decomposition identities.

Detailed API reference:

[ANT Certificates → Explicit-PNT Compiler Schemas](../../certificates/ant.md#explicit-pnt-compiler-schemas)
