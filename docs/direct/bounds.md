# Bounds And Inequalities

Use this path when the goal is a concrete inequality over an interval or box.

Typical goals:

```lean
∀ x ∈ I, f x ≤ c
∀ x ∈ I, c ≤ f x
∀ x ∈ I, f x ≤ g x
```

Main tactics and commands:

```lean
leancert
certify_bound
certify_kernel
certify_kernel_fallback
multivariate_bound
```

`certify_kernel` is strict and only succeeds when the kernel-verified dyadic
path can close the goal. Use `certify_kernel_fallback` when an explicit
compiler/runtime fallback is acceptable.

For ergonomic raw Lean goals, start with `leancert`. Use `certify_bound` when
you intentionally want the dedicated single-variable interval engine, including
explicit Taylor-depth selection.
The stricter kernel path is best for reflected `Expr.eval` goals or for goals
whose raw expression bridge is known to be supported. When you want to try that
kernel path first but still allow the normal raw-expression automation, use
`certify_kernel_fallback` explicitly.

Minimal example:

```lean
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  leancert
```

Discovery commands can help find a candidate bound before formalizing it.  See
[Optimization and Discovery](optimization-discovery.md).

For the full tactic reference, see [Reference → Tactics](../reference/tactics.md).

For troubleshooting failed interval proofs, see [Troubleshooting](troubleshooting.md).
