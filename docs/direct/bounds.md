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
certify_bound
certify_kernel
certify_kernel_fallback
multivariate_bound
```

`certify_kernel` is strict and only succeeds when the kernel-verified dyadic
path can close the goal. Use `certify_kernel_fallback` when an explicit
compiler/runtime fallback is acceptable.

Minimal example:

```lean
import LeanCert.Tactic.IntervalAuto

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound
```

Discovery commands can help find a candidate bound before formalizing it.  See
[Optimization and Discovery](optimization-discovery.md).

For the full tactic reference, see [Reference → Tactics](../reference/tactics.md).

For troubleshooting failed interval proofs, see [Troubleshooting](troubleshooting.md).
