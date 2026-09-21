# Bounds And Inequalities

For ordinary numerical inequalities, start with [`leancert`](leancert.md).
Use this page when you need the dedicated controls for an interval or box.

Typical goals:

```text
∀ x ∈ I, f x ≤ c
∀ x ∈ I, c ≤ f x
∀ x ∈ I, f x ≤ g x
```
Primary workflow:

```text
leancert
leancert?
```

Advanced controls:

```text
certify_bound
interval_bound_subdiv
multivariate_bound
```
These tactics use the configured certificate-verification route independently
of their numerical backend. See the [Trust model](../architecture/trust-model.md)
and [Backend selection](../architecture/backend-selection.md) for those two
axes.

For ergonomic raw Lean goals, start with `leancert`. Use `certify_bound` when
you intentionally want the dedicated single-variable interval engine, including
explicit Taylor-depth selection.
`certify_bound` is a numerical portfolio rather than a promise of one fixed
backend. Subdivision and global optimization are strategies, not backends.
Without a positional Taylor depth it uses the same coordinated three-stage
schedule as `leancert`: Dyadic precision increases from `-53` through `-85` to
`-117`, while Taylor depth increases by 10 at each stage. A positional depth,
for example `certify_bound 20`, keeps Taylor depth fixed and still adapts
Dyadic precision. The final Rational fallback runs only after the Dyadic
stages are exhausted.

Univariate rational polynomials take a separate route. `leancert` first tries
a Bernstein certificate: it composes the polynomial with the affine map of
`[0,1]` onto the interval, converts to Bernstein coefficients exactly over `ℚ`,
and closes one Boolean certificate when every coefficient satisfies the bound,
bisecting at most `subdivisions` times otherwise. Bernstein enclosures are
exact at the endpoints and immune to the dependency problem of Horner
interval evaluation, so bounds that are tight near an endpoint need no
subdivision. The strategy is skipped silently for non-polynomial goals. The
dedicated form is `bernstein_bound [depth]`:

```lean
import LeanCert.Tactic

-- Tight at the dyadic point `x = 1/2`: one bisection, no interval slack.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (1 / 4 : ℚ) := by
  bernstein_bound

example : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, x ^ 3 - x ≥ -1 := by
  leancert
```

A polynomial with a double root inside the interval (for example
`(x - 1/3) ^ 2 ≥ 0`) has no Bernstein certificate at any bisection depth; the
typed diagnostic reports the coefficient enclosure on the whole interval.

`interval_bound_subdiv depth maxDepth` splits candidate boxes and certifies
every retained leaf. `leancert?` reports its configured and deepest depths,
boxes examined, certified leaves, whether the addressed frontier passed its
structural check, and verification usage. The frontier check establishes a
complete canonical binary frontier; the subdivision recursion maintains the
association between each address and its proof leaf. See the
[verification-status table](../architecture/verification-status.md) for the
precise checker boundary and failure semantics.

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
