# Failure showcase

Good automation distinguishes false mathematics from unsupported syntax and
insufficient numerical resolution:

All five rows are executable regressions in
`LeanCert.Test.ShowcaseFailures`, built by both `Showcase` and
`FunctionalTests`.

| Situation | Diagnostic | Action |
| --- | --- | --- |
| false theorem | certified counterexample | inspect the witness and repair the statement |
| unsupported expression | specific unsupported feature | unfold/rewrite or use a checked API |
| invalid `log`/inverse domain | domain obstruction | repair the domain; precision is not the remedy |
| enclosure too wide | depth/subdivision recommendation | inspect with `leancert?`, then tune that control |
| kernel route too expensive | `auto → native` and gate reason | accept native trust or explicitly require kernel |

The counterexample path is executable:

```lean expect-error: Counter-example FOUND
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  interval_refute
```

Domain failures are distinguished from precision failures:

```lean expect-error: Domain obstruction
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Real.log x ≤ 1 := by
  leancert?
```

Question mode exposes the successful decision:

```lean
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  leancert? (trust := auto)
```

See [Troubleshooting](direct/troubleshooting.md) for the complete
diagnostic-to-remedy map.
