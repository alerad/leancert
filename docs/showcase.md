# Curated showcase

The `LeanCert.Showcase` target contains five examples chosen to show distinct
proof shapes:

```bash
lake build Showcase
```

```lean
import LeanCert.Tactic

example : Real.log 2 < 7 / 10 := by leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x * Real.cos x ≤ 3 := by leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x + y ≤ (2 : ℚ) := by leancert

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by leancert

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by leancert
```

The q-product enclosure example now lives in the downstream
**leancert-qproduct** package.

The showcase module also compiles the corresponding advanced-control proof for
every displayed example.

| Example | Advanced control | Certificate/trust story | Median |
| --- | --- | --- | ---: |
| `log 2 < 0.7` | `interval_auto 10` | observed Dyadic checker; repository-default native verification | 6.056 s |
| nonlinear quantified bound | `certify_bound 10` | observed Rational checker and verification route | 6.198 s |
| two-variable box | `multivariate_bound` | checked branch-and-bound certificate | 6.311 s |
| unique square root | `interval_unique_root` | checked interval-Newton certificate | 7.044 s |
| polynomial integral | `integral_exact` | exact rational kernel proof | 6.149 s |

These are medians of three isolated warm `lake env lean` processes on an
Apple-arm64 development machine, Lean/Mathlib v4.32.2. They include roughly
4–6 seconds of Lean process/import overhead and therefore measure the complete
copy-paste user experience, not tactic execution alone. The
[machine-readable baseline](https://github.com/alerad/leancert/blob/main/scripts/bench-showcase/baselines/v4.32.2.json)
records every sample and environment metadata. Runtime depends on hardware,
cache state, and verification mode.

Use `leancert?` to inspect the recognized shape, strategy, numerical backend or
policy, verification route, and advanced control.
