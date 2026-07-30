# Curated showcase

The `LeanCert.Showcase` target contains six examples chosen to show distinct
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

The domain-specific sixth theorem is:

```lean
import LeanCert.QProduct

open LeanCert.QProduct

example : primeLambda ≤ ((133 / 240 : ℚ) : ℝ) := by
  exact verify_primeLambda_upper 7 (133 / 240) (by native_decide)
```

| Example | Selected method | Trust story |
| --- | --- | --- |
| `log 2 < 0.7` | direct point enclosure | checked Dyadic certificate |
| nonlinear quantified bound | direct enclosure | Dyadic-first/Rational-fallback checked portfolio |
| two-variable box | branch-and-bound | checked global-bound certificate |
| unique square root | interval Newton | checked root certificate |
| polynomial integral | exact rational integration | ordinary kernel proof |
| prime q-product limit | finite truncation | Golden Theorem with native-checked premise |

On the reference development machine, a warm direct compilation of the whole
module took approximately 21 seconds on Lean/Mathlib v4.32.2. Runtime depends
on hardware, cache state, and verification mode.

Use `leancert?` to inspect the recognized shape, strategy, numerical backend or
policy, verification route, and advanced control.

