# Integration

Use this path when the goal is a certified definite-integral enclosure.

Typical goals:

```lean
∫ x in a..b, f x ∈ B
lo ≤ ∫ x in a..b, f x
∫ x in a..b, f x ≤ hi
```

Main tools:

```lean
leancert
interval_integrate
integrateInterval
```

For ordinary mathematical syntax, start with `leancert`:

```lean
import LeanCert.Tactic

open MeasureTheory

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert

example : (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  leancert
```

The exact path recognizes rational polynomials, computes their antiderivative
with `QPoly`, and checks the endpoint result using exact rational arithmetic.
For supported non-polynomial inequalities, the router uses the existing
certified partition search. Exact transcendental equalities are intentionally
not inferred from an interval enclosure.

Minimal certified enclosure example:

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core
open LeanCert.Engine

def I01 : IntervalRat := { lo := 0, hi := 1, le := by norm_num }
def cfg : EvalConfig := { taylorDepth := 10 }

example : ∫ x in (I01.lo : ℝ)..(I01.hi : ℝ),
    Expr.eval (fun _ => x) (Expr.var 0) ∈
    LeanCert.Validity.Integration.integrateInterval1Core (Expr.var 0) I01 cfg := by
  interval_integrate
```

Use `interval_integrate` when the goal explicitly names LeanCert's computed
enclosure, as in the example below. For Taylor-model generated integral
certificates, see
[Proof Templates → ConstantFactory](../proof-templates/constant-factory.md) and the
Taylor integration notes there.
