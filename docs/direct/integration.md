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
interval_integrate
integrateInterval
```

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

For Taylor-model generated integral certificates, see
[Proof Templates → ConstantFactory](../proof-templates/constant-factory.md) and the
Taylor integration notes there.
