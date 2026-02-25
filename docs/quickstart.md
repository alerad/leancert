# Quickstart

This quickstart is Lean-only and gets you to your first certified bound.

## 1. Add LeanCert

In your `lakefile.toml`:

```toml
[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "main"
```

Then run:

```bash
lake update
```

## 2. Prove a Bound

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, Real.exp x <= 3 := by
  certify_bound
```

## 3. Find a Root Existence Proof

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := { lo := 1, hi := 2, le := by norm_num }

example : exists x in I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

## 4. Use Discovery Commands

```lean
import LeanCert.Discovery.Commands

#find_min (fun x => x^2 + Real.sin x) on [-2, 2]
#bounds (fun x => x^3 - x) on [-2, 2]
```

## Notes

- Use `certify_bound` for direct inequality proofs.
- Use discovery commands to estimate constants before writing the final theorem.
- Use `lake exe check-compat` to validate Mathlib compatibility in larger projects.
