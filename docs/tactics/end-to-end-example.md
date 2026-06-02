# End-to-End Example: Discovery to Formal Theorem

This guide shows a Lean-only workflow from exploration to a finished proof.

## Goal

Prove:

- for all `x in [0, 1]`, `x^2 + sin(x) <= 2`

## Step 1: Explore Bounds

```lean
import LeanCert.Discovery.Commands

#bounds (fun x => x^2 + Real.sin x) on [0, 1]
```

Suppose discovery reports an upper enclosure below `2`. That gives a safe theorem target.

## Step 2: Write the Theorem

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, x^2 + Real.sin x <= 2 := by
  certify_bound
```

## Step 3: Add Root Evidence (Optional)

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := { lo := 1, hi := 2, le := by norm_num }

example : exists x in I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

## Practical Pattern

1. Explore with discovery commands.
2. Choose theorem constants with margin.
3. Commit short proof scripts using `certify_bound` and related tactics.

## Split Repositories

Python and bridge tooling live in separate repos:

- `https://github.com/alerad/leancert-python`
- `https://github.com/alerad/leancert-bridge`
