# Quickstart

This quickstart is Lean-only.  It gets you to a direct certified bound first,
then previews a proof-template workflow.

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

## 2. Direct Automation: Prove a Bound

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, Real.exp x <= 3 := by
  certify_bound
```

## 3. Direct Automation: Find a Root Existence Proof

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

Discovery commands help estimate constants before writing the final theorem.

## 5. Proof Template Preview: ConstantFactory

Proof templates are for structured certificate workflows, not just one-off
interval goals.  ConstantFactory is a perturbation-observer template: it reuses
certified kernel data for a base object and verifies finite perturbations around
it.

```lean
import LeanCert.ConstantFactory.IntervalBank

open LeanCert.ConstantFactory
open LeanCert.QProduct

example :
    observerIntegralRat ({2} : Finset Nat) ({3} : Finset Nat) = 7 / 12 := by
  native_decide

example :
    ((7 / 12 : ℚ) : ℝ) ≤ F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ∧
      F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ≤ ((7 / 12 : ℚ) : ℝ) :=
  verify_constantFactory_interval ({2} : Finset Nat) ({3} : Finset Nat)
    (7 / 12) (7 / 12) (by native_decide)
```

## Notes

- Use `certify_bound` for direct inequality proofs.
- Use discovery commands to estimate constants before writing the final theorem.
- Use proof templates when the proof has reusable structure: generated rows,
  main/error envelopes, perturbation observers, product-integral identities, or
  contour-shift bookkeeping.
- Use `lake exe check-compat` to validate Mathlib compatibility in larger projects.
