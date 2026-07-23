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
import LeanCert.Tactic

example : forall x in Set.Icc (0 : Real) 1, Real.exp x <= 3 := by
  leancert
```

## 3. Direct Automation: Find a Root Existence Proof

```lean
import LeanCert.Tactic

example : exists x in Set.Icc (1 : Real) 2, x^2 = 2 := by
  leancert
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

- Start direct inequality proofs with `leancert`; use `certify_bound` when you
  intentionally want the dedicated interval-bound engine or explicit Taylor-depth control.
- Use discovery commands to estimate constants before writing the final theorem.
- Use proof templates when the proof has reusable structure: generated rows,
  main/error envelopes, perturbation observers, product-integral identities, or
  contour-shift bookkeeping.
- Use `lake exe check-compat` to validate Mathlib compatibility in larger projects.
