# Discovery Mode

Discovery mode is for exploration before final theorem statements.

## Interactive Commands

```lean
import LeanCert.Discovery.Commands

#find_min (fun x => x^2 + Real.sin x) on [-2, 2]
#find_max (fun x => Real.sin x * Real.exp (-x)) on [0, 3]
#bounds (fun x => x^3 - x) on [-2, 2]
#eval_interval (fun x => Real.exp (Real.sin x)) on [0, 1]
```

These commands print rigorous enclosures and diagnostics inside the editor.

## Turning Exploration into Proofs

```lean
import LeanCert.Tactic.Discovery

example : exists m : Rat, forall x in Set.Icc (0 : Real) 1, x^2 >= m := by
  interval_minimize

example : exists M : Rat, forall x in Set.Icc (0 : Real) 1, Real.sin x <= M := by
  interval_maximize
```

## Recommended Workflow

1. Use `#find_min` / `#bounds` to inspect behavior.
2. Pick a clean rational target bound.
3. Prove with `certify_bound` or existential tactics (`interval_minimize`, `interval_maximize`).
4. Keep the proof script minimal and reproducible.

## Split Repositories

Python SDK workflows were moved out of this repo:

- `https://github.com/alerad/leancert-python`
- `https://github.com/alerad/leancert-bridge`
