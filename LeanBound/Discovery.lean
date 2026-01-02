/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Discovery.Types
import LeanBound.Discovery.Find
import LeanBound.Discovery.Commands

/-!
# LeanBound Discovery Mode

This module provides the "Discovery Mode" API for LeanBound - the ability to
automatically find and certify mathematical facts rather than just verify them.

## Components

* `Types` - Proof-carrying result structures (`VerifiedGlobalMin`, `VerifiedRoot`, etc.)
* `Find` - Finder functions that run algorithms and produce proofs
* `Commands` - Elaboration commands (`#minimize`, `#maximize`, `#bounds`)

## Usage

### Interactive Exploration

```lean
-- Find the minimum of x² + sin(x) on [-2, 2]
#minimize (fun x => x^2 + Real.sin x) on [-2, 2]

-- Find the maximum of e^x - x² on [0, 1]
#maximize (fun x => Real.exp x - x^2) on [0, 1]

-- Find both bounds
#bounds (fun x => x * Real.cos x) on [0, 3]
```

### Programmatic API

```lean
-- Get a verified minimum with proof
def result := findGlobalMin myExpr mySupport domain config
-- result.bound : ℚ  -- the minimum bound
-- result.is_lower_bound : ∀ ρ ∈ domain, bound ≤ eval ρ expr  -- the proof

-- Verify a specific bound
match verifyUpperBound expr support interval bound config with
| some proof => -- proof.is_upper_bound : ∀ x ∈ interval, eval x expr ≤ bound
| none => -- verification failed
```

### Tactics

```lean
-- Prove existence of a minimum
example : ∃ m : ℚ, ∀ x ∈ I01, x^2 + Real.sin x ≥ m := by
  interval_minimize

-- Prove existence of a root
example : ∃ x ∈ Icc (-2 : ℝ) 2, x^3 - x = 0 := by
  interval_roots
```

## Architecture

Discovery Mode builds on LeanBound's verification infrastructure:

1. **Algorithms** (from `Numerics/`): Branch-and-bound optimization, bisection root finding
2. **Certificates** (from `Certificate.lean`): Boolean checkers that `native_decide` can evaluate
3. **Golden Theorems**: Convert boolean certificates to semantic proofs
4. **Proof-Carrying Types**: Bundle computed results with their correctness proofs

The key insight is that the same interval arithmetic that verifies bounds can
discover them - we just need to run the algorithm first, then apply the
verification theorem to the computed result.
-/
