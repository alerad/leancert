/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.RootFinding.Basic
import LeanBound.Numerics.RootFinding.Bisection
import LeanBound.Numerics.RootFinding.Newton
import LeanBound.Numerics.RootFinding.MVTBounds
import LeanBound.Numerics.RootFinding.Contraction

/-!
# Root Finding: Main Module

This module re-exports all components of the root finding library.

## Module Structure

* `Basic.lean` - Core definitions (`RootStatus`, `excludesZero`, `signChange`, `checkRootStatus`)
  and basic correctness lemmas (`excludesZero_correct`, `signChange_correct`)

* `Bisection.lean` - Bisection algorithm (`bisectRootGo`, `bisectRoot`) and
  correctness theorems (`bisectRoot_hasRoot_correct`, `bisectRoot_noRoot_correct`)

* `Newton.lean` - Interval Newton method (`newtonStepTM`, `newtonStepSimple`,
  `newtonStep`, `newtonIntervalGo`, `newtonIntervalTM`) and core preservation
  theorems (`newton_preserves_root`, `newton_step_at_most_one_root`)

* `MVTBounds.lean` - Mean Value Theorem wrappers and quotient bound lemmas
  used for proving Newton contraction correctness

* `Contraction.lean` - Main contraction theorems (`newton_contraction_has_root`,
  `newton_contraction_unique_root`, `newtonIntervalGo_preserves_root`)

## Usage

For most applications, import this module to get access to all root finding
functionality:

```lean
import LeanBound.Numerics.RootFinding.Main
```

Or import specific submodules as needed.

## Verification Status

**Fully Verified (no `sorry`):**
- All root finding theorems are now fully proved with no `sorry` statements
- Bisection: `bisectRoot_hasRoot_correct`, `bisectRoot_noRoot_correct`
- Newton: `newton_preserves_root`, `newton_step_at_most_one_root`,
  `newton_contraction_has_root`, `newton_contraction_unique_root`,
  `newtonIntervalGo_preserves_root`
- MVT wrapper lemmas and all contraction contradiction lemmas
-/

namespace LeanBound.Numerics

-- Re-export key types and definitions
open LeanBound.Core

-- Everything is already exported via the imports

end LeanBound.Numerics
