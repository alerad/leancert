/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Types
import LeanCert.Tactic.IntervalAuto.Norm
import LeanCert.Tactic.IntervalAuto.Extract
import LeanCert.Tactic.IntervalAuto.Parse
import LeanCert.Tactic.IntervalAuto.Diagnostic
import LeanCert.Tactic.IntervalAuto.ProveCommon

/-!
# Interval Arithmetic Tactics - Module Index

This module re-exports all components of the interval arithmetic tactics.

## Submodules

- `Types`: Core data structures (IntervalInfo, BoundGoal, etc.)
- `Norm`: Goal normalization and bridge theorems
- `Extract`: Rational extraction from Lean expressions
- `Parse`: Goal parsing for various bound goal forms
- `Diagnostic`: Error reporting and diagnostics
- `ProveCommon`: Shared proving utilities

## Main Tactics

- `interval_bound` - Prove bounds on universally quantified expressions
- `interval_decide` - Prove point inequalities
- `interval_auto` - Unified entry point (recommended)
- `multivariate_bound` - Prove bounds on multivariate expressions
- `opt_bound` - Prove bounds using global optimization
- `root_bound` - Prove non-existence of roots
- `interval_bound_subdiv` - Prove bounds with subdivision
- `interval_bound_adaptive` - Prove bounds with adaptive branch-and-bound
-/
