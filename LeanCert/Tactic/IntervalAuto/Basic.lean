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
# Interval Arithmetic Tactics - Infrastructure

This module provides infrastructure for the interval arithmetic tactics:
- `Types`: Core data structures
- `Norm`: Goal normalization
- `Extract`: Rational extraction
- `Parse`: Goal parsing
- `Diagnostic`: Error reporting
- `ProveCommon`: Shared utilities

The main tactics are in `LeanCert.Tactic.IntervalAuto`.
-/
