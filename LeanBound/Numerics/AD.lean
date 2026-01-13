/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.AD.Basic
import LeanBound.Numerics.AD.Transcendental
import LeanBound.Numerics.AD.Eval
import LeanBound.Numerics.AD.Correctness
import LeanBound.Numerics.AD.PartialCorrectness
import LeanBound.Numerics.AD.Computable

/-!
# Automatic Differentiation via Intervals

This module provides forward-mode automatic differentiation using interval
arithmetic. We compute both the value and derivative of an expression,
with rigorous bounds on both.

## Module Structure

* `AD.Basic` - Core types: `DualInterval`, basic operations (`add`, `mul`, `neg`)
* `AD.Transcendental` - Transcendental functions (`sin`, `cos`, `exp`, etc.)
* `AD.Eval` - Evaluators: `evalDual`, `evalDual?`, `derivInterval`
* `AD.Correctness` - Correctness theorems for supported expressions
* `AD.PartialCorrectness` - Correctness for partial functions (inv, log, sqrt)
* `AD.Computable` - Taylor-based computable evaluators

## Main definitions

* `DualInterval` - A pair of intervals representing (value, derivative)
* `evalDual` - Evaluate expression to get value and derivative intervals
* `evalDual?` - Partial evaluator supporting inv, log, sqrt
* `evalDualCore` - Computable evaluator for native_decide

## Main theorems

* `evalDual_val_correct` - Value component is correct for supported expressions
* `evalDual_der_correct` - Derivative component is correct for supported expressions
* `evalDual?_val_correct`, `evalDual?_der_correct` - Correctness with domain checks
* `evalDualCore_val_correct`, `evalDualCore_der_correct` - Computable correctness

All theorems are FULLY PROVED with no sorry or axioms.
-/
