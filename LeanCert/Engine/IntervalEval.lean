/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Support
import LeanCert.Engine.Eval.Core
import LeanCert.Engine.Eval.Extended
import LeanCert.Tactic.Bound.Lemmas

/-!
# Interval Evaluation of Expressions

This file re-exports the interval evaluation infrastructure for `LeanCert.Core.Expr`.

## Module structure

The implementation is split across several files:

* `LeanCert.Core.Support` - Expression support predicates for total core
  evaluation and automatic differentiation

* `LeanCert.Engine.Eval.Core` - Computable interval evaluator (`LeanCert.Internal.Rational.evalTotalCore`)
  and transcendental interval bounds

* `LeanCert.Engine.Eval.Extended` - Internal noncomputable evaluator and the
  partial evaluator with inv/log support (`evalInterval?`)

* `LeanCert.Tactic.Bound.Lemmas` - Tactic-facing lemmas for proving bounds

## Main definitions (re-exported)

### Expression support predicates
* `ExprSupportedCore` - Computable subset (const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh, pi)
* `ADSupported` - Noncomputable AD subset (const, var, add, mul, neg, sin, cos, exp)

### Evaluators
* `LeanCert.Internal.Rational.evalTotalCore` - Computable interval evaluator (uses Taylor series)
* `LeanCert.Internal.Rational.evalUnchecked` - Internal noncomputable evaluator
* `evalInterval?` - Partial evaluator with inv/log support

### Correctness theorems
* `evalIntervalCore_correct` - Core evaluator correctness
* `evalInterval_correct` - Extended evaluator correctness
* `evalInterval?_correct` - Partial evaluator correctness

### Tactic lemmas
* `exprCore_le_of_interval_hi` / `exprCore_ge_of_interval_lo` - Core bounds
* `expr_le_of_interval_hi` / `expr_ge_of_interval_lo` - Extended bounds

## Design notes

The evaluators are split by computability:
- `LeanCert.Internal.Rational.evalTotalCore` is COMPUTABLE, enabling `native_decide` in tactics
- `evalInterval` is NONCOMPUTABLE, using Real.exp with floor/ceil bounds
- Both are fully verified (no sorry, no axioms)
-/

namespace LeanCert.Engine

-- Re-export all definitions from component modules
-- All imports are transitive, so users can continue to `import LeanCert.Engine.IntervalEval`
-- and have access to all definitions as before.

end LeanCert.Engine
