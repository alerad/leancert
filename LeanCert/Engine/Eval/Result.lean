/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Basic

/-!
# Checked evaluation results

Certified evaluators return a finite enclosure only after all partial-domain
conditions have been checked.  Failures are data: callers must propagate them
instead of substituting a finite sentinel that could be mistaken for an
enclosure.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-- Why a checked evaluator could not produce a finite certified enclosure. -/
inductive EvalError where
  | reciprocalContainsZero (interval : IntervalRat)
  | logNonpositive (interval : IntervalRat)
  | atanhOutsideUnitBall (interval : IntervalRat)
  | unsupportedBackend (operation : String)
  | nestedFailure (operation : String) (cause : EvalError)
  deriving Repr

/-- Result type used by checked evaluators and public computation APIs. -/
abbrev EvalResult (α : Type) := Except EvalError α

end LeanCert.Engine
