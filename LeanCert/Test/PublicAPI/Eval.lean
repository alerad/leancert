/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval

/-!
# Narrow public evaluation API contract

This module intentionally imports only `LeanCert.API.Eval`.
-/

namespace LeanCert.Test.PublicAPI.Eval

open LeanCert LeanCert.Core

def unit : IntervalRat := ⟨0, 1, by norm_num⟩
def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
def identity : Expr := .var 0
def sine : Expr := .sin identity
def cancellation : Expr := .add identity (.neg identity)

def usedBackend (expected : ConcreteBackend)
    (result : EvalResult IntervalOutcome) : Bool :=
  match result with
  | .ok outcome => decide (outcome.backend = expected)
  | .error _ => false

def failed (result : EvalResult IntervalOutcome) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

#guard usedBackend .rational (evalInterval identity [unit])
#guard usedBackend .dyadic (evalInterval sine [unit])
#guard usedBackend .affine (evalInterval cancellation [unit])
#guard failed (evalInterval (.log identity) [crossesZero])

example (outcome : IntervalOutcome)
    (h : evalInterval1 identity unit = .ok outcome)
    (x : ℝ) (hx : x ∈ unit) :
    Expr.eval (pointEnv1 x) identity ∈ outcome.interval :=
  evalInterval1_correct h hx

end LeanCert.Test.PublicAPI.Eval
