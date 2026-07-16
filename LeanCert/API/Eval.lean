/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Backend

/-!
# Public checked interval evaluation

This module is the authoritative public entry point for evaluating an
expression over a rational box. Backend selection is explicit, every backend
uses its checked evaluator, and a successful result has one backend-independent
enclosure theorem.

Backend-native result types remain available from `LeanCert.Backend.*`;
the public outcome intentionally contains only the common interval and the
backend that produced it.
-/

namespace LeanCert

open LeanCert.Core

export LeanCert.Engine (
  BackendChoice
  ConcreteBackend
  EvalError
  EvalResult
  IntervalOutcome
)

/-- Precision and representation controls shared by the certified backends. -/
structure PrecisionOptions where
  taylorDepth : Nat := 10
  dyadicExponent : Int := -53
  maxNoiseSymbols : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Options for the public interval evaluator. -/
structure EvalOptions where
  backend : BackendChoice := .auto
  precisionOptions : PrecisionOptions := {}
  deriving Repr, DecidableEq, Inhabited

/-- Translate stable public options to the current engine dispatcher options. -/
def EvalOptions.toBackendOptions (options : EvalOptions) : Engine.BackendOptions := {
  backend := options.backend
  taylorDepth := options.precisionOptions.taylorDepth
  dyadicPrecision := options.precisionOptions.dyadicExponent
  maxNoiseSymbols := options.precisionOptions.maxNoiseSymbols
}

/-- Semantic interpretation of a list-shaped interval box.

Coordinates beyond `box.length` are fixed to zero. This named predicate is the
shared input contract for all public box evaluators and their correctness
theorems. -/
def BoxEnvMem (rho : Nat → ℝ) (box : List IntervalRat) : Prop :=
  ∀ i, rho i ∈ box.getD i (IntervalRat.singleton 0)

/-- Recover membership in an in-bounds box coordinate. -/
theorem BoxEnvMem.get {rho : Nat → ℝ} {box : List IntervalRat}
    (h : BoxEnvMem rho box) (i : Nat) (hi : i < box.length) :
    rho i ∈ box[i]'hi := by
  simpa [BoxEnvMem, List.getD, List.getElem?_eq_getElem hi, Option.getD] using h i

/-- Coordinates outside a list-shaped box are zero. -/
theorem BoxEnvMem.eq_zero {rho : Nat → ℝ} {box : List IntervalRat}
    (h : BoxEnvMem rho box) (i : Nat) (hi : box.length ≤ i) : rho i = 0 := by
  have hmem : rho i ∈ IntervalRat.singleton 0 := by
    simpa [BoxEnvMem, List.getD, List.getElem?_eq_none hi, Option.getD] using h i
  have hb := (IntervalRat.mem_def _ _).mp hmem
  norm_num [IntervalRat.singleton] at hb
  linarith

/-- Evaluate an expression over a rational box using a checked certified backend.

The default `.auto` backend currently selects Dyadic evaluation. Explicit
backend requests are honored and invalid domains or configurations return a
structured `EvalError`; they never return a fallback interval. -/
def evalInterval (e : Expr) (box : List IntervalRat)
    (options : EvalOptions := {}) : EvalResult IntervalOutcome :=
  Internal.Eval.dispatch options.toBackendOptions e box

/-- A successful public interval evaluation encloses the expression value.

Coordinates beyond `box.length` are interpreted as zero, matching the
evaluator's box-to-environment conversion. -/
theorem evalInterval_correct {e : Expr} {box : List IntervalRat}
    {options : EvalOptions} {outcome : IntervalOutcome}
    (hsuccess : evalInterval e box options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    Expr.eval rho e ∈ outcome.interval := by
  apply Internal.Eval.dispatch_correct options.toBackendOptions e box outcome hsuccess rho
  intro i
  exact hrho i

/-- Environment used by the one-dimensional checked evaluator. -/
def pointEnv1 (x : ℝ) : Nat → ℝ
  | 0 => x
  | _ + 1 => 0

/-- Checked one-dimensional interval evaluation. Variables other than `var 0`
are interpreted as zero. -/
def evalInterval1 (e : Expr) (interval : IntervalRat)
    (options : EvalOptions := {}) : EvalResult IntervalOutcome :=
  evalInterval e [interval] options

/-- A successful one-dimensional evaluation encloses every value obtained by
substituting a point from the input interval for `var 0`. -/
theorem evalInterval1_correct {e : Expr} {interval : IntervalRat}
    {options : EvalOptions} {outcome : IntervalOutcome}
    (hsuccess : evalInterval1 e interval options = .ok outcome)
    {x : ℝ} (hx : x ∈ interval) :
    Expr.eval (pointEnv1 x) e ∈ outcome.interval := by
  apply evalInterval_correct hsuccess
  intro i
  cases i with
  | zero => simpa [pointEnv1]
  | succ i =>
      simp [pointEnv1, List.getD, IntervalRat.singleton, IntervalRat.mem_def]

end LeanCert
