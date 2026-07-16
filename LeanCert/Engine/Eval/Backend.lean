/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Extended
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine

/-!
# Unified interval-evaluation backends

This module is the single policy boundary between callers and concrete interval
implementations. Public callers select a backend here instead of calling a
permissive evaluator directly.

`auto` means "the fastest certified backend supported by this operation".
For plain interval evaluation that is currently Dyadic. Explicit backend
requests never silently switch implementation, and domain errors never trigger
fallback.
-/

namespace LeanCert.Engine

open LeanCert.Core
open LeanCert.Engine.Affine

/-- User-facing backend selection. -/
inductive BackendChoice where
  | auto
  | rational
  | dyadic
  | affine
  deriving Repr, DecidableEq, Inhabited

/-- A concrete backend, recorded in successful results. -/
inductive ConcreteBackend where
  | rational
  | dyadic
  | affine
  deriving Repr, DecidableEq

/-- Operations do not all have equivalent certified implementations yet. -/
inductive BackendOperation where
  | intervalEvaluation
  | globalOptimization
  | integration
  | rootFinding
  deriving Repr, DecidableEq

/-- Common options used by the backend dispatcher. -/
structure BackendOptions where
  backend : BackendChoice := .auto
  taylorDepth : Nat := 10
  dyadicPrecision : Int := -53
  maxNoiseSymbols : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Backend-independent successful interval result. -/
structure IntervalOutcome where
  interval : IntervalRat
  backend : ConcreteBackend
  dyadic : Option IntervalDyadic := none
  affine : Option AffineForm := none
  deriving Repr

/-- Whether a concrete backend has a certified implementation for an operation. -/
def backendSupports : ConcreteBackend → BackendOperation → Bool
  | .rational, _ => true
  | .dyadic, .intervalEvaluation | .dyadic, .globalOptimization => true
  | .dyadic, .integration | .dyadic, .rootFinding => false
  | .affine, .intervalEvaluation | .affine, .globalOptimization => true
  | .affine, .integration | .affine, .rootFinding => false

/-- Resolve `auto` once, at the operation boundary. -/
def resolveBackend (choice : BackendChoice) (operation : BackendOperation) :
    EvalResult ConcreteBackend :=
  let selected := match choice, operation with
    | .auto, .intervalEvaluation | .auto, .globalOptimization => ConcreteBackend.dyadic
    | .auto, .integration | .auto, .rootFinding => ConcreteBackend.rational
    | .rational, _ => ConcreteBackend.rational
    | .dyadic, _ => ConcreteBackend.dyadic
    | .affine, _ => ConcreteBackend.affine
  if backendSupports selected operation then
    .ok selected
  else
    .error (.unsupportedBackend s!"{repr selected} does not support certified {repr operation}")

/-- Convert a box-shaped list to the conventional interval environment. -/
def intervalEnvOfList (box : List IntervalRat) : IntervalEnv :=
  fun i => box.getD i (IntervalRat.singleton 0)

/-- The one certified entry point for evaluating an expression on a box.

All branches call checked evaluators. In particular, this function cannot
expose legacy finite sentinels for reciprocal, logarithm, or `atanh` failures.
-/
def evalIntervalWith (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) : EvalResult IntervalOutcome :=
  match resolveBackend options.backend .intervalEvaluation with
  | .error err => .error err
  | .ok backend => match backend with
    | .rational =>
        if options.taylorDepth != 10 then
          .error (.invalidConfiguration
            "the checked Rational evaluator has fixed Taylor depth 10")
        else
          (fun result => { interval := result, backend }) <$>
            evalIntervalChecked e (intervalEnvOfList box)
    | .dyadic =>
        if options.dyadicPrecision > 0 then
          .error (.invalidConfiguration
            "dyadicPrecision must be nonpositive for certified outward rounding")
        else
          let cfg : DyadicConfig := {
            precision := options.dyadicPrecision
            taylorDepth := options.taylorDepth
          }
          (fun result => { interval := result.toIntervalRat, backend, dyadic := some result }) <$>
            evalIntervalDyadicChecked e
              (toDyadicEnv (intervalEnvOfList box) options.dyadicPrecision) cfg
    | .affine =>
        let cfg : AffineConfig := {
          taylorDepth := options.taylorDepth
          maxNoiseSymbols := options.maxNoiseSymbols
        }
        (fun result => { interval := result.toInterval, backend, affine := some result }) <$>
          evalIntervalAffineChecked e (toAffineEnv box) cfg

/-- `auto` is definitionally the checked Dyadic path for interval evaluation. -/
theorem evalIntervalWith_auto_eq_dyadic (options : BackendOptions)
    (e : Expr) (box : List IntervalRat) :
    evalIntervalWith { options with backend := .auto } e box =
      evalIntervalWith { options with backend := .dyadic } e box := by
  rfl

/-- The Rational dispatcher branch preserves the checked evaluator theorem. -/
theorem evalIntervalWith_rational_correct (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : evalIntervalWith { options with backend := .rational } e box = .ok outcome)
    (ρ : Nat → ℝ) (hρ : envMem ρ (intervalEnvOfList box)) :
    Expr.eval ρ e ∈ outcome.interval := by
  have hdepth : options.taylorDepth = 10 := by
    by_contra h
    simp [evalIntervalWith, resolveBackend, backendSupports, h] at hsuccess
  cases heval : evalIntervalChecked e (intervalEnvOfList box) with
  | error err =>
      have : Except.error err = Except.ok outcome := by
        simpa [evalIntervalWith, resolveBackend, backendSupports, hdepth, heval] using hsuccess
      contradiction
  | ok I =>
      have hsound := evalIntervalChecked_correct e (intervalEnvOfList box) I heval ρ hρ
      have hout : outcome = { interval := I, backend := .rational } := by
        have h : (Except.ok { interval := I, backend := ConcreteBackend.rational } :
            EvalResult IntervalOutcome) = Except.ok outcome := by
          simpa [evalIntervalWith, resolveBackend, backendSupports, hdepth, heval] using hsuccess
        injection h with h'
        exact h'.symm
      subst outcome
      exact hsound

/-- The Dyadic dispatcher branch preserves the checked evaluator theorem. -/
theorem evalIntervalWith_dyadic_correct (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : evalIntervalWith { options with backend := .dyadic } e box = .ok outcome)
    (ρ : Nat → ℝ) (hρ : envMem ρ (intervalEnvOfList box)) :
    Expr.eval ρ e ∈ outcome.interval := by
  have hprec : options.dyadicPrecision ≤ 0 := by
    by_contra h
    have hpos : options.dyadicPrecision > 0 := lt_of_not_ge h
    have : Except.error (EvalError.invalidConfiguration
        "dyadicPrecision must be nonpositive for certified outward rounding") =
        Except.ok outcome := by
      simpa [evalIntervalWith, resolveBackend, backendSupports, hpos] using hsuccess
    contradiction
  let cfg : DyadicConfig := {
    precision := options.dyadicPrecision
    taylorDepth := options.taylorDepth
  }
  let ρd := toDyadicEnv (intervalEnvOfList box) options.dyadicPrecision
  have hρd : envMemDyadic ρ ρd := by
    intro i
    exact IntervalDyadic.mem_ofIntervalRat (hρ i) options.dyadicPrecision hprec
  cases heval : evalIntervalDyadicChecked e ρd cfg with
  | error err =>
      have : Except.error err = Except.ok outcome := by
        simpa [evalIntervalWith, resolveBackend, backendSupports, cfg, ρd,
          show ¬options.dyadicPrecision > 0 from not_lt.mpr hprec, heval] using hsuccess
      contradiction
  | ok I =>
      have hsound := evalIntervalDyadicChecked_correct e ρ ρd hρd cfg hprec I heval
      have hrat := IntervalDyadic.mem_toIntervalRat.mp hsound
      have hout : outcome = {
          interval := I.toIntervalRat, backend := .dyadic, dyadic := some I } := by
        have h : (Except.ok {
            interval := I.toIntervalRat, backend := ConcreteBackend.dyadic, dyadic := some I } :
            EvalResult IntervalOutcome) = Except.ok outcome := by
          simpa [evalIntervalWith, resolveBackend, backendSupports, cfg, ρd,
            show ¬options.dyadicPrecision > 0 from not_lt.mpr hprec, heval] using hsuccess
        injection h with h'
        exact h'.symm
      subst outcome
      exact hrat

/-- The Affine dispatcher branch preserves the checked evaluator theorem.
The noise assignment hypotheses are the standard semantic interpretation of
the affine box environment. -/
theorem evalIntervalWith_affine_correct_of_noise (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : evalIntervalWith { options with backend := .affine } e box = .ok outcome)
    (ρ : Nat → ℝ) (eps : AffineForm.NoiseAssignment)
    (hvalid : AffineForm.validNoise eps)
    (hρ : envMemAffine ρ (toAffineEnv box) eps) :
    Expr.eval ρ e ∈ outcome.interval := by
  let cfg : AffineConfig := {
    taylorDepth := options.taylorDepth
    maxNoiseSymbols := options.maxNoiseSymbols
  }
  cases heval : evalIntervalAffineChecked e (toAffineEnv box) cfg with
  | error err =>
      have : Except.error err = Except.ok outcome := by
        simpa [evalIntervalWith, resolveBackend, backendSupports, cfg, heval] using hsuccess
      contradiction
  | ok a =>
      have hsound := evalIntervalAffineChecked_correct e ρ (toAffineEnv box) eps
        hvalid hρ cfg a heval
      have hinterval := AffineForm.mem_toInterval_weak hvalid hsound
      have hout : outcome = {
          interval := a.toInterval, backend := .affine, affine := some a } := by
        have h : (Except.ok {
            interval := a.toInterval, backend := ConcreteBackend.affine, affine := some a } :
            EvalResult IntervalOutcome) = Except.ok outcome := by
          simpa [evalIntervalWith, resolveBackend, backendSupports, cfg, heval] using hsuccess
        injection h with h'
        exact h'.symm
      subst outcome
      exact hinterval

end LeanCert.Engine
