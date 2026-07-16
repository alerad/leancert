/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Extended
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.Affine.Environment

/-!
# Unified interval-evaluation backends

This module is the engine policy boundary between the public `LeanCert.evalInterval`
façade and concrete interval implementations. Backend-aware engine clients may
call the dispatcher directly; ordinary application code should use the façade.

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
  deriving Repr, DecidableEq

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

end LeanCert.Engine

namespace LeanCert.Internal.Eval

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Affine

/-- Checked engine dispatcher for evaluating an expression on a box.

All branches call checked evaluators. In particular, this function cannot
expose legacy finite sentinels for reciprocal, logarithm, or `atanh` failures.
-/
def dispatch (options : BackendOptions) (e : Expr)
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
          (fun result => { interval := result.toIntervalRat, backend }) <$>
            evalIntervalDyadicChecked e
              (toDyadicEnv (intervalEnvOfList box) options.dyadicPrecision) cfg
    | .affine =>
        let cfg : AffineConfig := {
          taylorDepth := options.taylorDepth
          maxNoiseSymbols := options.maxNoiseSymbols
        }
        (fun result => { interval := result.toInterval, backend }) <$>
          evalIntervalAffineChecked e (toAffineEnv box) cfg

/-- `auto` is definitionally the checked Dyadic path for interval evaluation. -/
theorem dispatch_auto_eq_dyadic (options : BackendOptions)
    (e : Expr) (box : List IntervalRat) :
    dispatch { options with backend := .auto } e box =
      dispatch { options with backend := .dyadic } e box := by
  rfl

/-- The Rational dispatcher branch preserves the checked evaluator theorem. -/
theorem dispatch_rational_correct (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : dispatch { options with backend := .rational } e box = .ok outcome)
    (ρ : Nat → ℝ) (hρ : envMem ρ (intervalEnvOfList box)) :
    Expr.eval ρ e ∈ outcome.interval := by
  have hdepth : options.taylorDepth = 10 := by
    by_contra h
    simp [dispatch, resolveBackend, backendSupports, h] at hsuccess
  cases heval : evalIntervalChecked e (intervalEnvOfList box) with
  | error err =>
      have : Except.error err = Except.ok outcome := by
        simpa [dispatch, resolveBackend, backendSupports, hdepth, heval] using hsuccess
      contradiction
  | ok I =>
      have hsound := evalIntervalChecked_correct e (intervalEnvOfList box) I heval ρ hρ
      have hout : outcome = { interval := I, backend := .rational } := by
        have h : (Except.ok { interval := I, backend := ConcreteBackend.rational } :
            EvalResult IntervalOutcome) = Except.ok outcome := by
          simpa [dispatch, resolveBackend, backendSupports, hdepth, heval] using hsuccess
        injection h with h'
        exact h'.symm
      subst outcome
      exact hsound

/-- The Dyadic dispatcher branch preserves the checked evaluator theorem. -/
theorem dispatch_dyadic_correct (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : dispatch { options with backend := .dyadic } e box = .ok outcome)
    (ρ : Nat → ℝ) (hρ : envMem ρ (intervalEnvOfList box)) :
    Expr.eval ρ e ∈ outcome.interval := by
  have hprec : options.dyadicPrecision ≤ 0 := by
    by_contra h
    have hpos : options.dyadicPrecision > 0 := lt_of_not_ge h
    have : Except.error (EvalError.invalidConfiguration
        "dyadicPrecision must be nonpositive for certified outward rounding") =
        Except.ok outcome := by
      simpa [dispatch, resolveBackend, backendSupports, hpos] using hsuccess
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
        simpa [dispatch, resolveBackend, backendSupports, cfg, ρd,
          show ¬options.dyadicPrecision > 0 from not_lt.mpr hprec, heval] using hsuccess
      contradiction
  | ok I =>
      have hsound := evalIntervalDyadicChecked_correct e ρ ρd hρd cfg hprec I heval
      have hrat := IntervalDyadic.mem_toIntervalRat.mp hsound
      have hout : outcome = {
          interval := I.toIntervalRat, backend := .dyadic } := by
        have h : (Except.ok {
            interval := I.toIntervalRat, backend := ConcreteBackend.dyadic } :
            EvalResult IntervalOutcome) = Except.ok outcome := by
          simpa [dispatch, resolveBackend, backendSupports, cfg, ρd,
            show ¬options.dyadicPrecision > 0 from not_lt.mpr hprec, heval] using hsuccess
        injection h with h'
        exact h'.symm
      subst outcome
      exact hrat

/-- The Affine dispatcher branch preserves the checked evaluator theorem.
The noise assignment hypotheses are the standard semantic interpretation of
the affine box environment. -/
theorem dispatch_affine_correct_of_noise (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : dispatch { options with backend := .affine } e box = .ok outcome)
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
        simpa [dispatch, resolveBackend, backendSupports, cfg, heval] using hsuccess
      contradiction
  | ok a =>
      have hsound := evalIntervalAffineChecked_correct e ρ (toAffineEnv box) eps
        hvalid hρ cfg a heval
      have hinterval := AffineForm.mem_toInterval_weak hvalid hsound
      have hout : outcome = {
          interval := a.toInterval, backend := .affine } := by
        have h : (Except.ok {
            interval := a.toInterval, backend := ConcreteBackend.affine } :
            EvalResult IntervalOutcome) = Except.ok outcome := by
          simpa [dispatch, resolveBackend, backendSupports, cfg, heval] using hsuccess
        injection h with h'
        exact h'.symm
      subst outcome
      exact hinterval

/-- The Affine dispatcher has the same box-membership contract as the Rational
and Dyadic branches. The standard correlated noise assignment is constructed
inside the affine evaluation layer. -/
theorem dispatch_affine_correct (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : dispatch { options with backend := .affine } e box = .ok outcome)
    (rho : Nat → ℝ) (hrho : envMem rho (intervalEnvOfList box)) :
    Expr.eval rho e ∈ outcome.interval := by
  have hbox : ∀ i (hi : i < box.length), rho i ∈ box[i]'hi := by
    intro i hi
    simpa [intervalEnvOfList, List.getD, List.getElem?_eq_getElem hi, Option.getD]
      using hrho i
  have hzero : ∀ i, i ≥ box.length → rho i = 0 := by
    intro i hi
    have h := hrho i
    have hmem : rho i ∈ IntervalRat.singleton 0 := by
      simpa [intervalEnvOfList, List.getD, List.getElem?_eq_none hi, Option.getD] using h
    have hb := (IntervalRat.mem_def _ _).mp hmem
    norm_num [IntervalRat.singleton] at hb
    linarith
  obtain ⟨eps, hvalid, henv⟩ := exists_noise_toAffineEnv box rho hbox hzero
  exact dispatch_affine_correct_of_noise options e box outcome hsuccess
    rho eps hvalid henv

/-- A successful dispatch through any backend encloses the expression value. -/
theorem dispatch_correct (options : BackendOptions) (e : Expr)
    (box : List IntervalRat) (outcome : IntervalOutcome)
    (hsuccess : dispatch options e box = .ok outcome)
    (rho : Nat → ℝ) (hrho : envMem rho (intervalEnvOfList box)) :
    Expr.eval rho e ∈ outcome.interval := by
  rcases options with ⟨backend, taylorDepth, dyadicPrecision, maxNoiseSymbols⟩
  cases backend with
  | auto =>
      exact dispatch_dyadic_correct
        { backend := .auto, taylorDepth, dyadicPrecision, maxNoiseSymbols }
        e box outcome hsuccess rho hrho
  | rational =>
      exact dispatch_rational_correct
        { backend := .rational, taylorDepth, dyadicPrecision, maxNoiseSymbols }
        e box outcome hsuccess rho hrho
  | dyadic =>
      exact dispatch_dyadic_correct
        { backend := .dyadic, taylorDepth, dyadicPrecision, maxNoiseSymbols }
        e box outcome hsuccess rho hrho
  | affine =>
      exact dispatch_affine_correct
        { backend := .affine, taylorDepth, dyadicPrecision, maxNoiseSymbols }
        e box outcome hsuccess rho hrho

end LeanCert.Internal.Eval
