/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval
import LeanCert.Validity.Integration
import LeanCert.Validity.IntegrationDyadic

/-!
# Public checked partition integration

This facade promotes the existing Rational and Dyadic checked integrators to
one typed public boundary. Automatic selection intentionally remains Rational
until comparative benchmarks justify a broader policy.
-/

namespace LeanCert

open LeanCert.Core
open LeanCert.Engine

/-- Controls relevant to checked partition integration. -/
structure IntegrationOptions where
  backend : BackendChoice := .auto
  taylorDepth : Nat := 10
  dyadicPrecision : Int := -53
  deriving Repr, DecidableEq, Inhabited

/-- Backend-independent result from checked partition integration. -/
structure IntegralOutcome where
  enclosure : IntervalRat
  partitionCount : Nat
  requested : BackendChoice
  backend : ConcreteBackend
  deriving Repr, DecidableEq

private def rationalIntegrationConfig (requested : BackendChoice)
    (options : IntegrationOptions) : EvalResult Unit :=
  if options.taylorDepth = 10 then
    if requested != .rational || options.dyadicPrecision = -53 then
      .ok ()
    else
      .error (.invalidConfiguration
        "dyadicPrecision is only meaningful for the Dyadic integration backend")
  else
    .error (.invalidConfiguration
      "Rational partition integration currently uses fixed Taylor depth 10")

private def dyadicIntegrationConfig (options : IntegrationOptions) : EvalResult DyadicConfig :=
  if options.dyadicPrecision ≤ 0 then
    .ok { precision := options.dyadicPrecision, taylorDepth := options.taylorDepth }
  else
    .error (.invalidConfiguration "Dyadic integration precision must be nonpositive")

private theorem dyadicIntegrationConfig_precision {options : IntegrationOptions}
    {cfg : DyadicConfig} (hcfg : dyadicIntegrationConfig options = .ok cfg) :
    cfg.precision ≤ 0 := by
  unfold dyadicIntegrationConfig at hcfg
  split at hcfg
  · rename_i hprec
    cases hcfg
    exact hprec
  · contradiction

private def diagnoseRationalPartitionFailure (e : Expr) : List IntervalRat → EvalError
  | [] => .unsupportedFeature "Rational partition integration rejected its certificate"
  | cell :: rest =>
      match evalIntervalChecked e (fun _ => cell) with
      | .error err => .nestedFailure "integration partition cell" err
      | .ok _ => diagnoseRationalPartitionFailure e rest

private def diagnoseDyadicPartitionFailure (e : Expr) (cfg : DyadicConfig) :
    List IntervalRat → EvalError
  | [] => .unsupportedFeature "Dyadic partition integration rejected its certificate"
  | cell :: rest =>
      let dyadicCell := IntervalDyadic.ofIntervalRat cell cfg.precision
      match evalIntervalDyadicChecked e (fun _ => dyadicCell) cfg with
      | .error err => .nestedFailure "integration partition cell" err
      | .ok _ => diagnoseDyadicPartitionFailure e cfg rest

private def integrateUniformRational (e : Expr) (interval : IntervalRat)
    (partitionCount : Nat) (hpos : 0 < partitionCount) (requested : BackendChoice)
    (options : IntegrationOptions) :
    EvalResult IntegralOutcome :=
  match rationalIntegrationConfig requested options with
  | .error err => .error err
  | .ok _ =>
      match Validity.Integration.integratePartitionChecked e interval partitionCount with
      | some enclosure => .ok {
          enclosure := enclosure
          partitionCount := partitionCount
          requested := requested
          backend := .rational
        }
      | none =>
          .error (diagnoseRationalPartitionFailure e
            (uniformPartition interval partitionCount hpos))

private def integrateUniformDyadic (e : Expr) (interval : IntervalRat)
    (partitionCount : Nat) (hpos : 0 < partitionCount) (options : IntegrationOptions) :
    EvalResult IntegralOutcome :=
  match dyadicIntegrationConfig options with
  | .error err => .error err
  | .ok cfg =>
      let checked := Validity.IntegrationDyadic.integratePartitionDyadicChecked
        e interval partitionCount hpos cfg
      if checked.2 then
        .ok {
          enclosure := checked.1
          partitionCount := partitionCount
          requested := options.backend
          backend := .dyadic
        }
      else
        .error (diagnoseDyadicPartitionFailure e cfg
          (uniformPartition interval partitionCount hpos))

private theorem integrateUniformRational_correct {e : Expr} {interval : IntervalRat}
    {partitionCount : Nat} {requested : BackendChoice} {options : IntegrationOptions}
    {outcome : IntegralOutcome} (hpos : 0 < partitionCount)
    (hsuccess : integrateUniformRational e interval partitionCount hpos requested options =
      .ok outcome)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume interval.lo interval.hi) :
    ∫ x in (interval.lo : ℝ)..(interval.hi : ℝ), Expr.eval (fun _ => x) e ∈
      outcome.enclosure := by
  unfold integrateUniformRational at hsuccess
  cases hcfg : rationalIntegrationConfig requested options with
  | error err => simp [hcfg] at hsuccess
  | ok _ =>
    simp only [hcfg] at hsuccess
    cases hbound : Validity.Integration.integratePartitionChecked e interval partitionCount with
    | none => simp [hbound] at hsuccess
    | some bound =>
      rw [hbound] at hsuccess
      simp only [Except.ok.injEq] at hsuccess
      subst outcome
      exact Validity.Integration.integratePartitionChecked_correct
        e interval partitionCount hpos bound hbound hInt

/-- Enclose a one-dimensional integral using a checked uniform partition.

An explicit backend is honored. `.auto` currently selects Rational; invalid
domains and configurations are returned as failures and never trigger retry
with another backend. -/
def integrateUniform (e : Expr) (interval : IntervalRat) (partitionCount : Nat)
    (options : IntegrationOptions := {}) : EvalResult IntegralOutcome :=
  if hpos : 0 < partitionCount then
    match options.backend with
    | .auto | .rational =>
        integrateUniformRational e interval partitionCount hpos options.backend options
    | .dyadic => integrateUniformDyadic e interval partitionCount hpos options
    | .affine => .error (.unsupportedBackend "partition integration with Affine")
  else
    .error (.invalidConfiguration "partitionCount must be positive")

/-- A successful public partition computation encloses the corresponding real
integral. This is the common Golden Theorem for both retained backends. -/
theorem integrateUniform_correct {e : Expr} {interval : IntervalRat}
    {partitionCount : Nat} {options : IntegrationOptions} {outcome : IntegralOutcome}
    (hsuccess : integrateUniform e interval partitionCount options = .ok outcome)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume interval.lo interval.hi) :
    ∫ x in (interval.lo : ℝ)..(interval.hi : ℝ), Expr.eval (fun _ => x) e ∈
      outcome.enclosure := by
  unfold integrateUniform at hsuccess
  split at hsuccess
  · rename_i hpos
    cases hchoice : options.backend with
    | auto | rational =>
        simp only [hchoice] at hsuccess
        exact integrateUniformRational_correct hpos hsuccess hInt
    | dyadic =>
        simp only [hchoice] at hsuccess
        unfold integrateUniformDyadic at hsuccess
        cases hcfg : dyadicIntegrationConfig options with
        | error err => simp [hcfg] at hsuccess
        | ok cfg =>
          simp only [hcfg] at hsuccess
          split at hsuccess
          · rename_i hvalid
            simp only [Except.ok.injEq] at hsuccess
            subst outcome
            apply Validity.IntegrationDyadic.integratePartitionDyadicChecked_correct
              e interval partitionCount hpos cfg (dyadicIntegrationConfig_precision hcfg)
            · apply Prod.ext
              · rfl
              · simpa using hvalid
            · exact hInt
          · simp at hsuccess
    | affine => simp [hchoice] at hsuccess
  · simp at hsuccess

end LeanCert
