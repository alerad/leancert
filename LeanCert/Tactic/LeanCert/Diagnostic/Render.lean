/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Diagnostic.Evidence
import LeanCert.Tactic.LeanCert.Solver.Protocol

/-!
# User-Facing Diagnostic Rendering

All public output is rendered here.  Solver internals may retain kernel
expressions in debug traces, but ordinary failures and `leancert?` reports use
mathematical language.
-/

namespace LeanCert.Tactic.Diagnostic

open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Solver

/-- A bounded decimal rendering for user-facing numerical evidence.  The
underlying checker continues to use the exact rational value. -/
def formatRatApprox (value : ℚ) (digits : Nat := 6) : String :=
  let numerator := value.num
  let denominator := value.den
  if denominator == 1 then
    toString numerator
  else
    let (sign, magnitude) :=
      if numerator < 0 then ("-", -numerator) else ("", numerator)
    let integerPart := magnitude / denominator
    let scale := 10 ^ digits
    let fractionalPart := magnitude % denominator
    let scaled := fractionalPart * scale / denominator
    let rawDigits := toString scaled
    let padding := String.ofList (List.replicate (digits - rawDigits.length) '0')
    s!"{sign}{integerPart}.{padding}{rawDigits}"

def intentLabel : GoalIntent → String
  | .integralBound => "definite integral bound"
  | .uniqueRoot => "unique real root"
  | .rootExists => "real root existence"
  | .noRoot => "nonvanishing on an interval"
  | .argmin => "existence of a minimizer"
  | .argmax => "existence of a maximizer"
  | .existentialMinimum => "discovered lower bound"
  | .existentialMaximum => "discovered upper bound"
  | .finiteSum => "finite sum"
  | .multivariateBound => "multivariate bound"
  | .intervalBound => "univariate interval bound"
  | .pointInequality => "closed numerical comparison"
  | .certificateCheck => "closed certificate check"
  | .conjunction => "conjunction of numerical theorems"

def attemptOutcome : AttemptOutcome → String
  | .unsupported evidence =>
      let unfoldedText :=
        if evidence.unfolded.isEmpty then ""
        else s!"\nLeanCert successfully unfolded: {String.intercalate ", "
          (evidence.unfolded.toList.map toString)}"
      s!"Could not reify the remaining expression:\n  {evidence.expression}{unfoldedText}"
  | .rejected evidence =>
      match evidence.enclosure with
      | some interval =>
          s!"The candidate certificate was rejected.\nComputed enclosure: \
            [{interval.lo}, {interval.hi}]"
      | none =>
          s!"{evidence.detail}\nTry increasing `taylorDepth`, enabling subdivision, \
            or using the corresponding dedicated tactic for finer control."
  | .domainObstruction evidence => s!"Domain obstruction: {evidence.reason}"
  | .inconclusive evidence => evidence.detail
  | .refuted evidence =>
      let detail := evidence.detail.map (fun value => s!"\n{value}") |>.getD ""
      s!"Certified counterexample: {evidence.witness}{detail}"
  | .notApplicable => "The solver does not apply to this theorem."
  | .proved _ => "The solver proved the theorem."
  | .internalError solver _ =>
      s!"LeanCert encountered an internal proof-construction error in `{solver}`. \
        Enable `set_option trace.LeanCert.solver true` when reporting this bug."

def successReport (report : SolverReport) : String :=
  let backend := report.backend.map (fun value => s!"\nBackend: {value}") |>.getD ""
  let checker := report.checker.map (fun value => s!"\nChecker: {value}") |>.getD ""
  let verifier := report.verifier.map (fun value => s!"\nVerifier: {value}") |>.getD ""
  s!"LeanCert can prove this.\n\nIntent: {intentLabel report.intent}\n\
    Method: {report.method}{backend}{checker}{verifier}\n\
    Suggested proof:\n  by leancert"

end LeanCert.Tactic.Diagnostic
