/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.IntervalAuto.Bound
import LeanCert.Validity.Bernstein

/-!
# Bernstein polynomial bounds

`bernstein_bound` proves `∀ x ∈ I, f x ⋈ c` for a univariate rational
polynomial `f` by the recursive Bernstein certificate
`LeanCert.Validity.Bernstein.checkPoly*Bound`. Untrusted search finds the
least bisection depth at which the certificate succeeds; the retained proof
closes that single Boolean certificate through the configured verification
route and lifts it with the matching golden theorem.

The strategy is typed and transactional: every non-success restores the
complete caller state, and a goal that is not a polynomial reports
`notPolynomial` so the semantic router can skip it without spending budget.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Auto

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-- Runtime facts retained by a successful Bernstein certificate. -/
structure BernsteinBoundOutcome where
  checker : Name
  verifier : Name
  verification : LeanCert.Tactic.VerificationUsage
  configuredDepth : Nat
  depthUsed : Nat
  boxesExamined : Nat
  /-- Bernstein enclosure of the polynomial on the whole interval. -/
  enclosure : IntervalRat
  deriving Inhabited

/-- Expected non-successes of the Bernstein strategy. -/
inductive BernsteinBoundFailure where
  | unsupported (expression detail : String)
  | notPolynomial (expression : String)
  | exhausted (configuredDepth : Nat) (enclosure : IntervalRat)
  | rejected (checker : Name) (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

def BernsteinBoundFailure.message (tacticName : String) :
    BernsteinBoundFailure → MessageData
  | .unsupported expression detail =>
      m!"{tacticName}: unsupported expression {expression}:\n{detail}"
  | .notPolynomial expression =>
      m!"{tacticName}: the function is not recognized as a univariate rational \
        polynomial:\n{expression}"
  | .exhausted depth enclosure =>
      m!"{tacticName}: no Bernstein certificate up to bisection depth {depth}; \
        the coefficient enclosure on the whole interval is \
        [{enclosure.lo}, {enclosure.hi}]"
  | .rejected checker detail =>
      m!"{tacticName}: certificate {checker} was rejected:\n{detail}"
  | .transportFailure detail =>
      m!"{tacticName}: proof transport failed:\n{detail}"
  | .internalFailure detail =>
      m!"{tacticName}: internal certificate failure:\n{detail}"

private def bernsteinCmp (isStrict isLower : Bool) : QPoly.Cmp :=
  match isStrict, isLower with
  | false, true => .lower
  | false, false => .upper
  | true, true => .strictLower
  | true, false => .strictUpper

private def bernsteinCmpExpr : QPoly.Cmp → Lean.Expr
  | .lower => mkConst ``QPoly.Cmp.lower
  | .upper => mkConst ``QPoly.Cmp.upper
  | .strictLower => mkConst ``QPoly.Cmp.strictLower
  | .strictUpper => mkConst ``QPoly.Cmp.strictUpper

private def bernsteinCheckerName : QPoly.Cmp → Name
  | .lower => ``Bernstein.checkPolyLowerBound
  | .upper => ``Bernstein.checkPolyUpperBound
  | .strictLower => ``Bernstein.checkPolyStrictLowerBound
  | .strictUpper => ``Bernstein.checkPolyStrictUpperBound

private def bernsteinVerifierName (fromIcc : Bool) : QPoly.Cmp → Name
  | .lower => if fromIcc then ``Bernstein.verify_poly_lower_bound_Icc
      else ``Bernstein.verify_poly_lower_bound
  | .upper => if fromIcc then ``Bernstein.verify_poly_upper_bound_Icc
      else ``Bernstein.verify_poly_upper_bound
  | .strictLower => if fromIcc then ``Bernstein.verify_poly_strict_lower_bound_Icc
      else ``Bernstein.verify_poly_strict_lower_bound
  | .strictUpper => if fromIcc then ``Bernstein.verify_poly_strict_upper_bound_Icc
      else ``Bernstein.verify_poly_strict_upper_bound

/-- Untrusted: recognise the reified AST as a `QPoly`. -/
unsafe def evalQPoly? (ast : Lean.Expr) : MetaM (Option QPoly) := do
  let optTy := mkApp (mkConst ``Option [.zero]) (mkConst ``LeanCert.Engine.QPoly)
  evalExpr (Option QPoly) optTy (← mkAppM ``QPoly.ofExpr #[ast])

/-- Untrusted: is the reified AST a univariate rational polynomial? Used by
the router to decide applicability before spending budget. -/
unsafe def isPolynomialAst (ast : Lean.Expr) : MetaM Bool := do
  try
    evalExpr Bool (mkConst ``Bool) (← mkAppM ``Bernstein.isPolynomial #[ast])
  catch _ => return false

private unsafe def bernsteinBoundAttempt (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (maxDepth : Nat) (isStrict isLower : Bool) :
    TacticM (Except BernsteinBoundFailure BernsteinBoundOutcome) := do
  let saved ← saveState
  goal.withContext do
    let preparation ←
      try
        discard <| tryNormalizeGoalToIcc
        let normalizedGoal ← getMainGoal
        let reified ← getAstWithReport func
        let boundRat ← extractRatBound bound
        pure <| some (normalizedGoal, reified, boundRat)
      catch e =>
        saved.restore
        return .error <| .unsupported (toString func) (← e.toMessageData.toString)
    let some (normalizedGoal, reified, boundRat) := preparation
      | saved.restore
        return .error <| .unsupported (toString func)
          "Bernstein preparation produced no expression"
    let ast := reified.expr
    let some boundValue ← getLiteral? boundRat
      | saved.restore
        return .error <| .unsupported (toString bound) "the requested bound is not rational"
    let some (lo, hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) ←
        getSubdivBounds intervalInfo
      | saved.restore
        return .error <| .unsupported (toString intervalInfo.intervalRat)
          "only literal Set.Icc or IntervalRat intervals are supported"
    let some poly ← evalQPoly? ast
      | saved.restore
        return .error <| .notPolynomial (toString func)
    if hle : lo ≤ hi then
    let interval : IntervalRat := ⟨lo, hi, hle⟩
    let cmp := bernsteinCmp isStrict isLower
    let enclosure := QPoly.bernsteinEnclosure poly interval
    let some depth := QPoly.bernsteinDepth? cmp poly boundValue interval maxDepth
      | saved.restore
        return .error <| .exhausted maxDepth enclosure
    let boxes := QPoly.bernsteinBoxes cmp poly boundValue interval depth
    let checker := bernsteinCheckerName cmp
    let verifier := bernsteinVerifierName fromSetIcc cmp
    let depthExpr := toExpr depth
    let intervalExpr ←
      if fromSetIcc then mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
      else pure intervalInfo.intervalRat
    let checkExpr ← mkAppM checker #[ast, intervalExpr, boundRat, depthExpr]
    let theoremArgs :=
      if fromSetIcc then #[ast, loRatExpr, hiRatExpr, leProof, boundRat, depthExpr]
      else #[ast, intervalInfo.intervalRat, boundRat, depthExpr]
    let theoremProof ←
      try mkAppM verifier theoremArgs
      catch e =>
        saved.restore
        return .error <| .transportFailure (← e.toMessageData.toString)
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    let verificationResult ← certGoalId.withContext do
      setGoals [certGoalId]
      closeCertificateGoalTyped (← VerificationConfig.current) certGoalId
        (tacticName := "bernstein_bound")
    let event ←
      match verificationResult with
      | .accepted event => pure event
      | .rejected =>
          saved.restore
          return .error <| .rejected checker
            "the Bernstein checker evaluated to false"
      | .failed failure =>
          saved.restore
          return .error <| .internalFailure (failure.message "bernstein_bound")
    let conclusionProof ←
      try mkAppM' theoremProof #[certGoal]
      catch e =>
        saved.restore
        return .error <| .transportFailure (← e.toMessageData.toString)
    unless ← closeBoundTransport normalizedGoal conclusionProof (some reified) do
      saved.restore
      return .error <| .transportFailure
        "the verified Bernstein certificate did not close every transport goal"
    return .ok {
      checker
      verifier
      verification := event.toUsage
      configuredDepth := maxDepth
      depthUsed := depth
      boxesExamined := boxes
      enclosure
    }
    else
      saved.restore
      return .error <| .unsupported (toString intervalInfo.intervalRat)
        "the interval endpoints are not ordered"

private unsafe def bernsteinBoundCoreTypedImpl (maxDepth : Nat) :
    TacticM (Except BernsteinBoundFailure BernsteinBoundOutcome) := do
  let original ← saveState
  try intervalNormCore
  catch e =>
    return .error <| .unsupported "goal normalization" (← e.toMessageData.toString)
  try
    evalTactic (← `(tactic|
      intro _x _hx
      simp only [ge_iff_le, gt_iff_lt]
      revert _x _hx))
  catch _ =>
    try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
    catch _ => pure ()
  try
    evalTactic (← `(tactic|
      simp only [pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some boundGoal ← parseBoundGoal goalType
    | original.restore
      return .error <| .unsupported (toString goalType)
        "expected a univariate interval bound"
  match boundGoal with
  | .forallLe _ intervalInfo func bound =>
      bernsteinBoundAttempt goal intervalInfo func bound maxDepth false false
  | .forallGe _ intervalInfo func bound =>
      bernsteinBoundAttempt goal intervalInfo func bound maxDepth false true
  | .forallLt _ intervalInfo func bound =>
      bernsteinBoundAttempt goal intervalInfo func bound maxDepth true false
  | .forallGt _ intervalInfo func bound =>
      bernsteinBoundAttempt goal intervalInfo func bound maxDepth true true

/-- Typed and exception-total Bernstein entry point. Every non-success restores
the complete caller tactic state. -/
unsafe def bernsteinBoundCoreTyped (maxDepth : Nat) :
    TacticM (Except BernsteinBoundFailure BernsteinBoundOutcome) := do
  let original ← saveState
  try
    match ← bernsteinBoundCoreTypedImpl maxDepth with
    | .ok outcome => return .ok outcome
    | .error failure =>
        original.restore
        return .error failure
  catch e =>
    original.restore
    return .error <| .internalFailure (← e.toMessageData.toString)

/-- `bernstein_bound [depth]` proves a univariate polynomial interval bound by
Bernstein coefficients, bisecting at most `depth` times (default `8`). -/
elab "bernstein_bound" depth:(num)? t:(leancertTrustItem)? : tactic => do
  discard <| VerificationConfig.current
  withTrustMode (← elabTrustItem? t) do
    let maxDepth := (depth.map (·.getNat)).getD 8
    match ← unsafe bernsteinBoundCoreTyped maxDepth with
    | .ok _ => pure ()
    | .error failure => throwError (failure.message "bernstein_bound")

end LeanCert.Tactic.Auto
