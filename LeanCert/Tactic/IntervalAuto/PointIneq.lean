/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.IntervalAuto.Bound
import LeanCert.Validity.Bounds
import LeanCert.Validity.DyadicBounds
import LeanCert.Engine.Optimization.BoundVerify

/-!
# Point Inequality Tactic (interval_decide)

The `interval_decide` tactic proves point inequalities like `Real.exp 1 ≤ 3`.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-- Try to prove a closed expression bound directly using certificate verification. -/
def proveClosedExpressionBound (goal : MVarId) (goalType : Lean.Expr) (taylorDepth : Nat) : TacticM Unit := do
  trace[interval_decide] "proveClosedExpressionBound: Starting with goal {goalType}"
  goal.withContext do
    -- Parse the inequality
    let some (lhs, rhs, isStrict, isReversedOrig) ← parsePointIneq goalType
      | throwError "proveClosedExpressionBound: Expected a point inequality"
    trace[interval_decide] "Parsed: lhs={lhs}, rhs={rhs}, isStrict={isStrict}, isReversedOrig={isReversedOrig}"

    -- Determine which side has the function by checking if it converts to rational
    -- (same logic as intervalDecideCore for consistency)
    let lhsIsConst ← toRat? lhs
    let rhsIsConst ← toRat? rhs
    let lhsConsts ← collectConstants lhs
    let rhsConsts ← collectConstants rhs

    let (funcExpr, boundExpr, needsFlip) :=
      if lhsIsConst.isSome && rhsIsConst.isNone then
        -- LHS is a rational constant, RHS is the function
        (rhs, lhs, true)
      else if rhsIsConst.isSome && lhsIsConst.isNone then
        -- RHS is a rational constant, LHS is the function
        (lhs, rhs, false)
      else if lhsConsts.isEmpty && !rhsConsts.isEmpty then
        (lhs, rhs, false)
      else if rhsConsts.isEmpty && !lhsConsts.isEmpty then
        (rhs, lhs, true)
      else
        if isReversedOrig then (rhs, lhs, false) else (lhs, rhs, false)

    let isReversed := isReversedOrig != needsFlip
    trace[interval_decide] "funcExpr={funcExpr}, boundExpr={boundExpr}, needsFlip={needsFlip}, isReversed={isReversed}"

    -- Try to extract the bound as a rational
    let boundRat? ← extractRatFromReal boundExpr

    -- If bound is not a rational, we have two transcendental expressions
    if boundRat?.isNone then
      trace[interval_decide] "Bound is not rational, trying difference approach"
      let diffExpr ←
        if isStrict then
          if isReversed then
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]
          else
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]
        else
          if isReversed then
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]
          else
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]

      trace[interval_decide] "diffExpr = {diffExpr}"

      let diffAst ← reify diffExpr
      let supportProof ← mkSupportedCoreProof diffAst
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      let zeroRat : ℚ := 0
      let leProof ← mkAppM ``le_refl #[toExpr zeroRat]
      let intervalExpr ← mkAppM ``IntervalRat.mk #[toExpr zeroRat, toExpr zeroRat, leProof]

      let theoremName := if isStrict then ``verify_strict_lower_bound else ``verify_lower_bound
      let checkName := if isStrict then ``LeanCert.Validity.checkStrictLowerBound
                       else ``LeanCert.Validity.checkLowerBound

      let checkExpr ← mkAppM checkName #[diffAst, intervalExpr, toExpr zeroRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      certGoalId.withContext do
        try
          setGoals [certGoalId]
          evalTactic (← `(tactic| native_decide))
        catch _ =>
          throwError "proveClosedExpressionBound: Certificate check failed for difference expression"

      let proof ← mkAppM theoremName #[diffAst, supportProof, intervalExpr, toExpr zeroRat, cfgExpr, certGoal]

      let zeroRatAsReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr (0 : ℚ)]
      let h1 ← mkAppM ``le_refl #[zeroRatAsReal]
      let h2 ← mkAppM ``le_refl #[zeroRatAsReal]
      let memProof ← mkAppM ``And.intro #[h1, h2]
      let proofAtZero := Lean.mkApp2 proof zeroRatAsReal memProof

      let proofType ← inferType proofAtZero
      trace[interval_decide] "Difference proof type: {proofType}"

      setGoals [goal]
      let proofStx ← Term.exprToSyntax proofAtZero

      try
        evalTactic (← `(tactic| (
          have h0 := $proofStx;
          simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                     LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                     LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                     LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                     LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                     LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                     Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                     Rat.cast_zero, sub_zero, zero_sub, neg_neg] at h0
        )))

        let hyps ← getLCtx
        for d in hyps do
          if d.userName.toString.startsWith "h0" then
            trace[interval_decide] "After first simp, h0 type: {← inferType d.toExpr}"

        evalTactic (← `(tactic| norm_num at h0))

        let hyps2 ← getLCtx
        for d in hyps2 do
          if d.userName.toString.startsWith "h0" then
            trace[interval_decide] "After norm_num, h0 type: {← inferType d.toExpr}"

        evalTactic (← `(tactic| (
          first
          | linarith
          | (simp only [Rat.divInt_eq_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at h0; linarith)
          | (norm_cast at h0; linarith)
          | (simp only [← sub_eq_add_neg] at h0; exact sub_pos.mp h0)
          | (simp only [← sub_eq_add_neg, sub_pos] at h0; exact h0)
          | (have h1 := lt_add_of_neg_add_lt_first h0; simp at h1; exact h1)
          | (have h1 := h0; ring_nf at h1; linarith)
        )))
        let remainingGoals ← getGoals
        if !remainingGoals.isEmpty then
          throwError "proveClosedExpressionBound: Goal not closed after difference approach"
        return
      catch e =>
        trace[interval_decide] "Difference approach error: {e.toMessageData}"
        throwError "proveClosedExpressionBound: Difference approach failed: {e.toMessageData}"

    let some boundRat := boundRat?
      | throwError "proveClosedExpressionBound: Could not extract rational bound from {boundExpr}"

    trace[interval_decide] "boundRat extracted: {boundRat}"

    let ast ← reify funcExpr
    trace[interval_decide] "ast reified"

    let supportProof ← mkSupportedCoreProof ast
    trace[interval_decide] "supportProof generated"

    -- Helper: try to close the goal given a proof term for the bound
    let tryCloseWith (proofStx : TSyntax `term) : TacticM Bool := do
      -- Approach 1: Direct simp + exact
      try
        setGoals [goal]
        evalTactic (← `(tactic| have h0 := $proofStx))
        evalTactic (← `(tactic| (
          simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                     LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                     LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                     LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                     LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                     LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                     Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast] at h0
        )))
        evalTactic (← `(tactic| exact h0))
        return true
      catch _ => pure ()

      -- Approach 2: convert with norm_num
      setGoals [goal]
      try
        evalTactic (← `(tactic| (
          have h0 := $proofStx;
          simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                     LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                     LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                     LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                     LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                     LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                     Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                     Rat.divInt_eq_div] at h0;
          convert h0 using 1 <;> norm_num
        )))
        return true
      catch e2 =>
        trace[interval_decide] "Approach 2 failed: {e2.toMessageData}"

      -- Approach 3: Normalize goal bound first
      setGoals [goal]
      let boundRatStx ← Term.exprToSyntax (toExpr boundRat)
      try
        evalTactic (← `(tactic| (
          show $(← Term.exprToSyntax funcExpr) ≤ ↑($boundRatStx : ℚ)
        )))
        evalTactic (← `(tactic| (
          have h0 := $proofStx;
          simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                     LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                     LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                     LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                     LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                     LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                     Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                     Rat.divInt_eq_div] at h0;
          exact h0
        )))
        return true
      catch e3 =>
        trace[interval_decide] "Approach 3 failed: {e3.toMessageData}"

      -- Approach 4: Use refine with explicit type cast
      setGoals [goal]
      try
        evalTactic (← `(tactic| (
          refine ?_;
          have h0 := $proofStx;
          simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                     LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                     LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                     LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                     LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                     LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                     Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                     Rat.divInt_eq_div] at h0;
          exact_mod_cast h0
        )))
        return true
      catch e4 =>
        trace[interval_decide] "Approach 4 failed: {e4.toMessageData}"

      return false

    -- Try dyadic backend first for supported expressions (all inequality types)
    try
      -- Try ExprSupported first, fall back to ExprSupportedWithInv
      let mut dyadicSupportProof ← mkSupportedWithInvProof ast
      let mut useDyadicWithInv := true
      try
        dyadicSupportProof ← mkSupportedProof ast
        useDyadicWithInv := false
      catch _ => pure ()
      trace[interval_decide] "dyadic supportProof generated (withInv={useDyadicWithInv})"

      let prec : Int := -80
      let precExpr := toExpr prec
      let depthExpr := toExpr taylorDepth
      let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
      let precLeZeroProof ← mkDecideProof precLeZeroTy

      let zeroRat : ℚ := 0
      let leProof ← mkAppM ``le_refl #[toExpr zeroRat]

      let dyadicTheoremName :=
        if useDyadicWithInv then
          if isStrict then
            if isReversed then ``LeanCert.Validity.verify_strict_lower_bound_dyadic_withInv
            else ``LeanCert.Validity.verify_strict_upper_bound_dyadic_withInv
          else
            if isReversed then ``LeanCert.Validity.verify_lower_bound_dyadic_withInv
            else ``LeanCert.Validity.verify_upper_bound_dyadic_withInv
        else
          if isStrict then
            if isReversed then ``LeanCert.Validity.verify_strict_lower_bound_dyadic'
            else ``LeanCert.Validity.verify_strict_upper_bound_dyadic'
          else
            if isReversed then ``LeanCert.Validity.verify_lower_bound_dyadic'
            else ``LeanCert.Validity.verify_upper_bound_dyadic'
      let dyadicCheckName :=
        if useDyadicWithInv then
          if isStrict then
            if isReversed then ``LeanCert.Validity.checkStrictLowerBoundDyadicWithInv
            else ``LeanCert.Validity.checkStrictUpperBoundDyadicWithInv
          else
            if isReversed then ``LeanCert.Validity.checkLowerBoundDyadicWithInv
            else ``LeanCert.Validity.checkUpperBoundDyadicWithInv
        else
          if isStrict then
            if isReversed then ``LeanCert.Validity.checkStrictLowerBoundDyadic
            else ``LeanCert.Validity.checkStrictUpperBoundDyadic
          else
            if isReversed then ``LeanCert.Validity.checkLowerBoundDyadic
            else ``LeanCert.Validity.checkUpperBoundDyadic

      trace[interval_decide] "Building dyadic certificate check"
      let dyadicCheckExpr ← mkAppM dyadicCheckName
        #[ast, toExpr zeroRat, toExpr zeroRat, leProof, toExpr boundRat, precExpr, depthExpr]
      let dyadicCertTy ← mkAppM ``Eq #[dyadicCheckExpr, mkConst ``Bool.true]
      let dyadicCertGoal ← mkFreshExprMVar dyadicCertTy
      let dyadicCertGoalId := dyadicCertGoal.mvarId!
      dyadicCertGoalId.withContext do
        setGoals [dyadicCertGoalId]
        trace[interval_decide] "Running native_decide (dyadic)"
        evalTactic (← `(tactic| native_decide))
        trace[interval_decide] "Dyadic certificate verified"

      let dyadicProof ← mkAppM dyadicTheoremName
        #[ast, dyadicSupportProof, toExpr zeroRat, toExpr zeroRat, leProof, toExpr boundRat,
          precExpr, depthExpr, precLeZeroProof, dyadicCertGoal]

      let zeroRatAsReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr (0 : ℚ)]
      let h1 ← mkAppM ``le_refl #[zeroRatAsReal]
      let h2 ← mkAppM ``le_refl #[zeroRatAsReal]
      let memProof ← mkAppM ``And.intro #[h1, h2]
      let dyadicProofAtZero := Lean.mkApp2 dyadicProof zeroRatAsReal memProof

      let dyadicProofStxRaw ← Term.exprToSyntax dyadicProofAtZero
      let dyadicProofStx : TSyntax `term := ⟨dyadicProofStxRaw⟩
      let closed ← tryCloseWith dyadicProofStx
      if closed then
        return
    catch e =>
      trace[interval_decide] "Dyadic backend failed: {e.toMessageData}"

    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let zeroRat : ℚ := 0
    let leProof ← mkAppM ``le_refl #[toExpr zeroRat]
    let intervalExpr ← mkAppM ``IntervalRat.mk #[toExpr zeroRat, toExpr zeroRat, leProof]

    let theoremName :=
      if isStrict then
        if isReversed then ``verify_strict_lower_bound else ``verify_strict_upper_bound
      else
        if isReversed then ``verify_lower_bound else ``verify_upper_bound

    let checkName :=
      if isStrict then
        if isReversed then ``LeanCert.Validity.checkStrictLowerBound
        else ``LeanCert.Validity.checkStrictUpperBound
      else
        if isReversed then ``LeanCert.Validity.checkLowerBound
        else ``LeanCert.Validity.checkUpperBound

    trace[interval_decide] "Building certificate check"
    let checkExpr ← mkAppM checkName #[ast, intervalExpr, toExpr boundRat, cfgExpr]
    trace[interval_decide] "checkExpr built"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    certGoalId.withContext do
      try
        setGoals [certGoalId]
        trace[interval_decide] "Running native_decide"
        evalTactic (← `(tactic| native_decide))
        trace[interval_decide] "Certificate verified"
      catch e =>
        trace[interval_decide] "native_decide failed: {e.toMessageData}"
        throwError "proveClosedExpressionBound: Certificate check failed for closed expression"

    let proof ← mkAppM theoremName #[ast, supportProof, intervalExpr, toExpr boundRat, cfgExpr, certGoal]

    let zeroRatAsReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr (0 : ℚ)]
    let h1 ← mkAppM ``le_refl #[zeroRatAsReal]
    let h2 ← mkAppM ``le_refl #[zeroRatAsReal]
    let memProof ← mkAppM ``And.intro #[h1, h2]
    let proofAtZero := Lean.mkApp2 proof zeroRatAsReal memProof

    setGoals [goal]

    let proofStxRaw ← Term.exprToSyntax proofAtZero
    let proofStx : TSyntax `term := ⟨proofStxRaw⟩

    let proofType ← inferType proofAtZero
    trace[interval_decide] "Proof type: {proofType}"
    trace[interval_decide] "Goal type: {goalType}"

    let closed ← tryCloseWith proofStx
    if closed then
      return
    throwError "proveClosedExpressionBound: Failed to close goal after all attempts"

/-- The interval_decide tactic implementation. -/
def intervalDecideCore (taylorDepth : Nat) : TacticM Unit := do
  intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType
  trace[interval_decide] "intervalDecideCore: goal type = {goalType}"

  let some (lhs, rhs, _isStrict, isReversed) ← parsePointIneq goalType
    | let diagReport ← mkDiagnosticReport "interval_decide" goalType "parse"
        (some m!"Expected a point inequality of form:\n\
                 • expr ≤ bound  (or <, ≥, >)\n\
                 • e.g., Real.exp 1 ≤ 3\n\n\
                 For universally quantified goals, use `interval_bound` instead.")
      throwError "interval_decide: Could not parse as point inequality.\n\n{diagReport}"

  let lhsIsConst ← toRat? lhs
  let rhsIsConst ← toRat? rhs
  let lhsConsts ← collectConstants lhs
  let rhsConsts ← collectConstants rhs

  let (funcExpr, boundExpr, needsFlip) :=
    if lhsIsConst.isSome && rhsIsConst.isNone then
      (rhs, lhs, true)
    else if rhsIsConst.isSome && lhsIsConst.isNone then
      (lhs, rhs, false)
    else if lhsConsts.isEmpty && !rhsConsts.isEmpty then
      (lhs, rhs, false)
    else if rhsConsts.isEmpty && !lhsConsts.isEmpty then
      (rhs, lhs, true)
    else
      if isReversed then (rhs, lhs, false) else (lhs, rhs, false)

  let actualIsReversed := isReversed != needsFlip
  trace[interval_decide] "funcExpr = {funcExpr}, boundExpr = {boundExpr}, needsFlip = {needsFlip}, actualIsReversed = {actualIsReversed}"

  let consts ← collectConstants funcExpr
  trace[interval_decide] "consts = {consts}"

  let hasFreeVars := funcExpr.hasFVar
  trace[interval_decide] "hasFreeVars = {hasFreeVars}"

  let c : ℚ ←
    if !hasFreeVars then
      trace[interval_decide] "No free variables, trying closed expression path"
      let mut currentGoal := goal
      let mut currentGoalType := goalType
      try
        evalTactic (← `(tactic| norm_num))
        let remainingGoals ← getGoals
        if remainingGoals.isEmpty then
          return
        else
          let isAssignedAfter ← goal.isAssigned
          if isAssignedAfter && !remainingGoals.isEmpty then
            currentGoal := remainingGoals.head!
            currentGoalType ← currentGoal.getType
      catch _ => pure ()

      try
        proveClosedExpressionBound currentGoal currentGoalType taylorDepth
        return
      catch _ => pure ()

      trace[interval_decide] "Falling through to fallback"
      if consts.isEmpty then pure 0 else pure consts.head!
    else
      if consts.isEmpty then pure 0 else pure consts.head!

  let goalsBefore ← getGoals
  try
    evalTactic (← `(tactic| norm_num))
    let goalsAfter ← getGoals
    if goalsAfter.isEmpty || goalsAfter.length < goalsBefore.length then
      return
  catch _ => pure ()

  let cStx : Lean.Term ←
    if c.den == 1 then
      if c.num >= 0 then
        pure ⟨Syntax.mkNumLit (toString c.num)⟩
      else
        `(- $(Syntax.mkNumLit (toString (-c.num))))
    else
      if c.num >= 0 then
        `($(Syntax.mkNumLit (toString c.num)) / $(Syntax.mkNumLit (toString c.den)))
      else
        `(- ($(Syntax.mkNumLit (toString (-c.num))) / $(Syntax.mkNumLit (toString c.den))))

  let depthStx := Syntax.mkNumLit (toString taylorDepth)

  try
    evalTactic (← `(tactic|
      (have h : ∀ x ∈ Set.Icc ($cStx : ℝ) $cStx, _ := by interval_bound $depthStx) <;>
      exact h $cStx ⟨le_refl $cStx, le_refl $cStx⟩
    ))
    return
  catch _ => pure ()

  let cStr := if c.den == 1 then s!"{c.num}" else s!"{c.num}/{c.den}"
  let funcStr ← Meta.ppExpr funcExpr
  let boundStr ← Meta.ppExpr boundExpr
  throwError "interval_decide: Could not automatically prove this inequality.\n\n\
              Detected:\n\
              • Function: {funcStr}\n\
              • Bound: {boundStr}\n\
              • Evaluation point: {cStr}\n\n\
              Suggestions:\n\
              • Try increasing depth: `interval_decide 30`\n\
              • Check if the bound is mathematically correct\n\n\
              Manual workaround pattern:\n\
              ```lean\n\
              have h : ∀ x ∈ Set.Icc ({cStr}:ℝ) {cStr}, f x ≤ bound := by interval_bound\n\
              exact h {cStr} ⟨le_refl {cStr}, le_refl {cStr}⟩\n\
              ```\n\
              Replace `f x` with your expression (using `x` instead of `{cStr}`)."

/-! ### Depth estimation helpers -/

/-- Compute `ceil(|q|)` for a rational `q` as a `Nat`. -/
private def ratCeilAbs (q : ℚ) : Nat :=
  let a := q.num.natAbs
  let d := q.den
  (a + d - 1) / d

/-- Heuristic reduction factor for exp (mirrors `IntervalRat.expReduceK`). -/
private def expReduceKMeta (q : ℚ) : Nat :=
  Nat.log2 (ratCeilAbs q + 1)

/-- Heuristic exp depth estimate using argument reduction.
    We approximate the required depth based on |q/2^k|, where k = log2(ceil|q|+1). -/
private def expDepthEstimate (q : ℚ) : Nat :=
  let k := expReduceKMeta q
  let q' : ℚ := q / (2 ^ k : Nat)
  (q'.num.natAbs * 7 / q'.den).max 10

/-- Estimate the Taylor depth needed based on constants inside transcendental functions.
    For `exp(c)`, we account for argument reduction and use roughly `7 * |c/2^k|` terms.
    For `sin(c)`, `cos(c)`, convergence requires roughly `3 * |c|` terms.
    Returns at least 10. -/
private partial def estimateTranscendentalDepth (e : Lean.Expr) : MetaM Nat := do
  let mut maxDepth : Nat := 10
  let estimate ← go e
  return Nat.max maxDepth estimate
where
  go (e : Lean.Expr) : MetaM Nat := do
    let e ← instantiateMVars e
    let fn := e.getAppFn
    let args := e.getAppArgs
    -- Check for transcendental functions
    if fn.isConst then
      let name := fn.constName!
      let nameStr := name.toString
      -- exp, sinh, cosh need ~7x the argument magnitude (with exp reduction)
      if nameStr.endsWith "exp" || nameStr.endsWith "sinh" || nameStr.endsWith "cosh" then
        if args.size > 0 then
          let arg := args.back!
          if let some q ← extractRatFromReal arg then
            let mag := expDepthEstimate q
            let childDepth ← go arg
            return Nat.max mag childDepth
          else
            -- Recurse into the argument to find nested constants
            let childDepth ← go arg
            return childDepth
      -- sin, cos need ~3x the argument magnitude
      if nameStr.endsWith "sin" || nameStr.endsWith "cos" then
        if args.size > 0 then
          let arg := args.back!
          if let some q ← extractRatFromReal arg then
            let mag := (q.num.natAbs * 3 / q.den).max 10
            let childDepth ← go arg
            return Nat.max mag childDepth
          else
            let childDepth ← go arg
            return childDepth
      -- log needs ~3x for large arguments
      if nameStr.endsWith "log" then
        if args.size > 0 then
          let arg := args.back!
          if let some q ← extractRatFromReal arg then
            let mag := (q.num.natAbs * 3 / q.den).max 10
            let childDepth ← go arg
            return Nat.max mag childDepth
          else
            let childDepth ← go arg
            return childDepth
    -- For binary ops (add, mul, sub, div), recurse into both sides
    if fn.isConst then
      let name := fn.constName!
      if name == ``HAdd.hAdd || name == ``HSub.hSub ||
         name == ``HMul.hMul || name == ``HDiv.hDiv then
        if args.size >= 6 then
          let d1 ← go args[4]!
          let d2 ← go args[5]!
          return Nat.max d1 d2
      if name == ``Neg.neg && args.size >= 3 then
        return ← go args[2]!
    return 10

/-- Flatten a real-valued addition expression into its summand terms. -/
private partial def flattenAdd (e : Lean.Expr) : List Lean.Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConst && fn.constName! == ``HAdd.hAdd && args.size >= 6 then
    flattenAdd args[4]! ++ flattenAdd args[5]!
  else
    [e]

/-- Rebuild a real-valued sum expression from a list of terms. -/
private def rebuildSum (terms : List Lean.Expr) : MetaM Lean.Expr := do
  match terms with
  | [] => throwError "rebuildSum: empty list"
  | [t] => pure t
  | t :: rest => do
    let acc ← rebuildSum rest
    mkAppM ``HAdd.hAdd #[t, acc]

/-- Compute an upper bound for a real expression by reifying it and evaluating the interval.
    Returns the `.hi` of the interval as a rational number, cast to ℝ syntax. -/
private def computeUpperBoundExpr (e : Lean.Expr) (taylorDepth : Nat) : MetaM Lean.Expr := do
  -- Reify the expression to a LeanCert.Core.Expr
  let ast ← reify e
  let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]
  let zeroRat : ℚ := 0
  let leProof ← mkAppM ``le_refl #[toExpr zeroRat]
  let intervalExpr ← mkAppM ``IntervalRat.mk #[toExpr zeroRat, toExpr zeroRat, leProof]
  -- Build: (evalIntervalCore1 ast interval cfg).hi
  let evalResult ← mkAppM ``evalIntervalCore1 #[ast, intervalExpr, cfgExpr]
  let hiExpr ← mkAppM ``IntervalRat.hi #[evalResult]
  -- Reduce to a concrete rational value
  let hiReduced ← withTransparency TransparencyMode.all <| reduce hiExpr
  -- Return as ↑(q : ℚ) : ℝ
  mkAppOptM ``Rat.cast #[mkConst ``Real, none, hiReduced]

/-- Try to prove a point inequality by splitting large sums into smaller groups.
    Each group is proved separately via `interval_decide`, then combined with `linarith`.
    Returns `true` if the goal was closed. -/
private def trySumSplitting (taylorDepth : Nat) (groupSize : Nat := 10) : TacticM Bool := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Parse as point inequality
  let some (lhs, _rhs, isStrict, _isReversed) ← parsePointIneq goalType
    | return false
  -- Only handle non-strict ≤ for now
  if isStrict then return false
  -- The function side should be a sum (any size, we'll try direct proof first)
  let terms := flattenAdd lhs
  -- Skip single terms (not a sum) but allow small sums (≥2 terms)
  if terms.length < 2 then return false
  trace[interval_decide] "Sum splitting: found {terms.length} terms, splitting into groups of {groupSize}"
  -- Partition into groups
  let mut groups : Array (List Lean.Expr) := #[]
  let termsArr := terms.toArray
  let mut i := 0
  while i < termsArr.size do
    let endIdx := min (i + groupSize) termsArr.size
    groups := groups.push (termsArr.toList.drop i |>.take (endIdx - i))
    i := endIdx
  -- For each group, compute its interval upper bound and prove the sub-inequality
  for (group, idx) in groups.toList.zip (List.range groups.size) do
    let groupExpr ← rebuildSum group
    -- Compute the upper bound for this group via interval evaluation
    let boundExpr ← try
      computeUpperBoundExpr groupExpr taylorDepth
    catch _ =>
      trace[interval_decide] "Sum splitting: failed to compute bound for group {idx}"
      return false
    let boundStx ← Term.exprToSyntax boundExpr
    let groupStx ← Term.exprToSyntax groupExpr
    let haveNameId := mkIdent (Name.mkSimple s!"h_group_{idx}")
    try
      -- Create the have goal and prove it with intervalDecideCore
      evalTactic (← `(tactic|
        have $haveNameId : $groupStx ≤ $boundStx := by skip
      ))
      -- The new goal from `skip` is `groupExpr ≤ boundExpr`
      intervalDecideCore taylorDepth
    catch _ =>
      trace[interval_decide] "Sum splitting: failed to prove group {idx}"
      return false
  -- Close the original goal with linarith using all the group bounds
  try
    evalTactic (← `(tactic| linarith))
    return true
  catch _ =>
    trace[interval_decide] "Sum splitting: linarith failed to combine group bounds"
    return false

/-- Run interval_decide on a single goal (non-conjunction) -/
private def intervalDecideSingle (depth : Option Nat) : TacticM Unit := do
  match depth with
  | some n =>
    let goalState ← saveState
    let goalType ← getMainTarget
    -- If we can estimate a much smaller depth, try it first to save time.
    let est ← estimateTranscendentalDepth goalType
    let est' := Nat.min est n
    let depths : List Nat :=
      if est' + 5 < n then [est', n] else [n]
    let mut lastError : Option Exception := none
    for d in depths do
      try
        restoreState goalState
        intervalDecideCore d
        return
      catch e =>
        lastError := some e
        continue
    restoreState goalState
    let splitSuccess ← trySumSplitting n
    if splitSuccess then return
    match lastError with
    | some e => throw e
    | none => throwError "interval_decide: failed at all depth levels"
  | none =>
    let goalType ← getMainTarget
    let est ← estimateTranscendentalDepth goalType
    let depths :=
      if est > 10 then
        [est, est + 10, est + 20]
      else
        [10, 15, 20, 25, 30]
    trace[interval_decide] "Estimated depth: {est}, trying depths: {depths}"
    let goalState ← saveState
    let mut lastError : Option Exception := none
    for d in depths do
      try
        restoreState goalState
        trace[interval_decide] "Trying Taylor depth {d}..."
        intervalDecideCore d
        trace[interval_decide] "Success with Taylor depth {d}"
        return
      catch e =>
        lastError := some e
        continue
    -- All depths failed — try sum splitting as a last resort
    let est2 := if est > 10 then est else 30
    restoreState goalState
    let splitSuccess ← trySumSplitting est2
    if splitSuccess then return
    match lastError with
    | some e => throw e
    | none => throwError "interval_decide: failed at all depth levels"

/-- Recursively handle conjunctions and disjunctions, then apply intervalDecideSingle -/
partial def intervalDecideWithConnectives (depth : Option Nat) : TacticM Unit := do
  intervalNormCore
  let goal ← getMainTarget
  if goal.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| constructor))
    let goals ← getGoals
    match goals with
    | g1 :: g2 :: rest =>
      setGoals [g1]
      intervalDecideWithConnectives depth
      setGoals [g2]
      intervalDecideWithConnectives depth
      setGoals rest
    | [g1] =>
      setGoals [g1]
      intervalDecideWithConnectives depth
    | [] =>
      pure ()
  else if goal.isAppOfArity ``Or 2 then
    let savedState ← saveState
    try
      evalTactic (← `(tactic| left))
      intervalDecideWithConnectives depth
    catch _ =>
      savedState.restore
      evalTactic (← `(tactic| right))
      intervalDecideWithConnectives depth
  else
    intervalDecideSingle depth

elab "interval_decide" depth:(num)? : tactic => do
  intervalDecideWithConnectives (depth.map (·.getNat))

end LeanCert.Tactic.Auto
