/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.Expr
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Meta.ProveSupported
import LeanCert.Tactic.IntervalAuto.Types
import LeanCert.Tactic.IntervalAuto.Extract

/-!
# Common Proving Utilities

Shared utilities for proving bounds across all interval tactics.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Auto

open LeanCert.Core
open LeanCert.Meta

/-- Try to close a goal with a sequence of tactics -/
def tryCloseWith (tacs : List (TSyntax `tactic)) : TacticM Bool := do
  for tac in tacs do
    let savedState ← saveState
    try
      evalTactic tac
      if (← getGoals).isEmpty then
        return true
    catch _ =>
      restoreState savedState
  return false

/-- Standard tactics for closing side goals -/
def standardCloseTactics : TacticM (List (TSyntax `tactic)) := do
  return [
    ← `(tactic| rfl),
    ← `(tactic| norm_num),
    ← `(tactic| norm_cast),
    ← `(tactic| (norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl)),
    ← `(tactic| (simp only [Rat.divInt_eq_div]; push_cast; rfl)),
    ← `(tactic| (congr 1 <;> norm_num)),
    ← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one])
  ]

/-- Try to close the current goal using standard tactics -/
def tryCloseGoal : TacticM Bool := do
  let tacs ← standardCloseTactics
  tryCloseWith tacs

/-- Parse a ≤ b expression. -/
private def parseLe? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``LE.le)
  guard (args.size >= 4)
  some (args[args.size - 2]!, args[args.size - 1]!)

/-- Parse a < b expression. -/
private def parseLt? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``LT.lt)
  guard (args.size >= 4)
  some (args[args.size - 2]!, args[args.size - 1]!)

/-- Parse x ^ y (either through `HPow.hPow` or `Real.rpow`). -/
private def parsePow? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``HPow.hPow || fn.isConstOf ``Pow.pow then
    guard (args.size >= 2)
    return (args[args.size - 2]!, args[args.size - 1]!)
  if fn.isConstOf ``Real.rpow then
    guard (args.size >= 2)
    return (args[args.size - 2]!, args[args.size - 1]!)
  none

/-- Parse `Real.log x`. -/
private def parseLogArg? (e : Lean.Expr) : Option Lean.Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  guard (fn.isConstOf ``Real.log)
  guard (args.size >= 1)
  return args[args.size - 1]!

/-- Parse `Set.Icc lo hi` as a set expression. -/
private def parseIccSet? (s : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let fn := s.getAppFn
  let args := s.getAppArgs
  guard (fn.isConstOf ``Set.Icc)
  guard (args.size >= 2)
  some (args[args.size - 2]!, args[args.size - 1]!)

/-- Parse an Icc proposition in either `x ∈ Set.Icc lo hi` or `Set.Icc lo hi x` form. -/
private def parseIccProp? (p : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) := do
  -- Membership form: Membership.mem x (Set.Icc lo hi)
  let fn := p.getAppFn
  let args := p.getAppArgs
  if fn.isConstOf ``Membership.mem && args.size >= 2 then
    let x := args[args.size - 2]!
    let s := args[args.size - 1]!
    if let some (lo, hi) := parseIccSet? s then
      return (x, lo, hi)
  -- Application form: Set.Icc lo hi x
  let fn2 := p.getAppFn
  let args2 := p.getAppArgs
  if fn2.isConstOf ``Set.Icc && args2.size >= 3 then
    let lo := args2[args2.size - 3]!
    let hi := args2[args2.size - 2]!
    let x := args2[args2.size - 1]!
    return (x, lo, hi)
  none

/-- Try to solve a fresh goal by running a tactic; returns a proof term on success. -/
private def solveByTactic? (goalTy : Lean.Expr) (tac : TSyntax `tactic) : TacticM (Option Lean.Expr) := do
  let saved ← saveState
  let g ← mkFreshExprMVar goalTy
  setGoals [g.mvarId!]
  try
    evalTactic tac
    if (← getGoals).isEmpty then
      let pf ← instantiateMVars g
      saved.restore
      return some pf
    saved.restore
    return none
  catch _ =>
    saved.restore
    return none

/-- Build `0 < e` type for reals. -/
private def mkZeroLt (e : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← inferType e
  let zero ← mkAppOptM ``Rat.cast #[some ty, none, some (toExpr (0 : Rat))]
  mkAppM ``LT.lt #[zero, e]

/-- Build `1 < e` type for reals. -/
private def mkOneLt (e : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← inferType e
  let one ← mkAppOptM ``Rat.cast #[some ty, none, some (toExpr (1 : Rat))]
  mkAppM ``LT.lt #[one, e]

/-- Collect lower-bound proofs `lo ≤ target` with extracted rational `lo`. -/
private def collectLowerBounds (target : Lean.Expr) : TacticM (Array (ℚ × Lean.Expr × Lean.Expr)) := do
  let mut out : Array (ℚ × Lean.Expr × Lean.Expr) := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail || ldecl.isAuxDecl then
      continue
    let h := mkFVar ldecl.fvarId
    let tyWhnf ← whnf ldecl.type

    -- Direct lower-bound hypothesis: lo ≤ target.
    if let some (lo, rhs) := parseLe? tyWhnf then
      if (← isDefEq rhs target) then
        if let some q ← extractRatFromReal lo then
          out := out.push (q, lo, h)

    -- Strict lower-bound hypothesis: lo < target.
    if let some (lo, rhs) := parseLt? tyWhnf then
      if (← isDefEq rhs target) then
        if let some q ← extractRatFromReal lo then
          let hle ← mkAppM ``le_of_lt #[h]
          out := out.push (q, lo, hle)

    -- Membership/app-style Set.Icc hypotheses.
    if let some (x, lo, _hi) := parseIccProp? tyWhnf then
      if (← isDefEq x target) then
        if let some q ← extractRatFromReal lo then
          let hLoLe ← mkAppM ``And.left #[h]
          out := out.push (q, lo, hLoLe)

    -- Conjunctive hypotheses (e.g. from Set.Icc): extract both sides.
    let fn := tyWhnf.getAppFn
    let args := tyWhnf.getAppArgs
    if fn.isConstOf ``And && args.size >= 2 then
      let leftProp := args[0]!
      let rightProp := args[1]!
      let hLeft ← mkAppM ``And.left #[h]
      let hRight ← mkAppM ``And.right #[h]

      if let some (lo, rhs) := parseLe? leftProp then
        if (← isDefEq rhs target) then
          if let some q ← extractRatFromReal lo then
            out := out.push (q, lo, hLeft)
      if let some (lo, rhs) := parseLt? leftProp then
        if (← isDefEq rhs target) then
          if let some q ← extractRatFromReal lo then
            let hle ← mkAppM ``le_of_lt #[hLeft]
            out := out.push (q, lo, hle)

      if let some (lo, rhs) := parseLe? rightProp then
        if (← isDefEq rhs target) then
          if let some q ← extractRatFromReal lo then
            out := out.push (q, lo, hRight)
      if let some (lo, rhs) := parseLt? rightProp then
        if (← isDefEq rhs target) then
          if let some q ← extractRatFromReal lo then
            let hle ← mkAppM ``le_of_lt #[hRight]
            out := out.push (q, lo, hle)
  return out

/-- Try to prove `0 < target` from collected lower bounds. -/
private def provePositiveFromBounds? (target : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let lbs ← collectLowerBounds target
  for (q, lo, hLoLeTarget) in lbs do
    if q > 0 then
      let some hZeroLtLo ← solveByTactic? (← mkZeroLt lo) (← `(tactic| norm_num))
        | continue
      let hPos ← mkAppM ``lt_of_lt_of_le #[hZeroLtLo, hLoLeTarget]
      return some hPos
  return none

/-- Try to prove `0 < target` from an `Set.Icc` hypothesis in the local context. -/
private def provePositiveFromIccAssumption? (target : Lean.Expr) : TacticM (Option Lean.Expr) := do
  solveByTactic? (← mkZeroLt target) (← `(tactic|
    first
    | exact lt_of_lt_of_le (by norm_num) ((Set.mem_Icc.mp (by assumption)).1)
    | exact lt_of_lt_of_le (by positivity) ((Set.mem_Icc.mp (by assumption)).1)
    | positivity))

/-- Try to prove `0 < log arg` from bounds on `arg`. -/
private def proveLogPositiveFromBounds? (arg : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let lbs ← collectLowerBounds arg
  for (q, lo, hLoLeArg) in lbs do
    if q > 1 then
      let some hOneLtLo ← solveByTactic? (← mkOneLt lo) (← `(tactic| norm_num))
        | continue
      let hOneLtArg ← mkAppM ``lt_of_lt_of_le #[hOneLtLo, hLoLeArg]
      let hLogPos ← mkAppM ``Real.log_pos #[hOneLtArg]
      return some hLogPos
  return none

/-- Try to prove `0 < log arg` from an `Set.Icc` hypothesis on `arg`. -/
private def proveLogPositiveFromIccAssumption? (arg : Lean.Expr) : TacticM (Option Lean.Expr) := do
  solveByTactic? (← mkZeroLt (← mkAppM ``Real.log #[arg])) (← `(tactic|
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) ((Set.mem_Icc.mp (by assumption)).1))))

/-- Try to close side goals generated by reifying `x ^ q` as `exp (log x * q)`. -/
def tryCloseRpowSideGoal : TacticM Bool := do
  let saved ← saveState
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| try intros))
      -- Unfold the reflected RHS into plain real operations.
      evalTactic (← `(tactic|
        simp only [LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_mul,
          LeanCert.Core.Expr.eval_log, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_const]))

      let goal ← getMainGoal
      let goalTy ← instantiateMVars (← goal.getType)
      let some (_eqTy, lhs, rhs) := goalTy.eq?
        | saved.restore; return false

      let orientationAndPow? : Option (Bool × Lean.Expr × Lean.Expr) :=
        match parsePow? lhs with
        | some (base, exp) => some (true, base, exp)
        | none =>
          match parsePow? rhs with
          | some (base, exp) => some (false, base, exp)
          | none => none
      let some (powOnLeft, base, _exp) := orientationAndPow?
        | saved.restore; return false

      -- Prove positivity of the rpow base from interval/domain hypotheses.
      let hPos? ←
        match parseLogArg? base with
        | some arg =>
          -- For `(log arg)^q`, we need `1 < arg`.
          proveLogPositiveFromBounds? arg
        | none =>
          provePositiveFromBounds? base
      let some hPos := hPos?
        | saved.restore; return false

      let hPosSyn ← Lean.Elab.Term.exprToSyntax hPos
      let zeroReal ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit 0), none]
      let hPos0Ty ← mkAppM ``LT.lt #[zeroReal, base]
      let some hPos0 ← solveByTactic? hPos0Ty (← `(tactic| simpa [Rat.cast_zero] using $hPosSyn))
        | saved.restore; return false
      let hPos0Syn ← Lean.Elab.Term.exprToSyntax hPos0
      if powOnLeft then
        evalTactic (← `(tactic|
          simpa [Real.rpow_def_of_pos $hPos0Syn, Rat.divInt_eq_div,
            mul_comm, mul_left_comm, mul_assoc]))
      else
        evalTactic (← `(tactic|
          symm;
          simpa [Real.rpow_def_of_pos $hPos0Syn, Rat.divInt_eq_div,
            mul_comm, mul_left_comm, mul_assoc]))

      if (← getGoals).isEmpty then
        return true
      saved.restore
      return false
    catch _ =>
      saved.restore
      return false

/-- Close all remaining side goals -/
def closeAllSideGoals (tacticName : String) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    setGoals [g]
    if ← tryCloseGoal then
      continue
    else
      logWarning m!"{tacticName}: Could not close side goal: {← g.getType}"

/-- Extract rational bound from possible coercion -/
def extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
  let fn := bound.getAppFn
  let args := bound.getAppArgs

  -- Check for Rat.cast (which is what ↑ becomes for ℚ → ℝ)
  if fn.isConstOf ``Rat.cast then
    if args.size > 0 then
      return args.back!
    else
      throwError "Unexpected Rat.cast structure"
  else if fn.isConstOf ``RatCast.ratCast then
    if args.size > 0 then
      return args.back!
    else
      throwError "Unexpected RatCast.ratCast structure"
  else
    let boundTy ← inferType bound
    if boundTy.isConstOf ``Rat then
      return bound
    else
      if let some q ← extractRatFromReal bound then
        return toExpr q
      else
        let boundReduced ← whnf bound
        let fnReduced := boundReduced.getAppFn
        if fnReduced.isConstOf ``Rat.cast || fnReduced.isConstOf ``RatCast.ratCast then
          let argsReduced := boundReduced.getAppArgs
          if argsReduced.size > 0 then
            return argsReduced.back!
        throwError m!"Cannot extract rational from bound: {bound}\n\n\
                      This happens when the bound contains non-computable constants.\n\
                      Suggestions:\n\
                      • Use a rational approximation\n\
                      • Use interval_decide for point inequalities with transcendentals"

/-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
def getAst (func : Lean.Expr) : TacticM Lean.Expr := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    if fn.isConstOf ``LeanCert.Core.Expr.eval then
      let args := body.getAppArgs
      if args.size ≥ 2 then
        return args[1]!
      else
        throwError m!"Unexpected Expr.eval application structure.\n\
                      Expected: Expr.eval env ast\n\
                      Got {args.size} arguments: {args.toList}"
    else
      reify func

/-- Get support proof for an AST, returning (proof, useWithInv) -/
def getSupportProof (ast : Lean.Expr) : TacticM (Lean.Expr × Bool) := do
  -- First try ExprSupportedCore (simpler, works for most cases)
  try
    let proof ← mkSupportedCoreProof ast
    return (proof, false)
  catch _ =>
    -- Fall back to ExprSupportedWithInv (handles log/inv)
    let proof ← mkSupportedWithInvProof ast
    return (proof, true)

/-- Build a Box expression (List IntervalRat) from an array of VarIntervalInfo -/
def mkBoxExpr (infos : Array VarIntervalInfo) : MetaM Lean.Expr := do
  let intervalRatType := Lean.mkConst ``IntervalRat
  let intervals := infos.map (·.intervalRat)
  mkListLit intervalRatType intervals.toList

/-- Check if a certificate check will succeed (without throwing) -/
def certCheckSucceeds (checkFn : Lean.Expr) : TacticM Bool := do
  let certTy ← mkAppM ``Eq #[checkFn, mkConst ``Bool.true]
  let certGoal ← mkFreshExprMVar certTy
  let certGoalId := certGoal.mvarId!
  let savedState ← saveState
  try
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    restoreState savedState
    return true
  catch _ =>
    restoreState savedState
    return false

/-- Extract bounds from IntervalInfo for subdivision -/
def getSubdivBounds (intervalInfo : IntervalInfo) :
    TacticM (Option (ℚ × ℚ × Lean.Expr × Lean.Expr × Lean.Expr × Bool)) := do
  match intervalInfo.fromSetIcc with
  | some (lo, hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
    return some (lo, hi, loRatExpr, hiRatExpr, leProof, true)
  | none =>
    try
      let intervalVal ← unsafe evalExpr IntervalRat (mkConst ``IntervalRat) intervalInfo.intervalRat
      let lo := intervalVal.lo
      let hi := intervalVal.hi
      let loRatExpr := toExpr lo
      let hiRatExpr := toExpr hi
      let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
      let leProof ← mkDecideProof leProofTy
      return some (lo, hi, loRatExpr, hiRatExpr, leProof, false)
    catch _ =>
      return none

/-- Extract a rational literal from an expression -/
def getLiteral? (e : Lean.Expr) : TacticM (Option ℚ) := do
  try
    let val ← unsafe evalExpr ℚ (mkConst ``Rat) e
    return some val
  catch _ =>
    return none

end LeanCert.Tactic.Auto
