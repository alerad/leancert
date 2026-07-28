/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean

/-!
# Centralized certificate verification (trust choke point)

Every LeanCert reflective tactic ultimately closes a Boolean certificate goal
of the form `check … = true`. This module is the single place where that goal
gets closed, and therefore the single place where the trusted base of the
resulting proof is decided:

| Mode      | Closes with         | Trusted base                                    |
|-----------|---------------------|-------------------------------------------------|
| `.native` | `native_decide`     | kernel + compiler/runtime (`Lean.ofReduceBool`)  |
| `.kernel` | `decide +kernel`    | kernel only (foundational axioms)                |
| `.auto`   | kernel, then native | kernel when it succeeds; fallback is reported    |

Design rules:

* `.kernel` **never** falls back to native verification. Failure is a hard
  error telling the user how to opt in to native trust explicitly.
* `.auto` may fall back, and reports when it does (`trace[leancert.verification]`
  always; one `logInfo` per process on first fallback).
* The kernel route goes through the `decide +kernel` elaboration path (kernel
  reduction via `mkAuxLemma`: eager in-tactic error reporting plus per-module
  caching) — never raw `Lean.Meta.mkDecideProof`, whose failures on a false or
  stuck certificate surface only at `addDecl` as an unreadable kernel error.

The mode is currently selected with `set_option leancert.trust "kernel"`
(likewise `"native"`, `"auto"`). Tactic-level `(trust := …)` syntax arrives
with the public configuration API.

Caveat for `.auto`: the heartbeat budget bounds elaboration-side work, but
kernel reduction itself is not heartbeat-interruptible; a pathologically large
certificate can exceed the budget wall-clock. Cost-model gating (skipping the
kernel attempt for certificates that are predictably too large) is planned on
top of this hook.
-/

open Lean Meta Elab Tactic

register_option leancert.trust : String := {
  defValue := "native"
  descr := "LeanCert certificate verification route: \"native\" (native_decide; \
    trusts the compiler/runtime), \"kernel\" (decide +kernel; kernel-only \
    trusted base, never falls back), or \"auto\" (try kernel first within \
    leancert.trust.kernelHeartbeats, fall back to native_decide and report)"
}

register_option leancert.trust.kernelHeartbeats : Nat := {
  defValue := 400000
  descr := "heartbeat budget for the kernel verification attempt in \
    leancert.trust = \"auto\" mode (same units as maxHeartbeats)"
}

register_option leancert.trust.autoGate : Bool := {
  defValue := true
  descr := "in leancert.trust = \"auto\" mode, skip the kernel attempt for \
    certificates whose size predictably exceeds the calibrated kernel/native \
    crossover (finite-sum term count, integration partition count, \
    optimization iterations) and go straight to native_decide; see \
    scripts/bench-trust/README.md for the calibration data"
}

register_option leancert.trust.autoMaxSumTerms : Nat := {
  defValue := 2000
  descr := "auto-mode gate: maximum finite-sum term count for which the \
    kernel attempt is made (crossover ≈ 10^4 terms at ~35s/+1.5 GiB; \
    ≤2×10^3 costs under a second)"
}

register_option leancert.trust.autoMaxPartitions : Nat := {
  defValue := 500
  descr := "auto-mode gate: maximum integration partition count for which \
    the kernel attempt is made (500 partitions ≈ +2.5s)"
}

register_option leancert.trust.autoMaxOptIterations : Nat := {
  defValue := 100
  descr := "auto-mode gate: maximum branch-and-bound iteration limit for \
    which the kernel attempt is made (25 iterations ≈ +2s)"
}

namespace LeanCert.Tactic

initialize registerTraceClass `leancert.verification

/-- Reported once per process on the first `.auto`-mode native fallback, so a
file with hundreds of certificate checks does not produce hundreds of
messages. Per-invocation detail is always available under
`trace[leancert.verification]`. -/
initialize autoFallbackReported : IO.Ref Bool ← IO.mkRef false

/-- How a certificate goal is allowed to be verified. -/
inductive VerificationMode where
  /-- Close with `native_decide`; the proof additionally trusts the Lean
  compiler and runtime (`Lean.ofReduceBool`). -/
  | native
  /-- Close with `decide +kernel`; kernel-only trusted base. Never falls back
  to native verification. -/
  | kernel
  /-- Try the kernel route first, fall back to `native_decide`, reporting the
  fallback. -/
  | auto
  deriving DecidableEq, Repr, Inhabited

/-- Which route actually closed a certificate goal. -/
inductive VerificationUsed where
  | kernel
  | native
  deriving DecidableEq, Repr

def VerificationMode.ofString? : String → Option VerificationMode
  | "native" => some .native
  | "kernel" => some .kernel
  | "auto"   => some .auto
  | _        => none

/-- Option-value spelling of the mode (`"kernel"` / `"native"` / `"auto"`). -/
def VerificationMode.asString : VerificationMode → String
  | .native => "native"
  | .kernel => "kernel"
  | .auto   => "auto"

/-- Configuration for certificate verification. Tactics resolve this from
options via `VerificationConfig.current`; a future public `(trust := …)`
syntax will override it per invocation. -/
structure VerificationConfig where
  mode : VerificationMode := .native
  /-- Heartbeat budget for the kernel attempt in `.auto` mode. -/
  kernelHeartbeats : Nat := 400000
  deriving Repr, Inhabited

/-- Read the verification configuration from the current options
(`leancert.trust`, `leancert.trust.kernelHeartbeats`). -/
def VerificationConfig.current : CoreM VerificationConfig := do
  let opts ← getOptions
  let raw := leancert.trust.get opts
  let some mode := VerificationMode.ofString? raw
    | throwError "invalid value '{raw}' for option 'leancert.trust'; \
        expected \"native\", \"kernel\", or \"auto\""
  return { mode, kernelHeartbeats := leancert.trust.kernelHeartbeats.get opts }

private def closeNativeCore (certGoal : MVarId) (tacticName : String) :
    TacticM Unit := do
  setGoals [certGoal]
  try
    evalTactic (← `(tactic| native_decide))
  catch e =>
    throwError "{tacticName}: native_decide failed on certificate check:{indentD e.toMessageData}"

private def closeKernelCore (certGoal : MVarId) (tacticName : String) :
    TacticM Unit := do
  setGoals [certGoal]
  try
    evalTactic (← `(tactic| decide +kernel))
  catch e =>
    throwError "{tacticName}: kernel verification (decide +kernel) failed on \
      certificate check:{indentD e.toMessageData}\n\
      Kernel mode never falls back to native verification. Use \
      `set_option leancert.trust \"native\"` (or \"auto\") to allow \
      `native_decide`, which additionally trusts the compiler."

/-! ### Auto-mode cost gate

Thresholds come from `scripts/bench-trust/baselines/` (see the README there):
kernel reduction is essentially free for point/bound/Newton certificates,
cheap for moderate partition/subdivision counts, and crosses over to
"markedly worse than native" around 10^4 finite-sum terms (superlinear time,
+1.5 GiB RSS). The gate reads scale parameters syntactically off the
certificate goal; anything it does not recognize is attempted normally.

The checker names below are unresolved `Name` literals because this module
deliberately imports only `Lean` (everything in LeanCert imports it back).
`LeanCert/Test/TrustModes.lean` builds these applications with *resolved*
names and asserts the gate fires, so a checker rename breaks CI rather than
silently disabling the gate. -/

/-- First subterm that is a (full enough) application of any of `names`. -/
private def findAppOfAny? (e : Expr) (names : List Name) (minArgs : Nat) :
    Option Expr :=
  e.find? fun sub => names.any (sub.isAppOf ·) && sub.getAppNumArgs ≥ minArgs

/-- Length of a syntactic `List` literal (`List.cons` chain). -/
private partial def listLitLength (e : Expr) (acc : Nat := 0) : Nat :=
  if e.isAppOfArity ``List.cons 3 then listLitLength e.appArg! (acc + 1) else acc

/-- If the certificate is predictably past the kernel/native crossover,
return a human-readable reason to skip the kernel attempt in auto mode.
`none` means "attempt the kernel". -/
def autoGateReason? (opts : Options) (certType : Expr) : Option String := Id.run do
  unless leancert.trust.autoGate.get opts do return none
  let maxSum := leancert.trust.autoMaxSumTerms.get opts
  let maxParts := leancert.trust.autoMaxPartitions.get opts
  let maxIters := leancert.trust.autoMaxOptIterations.get opts
  -- Finite sums over `Finset.Icc a b`: terms = b + 1 - a.
  let sumChecks : List Name :=
    [`LeanCert.Engine.checkFinSumUpperBoundFull, `LeanCert.Engine.checkFinSumLowerBoundFull,
     `LeanCert.Engine.checkFinSumUpperBound, `LeanCert.Engine.checkFinSumLowerBound]
  if let some app := findAppOfAny? certType sumChecks 3 then
    let args := app.getAppArgs
    if let (some a, some b) := (args[1]!.nat?, args[2]!.nat?) then
      let terms := b + 1 - a
      if terms > maxSum then
        return some s!"finite sum with {terms} terms exceeds autoMaxSumTerms={maxSum}"
  -- List-indexed finite sums: term count is the index-list literal length.
  let listChecks : List Name :=
    [`LeanCert.Engine.checkFinSumUpperBoundListFull,
     `LeanCert.Engine.checkFinSumLowerBoundListFull]
  if let some app := findAppOfAny? certType listChecks 3 then
    if listLitLength app.getAppArgs[2]! > maxSum then
      return some s!"list-indexed sum with {listLitLength app.getAppArgs[2]!} \
        terms exceeds autoMaxSumTerms={maxSum}"
  -- Partitioned integration: third argument is the partition count.
  if let some app := findAppOfAny? certType
      [`LeanCert.Validity.Integration.integratePartitionChecked] 3 then
    if let some n := app.getAppArgs[2]!.nat? then
      if n > maxParts then
        return some s!"{n} integration partitions exceed autoMaxPartitions={maxParts}"
  -- Global optimization: read maxIterations off a GlobalOptConfig literal.
  let optChecks : List Name :=
    [`LeanCert.Validity.GlobalOpt.checkGlobalUpperBound,
     `LeanCert.Validity.GlobalOpt.checkGlobalLowerBound,
     `LeanCert.Validity.GlobalOpt.checkGlobalBounds]
  if (findAppOfAny? certType optChecks 4).isSome then
    if let some cfgApp := findAppOfAny? certType
        [`LeanCert.Engine.Optimization.GlobalOptConfig.mk] 1 then
      if let some iters := cfgApp.getAppArgs[0]!.nat? then
        if iters > maxIters then
          return some s!"{iters} optimization iterations exceed autoMaxOptIterations={maxIters}"
  return none

private def closeAutoCore (cfg : VerificationConfig) (certGoal : MVarId)
    (tacticName : String) : TacticM VerificationUsed := do
  let certType ← instantiateMVars (← certGoal.getType)
  if let some reason := autoGateReason? (← getOptions) certType then
    trace[leancert.verification] "{tacticName}: auto gate routed certificate to \
      native_decide ({reason})"
    closeNativeCore certGoal tacticName
    return .native
  let s ← saveState
  try
    withOptions (fun o => o.set `maxHeartbeats cfg.kernelHeartbeats) do
      closeKernelCore certGoal tacticName
    trace[leancert.verification] "{tacticName}: certificate verified by kernel reduction (auto)"
    pure .kernel
  catch e =>
    s.restore
    trace[leancert.verification] "{tacticName}: kernel attempt failed in auto mode, \
      falling back to native_decide:{indentD e.toMessageData}"
    unless (← autoFallbackReported.get) do
      autoFallbackReported.set true
      logInfo m!"{tacticName}: a certificate was verified with native_decide \
        (kernel attempt did not succeed within budget). The proof \
        additionally trusts the compiler. Further fallbacks in this \
        session are reported under `trace[leancert.verification]` only."
    closeNativeCore certGoal tacticName
    pure .native

/-- Close a Boolean certificate goal (`check … = true`) according to the
verification mode, and return which route actually closed it. The surrounding
goal list is saved and restored. -/
def closeCertificateGoal (cfg : VerificationConfig) (certGoal : MVarId)
    (tacticName : String := "leancert") : TacticM VerificationUsed := do
  let savedGoals ← getGoals
  try
    match cfg.mode with
    | .native =>
        closeNativeCore certGoal tacticName
        trace[leancert.verification] "{tacticName}: certificate verified by native_decide"
        pure .native
    | .kernel =>
        closeKernelCore certGoal tacticName
        trace[leancert.verification] "{tacticName}: certificate verified by kernel reduction"
        pure .kernel
    | .auto =>
        closeAutoCore cfg certGoal tacticName
  finally
    -- Restore the surrounding goal list, dropping anything closed in the
    -- meantime (in particular `certGoal` itself when it was the main goal —
    -- callers check goal-list emptiness to detect success).
    setGoals savedGoals
    pruneSolvedGoals

/-- Close the current goal as a LeanCert certificate check according to the
configured verification route (`leancert.trust`, or a `(trust := …)` override
active via `withTrustMode`). For tactic implementations that embed certificate
obligations inside quoted proof terms — `(by leancert_verify_cert)` — where
`closeCertificateGoal` cannot be called directly. Not intended for end users. -/
elab "leancert_verify_cert" : tactic => do
  discard <| closeCertificateGoal (← VerificationConfig.current) (← getMainGoal)
    (tacticName := "leancert")

/-! ## Public per-invocation syntax: `(trust := kernel|native|auto)`

Tactics accept an optional trailing `leancertTrustItem`; when present it
overrides the `leancert.trust` option for that invocation only (implemented
by running the tactic core under `withOptions`, so every certificate check in
the invocation — including nested fallback strategies — honors it). -/

/-- Per-invocation verification route for LeanCert tactics:
`(trust := kernel)`, `(trust := native)`, or `(trust := auto)`. -/
syntax leancertTrustItem := "(" &"trust" " := " ident ")"

/-- Elaborate an optional `(trust := …)` item. -/
def elabTrustItem? : Option (TSyntax ``leancertTrustItem) →
    TacticM (Option VerificationMode)
  | none => pure none
  | some stx =>
    match stx with
    | `(leancertTrustItem| (trust := $m:ident)) => do
      let some mode := VerificationMode.ofString? m.getId.toString
        | throwErrorAt m "invalid trust mode '{m.getId}'; expected kernel, native, or auto"
      return some mode
    | _ => throwUnsupportedSyntax

/-- Run `act` with `leancert.trust` overridden to `mode?` when provided. -/
def withTrustMode (mode? : Option VerificationMode) (act : TacticM α) : TacticM α :=
  match mode? with
  | none => act
  | some m => withOptions (fun o => o.set `leancert.trust m.asString) act

/-! ## `#assert_trust`: CI trust manifests

`#assert_trust kernel thm` / `#assert_trust native thm` pin a theorem's trust
class. Drift in *either* direction fails: a kernel-clean theorem acquiring
native-compiler trust is a regression, and a native-pinned theorem losing its
native dependency means the manifest should be tightened to `kernel`.
`sorryAx` and unrecognized axioms always fail. -/

/-- Trust classification of a single axiom. -/
inductive TrustClass where
  /-- `propext`, `Classical.choice`, `Quot.sound`. -/
  | foundational
  /-- `Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler`, or a
  per-declaration `native_decide` auxiliary (`<decl>._native.native_decide.ax_*`). -/
  | nativeCompiler
  /-- `sorryAx`. -/
  | sorryAx
  /-- Anything else. -/
  | custom
  deriving DecidableEq, Repr

/-- Classify an axiom name into its trust class. -/
def classifyAxiom (n : Name) : TrustClass :=
  if n == ``propext || n == ``Classical.choice || n == ``Quot.sound then
    .foundational
  else if n == ``Lean.ofReduceBool || n == ``Lean.ofReduceNat
      || n == ``Lean.trustCompiler then
    .nativeCompiler
  else if n == ``sorryAx then
    .sorryAx
  else
    match n with
    | .str (.str _ "native_decide") _ => .nativeCompiler
    | _ => .custom

open Elab Command in
/-- `#assert_trust kernel thm`: `thm` depends on foundational axioms only.
`#assert_trust native thm`: `thm` additionally depends on native-compiler
trust (and nothing worse). Any `sorryAx` or unrecognized axiom fails both. -/
elab "#assert_trust " cls:ident thm:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  liftCoreM do
    let axs ← collectAxioms declName
    let part (c : TrustClass) : Array Name := axs.filter (classifyAxiom · == c)
    let foundational := part .foundational
    let native := part .nativeCompiler
    let sorries := part .sorryAx
    let custom := part .custom
    let breakdown : MessageData := MessageData.joinSep
      ([(`foundational, foundational), (`nativeCompiler, native),
        (`sorryAx, sorries), (`custom, custom)].filterMap fun (label, group) =>
        if group.isEmpty then none
        else some m!"  {label}: {MessageData.joinSep (group.toList.map toMessageData) ", "}")
      "\n"
    unless sorries.isEmpty && custom.isEmpty do
      throwErrorAt thm "#assert_trust: '{declName}' depends on sorry or \
        unrecognized axioms\n{breakdown}"
    match cls.getId with
    | `kernel =>
      unless native.isEmpty do
        throwErrorAt thm "#assert_trust kernel: '{declName}' is not \
          kernel-clean\n{breakdown}"
    | `native =>
      if native.isEmpty then
        throwErrorAt thm "#assert_trust native: '{declName}' has no \
          native-compiler dependency; tighten the manifest to `kernel`"
    | other =>
      throwErrorAt cls "#assert_trust: unknown trust class '{other}'; \
        expected 'kernel' or 'native'"

end LeanCert.Tactic
