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

private def closeAutoCore (cfg : VerificationConfig) (certGoal : MVarId)
    (tacticName : String) : TacticM VerificationUsed := do
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

end LeanCert.Tactic
