/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Trust-mode regression tests (`leancert.trust`)

Guards the verification choke point (`LeanCert.Tactic.closeCertificateGoal`)
behind `interval_decide`:

* default (native) behavior is unchanged;
* `set_option leancert.trust "kernel"` closes certificates by kernel
  reduction only — the axiom pins below fail if `Lean.ofReduceBool` (or a
  `*.native_decide.ax_*` auxiliary) ever sneaks back in;
* `"auto"` stays foundational on goals the kernel can handle.

The strict `certify_kernel` prototype rotted precisely because its kernel
path had no test exercising it (only `_fallback` variants were tested, which
silently used native verification). These pins are the guard against a
repeat.
-/

open Lean Elab Tactic

private def closeAndExpectVerificationEvent
    (cfg : LeanCert.Tactic.VerificationConfig)
    (requested : LeanCert.Tactic.VerificationMode)
    (used : LeanCert.Tactic.VerificationUsed)
    (cause : LeanCert.Tactic.VerificationCause) : TacticM Unit := do
  let goal ← getMainGoal
  let event ← LeanCert.Tactic.closeCertificateGoalReported cfg goal
    "trust telemetry test"
  unless event.requested == requested do
    throwError "wrong requested verification mode: {repr event}"
  unless event.used == used do
    throwError "wrong observed verification route: {repr event}"
  unless event.cause == cause do
    throwError "wrong verification cause: {repr event}"

elab "close_expect_native_event" : tactic =>
  closeAndExpectVerificationEvent { mode := .native }
    .native .native .explicitNative

elab "close_expect_kernel_event" : tactic =>
  closeAndExpectVerificationEvent { mode := .kernel }
    .kernel .kernel .explicitKernel

elab "close_expect_auto_kernel_event" : tactic =>
  closeAndExpectVerificationEvent { mode := .auto }
    .auto .kernel .autoKernel

example : True := by close_expect_native_event
example : True := by close_expect_kernel_event
example : True := by close_expect_auto_kernel_event

/-! ### Default mode: native (behavior preserved) -/

theorem trustDefaultNative : Real.log 2 < 7/10 := by interval_decide

-- native_decide mints a per-declaration auxiliary axiom; its presence here
-- confirms the default route is unchanged.
open Lean in
run_meta do
  let axs ← collectAxioms ``trustDefaultNative
  let isNativeAux (a : Name) : Bool :=
    match a with
    | .str (.str _ "native_decide") _ => true
    | _ => false
  unless axs.any isNativeAux || axs.contains ``Lean.ofReduceBool do
    throwError "expected trustDefaultNative to be native_decide-verified \
      (default mode changed?); axioms: {axs.toList}"

/-! ### Kernel mode: foundational axioms only, never falls back -/

set_option leancert.trust "kernel" in
theorem trustKernelLogUpper : Real.log 2 < 7/10 := by interval_decide

set_option leancert.trust "kernel" in
theorem trustKernelLogLower : (69 : ℝ)/100 < Real.log 2 := by interval_decide

set_option leancert.trust "kernel" in
theorem trustKernelExp : Real.exp 1 ≤ 2.72 := by interval_decide

/-- info: 'trustKernelLogUpper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelLogUpper

/-- info: 'trustKernelLogLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelLogLower

/-- info: 'trustKernelExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelExp

/-! ### Kernel mode: quantified bounds (`certify_bound`, Phase 2 migration) -/

set_option leancert.trust "kernel" in
theorem trustKernelBoundExp : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_bound

/-- info: 'trustKernelBoundExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelBoundExp

/-! ### Auto mode: kernel-capable goals stay foundational -/

set_option leancert.trust "auto" in
theorem trustAutoLog : Real.log 2 < 7/10 := by interval_decide

/-- info: 'trustAutoLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustAutoLog

/-! ### Public per-invocation syntax: `(trust := …)` (Phase 3) -/

theorem trustSyntaxKernel : Real.log 2 < 7/10 := by
  interval_decide (trust := kernel)

theorem trustSyntaxKernelDepth : Real.log 2 < 7/10 := by
  interval_decide 20 (trust := kernel)

theorem trustSyntaxBound : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_bound (trust := kernel)

theorem trustSyntaxAuto : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  interval_auto (trust := kernel)

theorem trustSyntaxRouter : Real.log 2 < 7/10 := by
  leancert (trust := kernel)

/-! ### Kernel mode: discovery Set.Icc branches (embedded certificate terms) -/

set_option leancert.trust "kernel" in
theorem trustKernelRoots : ∃ x ∈ Set.Icc (0 : ℝ) 2, x * x - 2 = 0 := by
  interval_roots

set_option leancert.trust "kernel" in
theorem trustKernelUniqueRoot : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x * x - 2 = 0 := by
  interval_unique_root

/-! ### Auto-mode cost gate (calibrated thresholds; see scripts/bench-trust) -/

-- Unit test with *resolved* checker names: if a checker is renamed, this
-- breaks CI instead of silently disabling the gate (whose own references
-- are unresolved Name literals to keep Verification.lean import-free).
open Lean Meta LeanCert.Tactic in
run_meta do
  let body ← mkAppM ``LeanCert.Core.Expr.var #[toExpr (0 : Nat)]
  let mkSumCheck (a b : Nat) : MetaM Lean.Expr := do
    let app ← mkAppM ``LeanCert.Engine.checkFinSumUpperBoundFull
      #[body, toExpr a, toExpr b, toExpr (0 : ℚ)]
    mkEq app (toExpr true)
  let opts ← getOptions
  let bigTy ← mkSumCheck 1 5000
  let expected :=
    "finite sum with 5000 terms exceeds autoMaxSumTerms=2000"
  let actual := autoGateReason? opts bigTy
  unless actual == some expected do
    throwError "auto gate reason mismatch: expected {expected}, got {repr actual}"
  let smallTy ← mkSumCheck 1 100
  unless (autoGateReason? opts smallTy).isNone do
    throwError "auto gate wrongly fired on a 100-term finite sum"
  -- disabling the gate must disable the skip
  let noGate := leancert.trust.autoGate.set opts false
  unless (autoGateReason? noGate bigTy).isNone do
    throwError "auto gate fired despite leancert.trust.autoGate=false"

-- End-to-end: past the crossover, auto routes to native (the `native` pin
-- would fail with a tighten-to-kernel hint if the gate stopped working).
-- The body must use the index: constant-body sums are closed by a
-- non-certificate arithmetic strategy and never reach the gate.
set_option leancert.trust "auto" in
theorem trustAutoGatedSum :
    ∑ k ∈ Finset.Icc (1 : ℕ) 5000, (↑k : ℝ) ≤ 12502500 := by
  finsum_bound

#assert_trust native trustAutoGatedSum

-- …while small sums still get kernel verification.
set_option leancert.trust "auto" in
theorem trustAutoSmallSum :
    ∑ k ∈ Finset.Icc (1 : ℕ) 100, (↑k : ℝ) ≤ 5050 := by
  finsum_bound

#assert_trust kernel trustAutoSmallSum

/-! ### `#assert_trust`: the CI manifest command -/

#assert_trust kernel trustSyntaxKernel
#assert_trust kernel trustSyntaxKernelDepth
#assert_trust kernel trustSyntaxBound
#assert_trust kernel trustSyntaxAuto
#assert_trust kernel trustSyntaxRouter
#assert_trust kernel trustKernelLogUpper
#assert_trust kernel trustKernelRoots
#assert_trust kernel trustKernelUniqueRoot
#assert_trust native trustDefaultNative

-- Drift is caught in BOTH directions: pinning `native` on a kernel-clean
-- theorem fails with a tighten-the-manifest hint.
/--
error: #assert_trust native: 'trustSyntaxKernel' has no native-compiler dependency; tighten the manifest to `kernel`
-/
#guard_msgs in
#assert_trust native trustSyntaxKernel

-- Invalid trust mode in the per-invocation syntax errors cleanly.
/--
error: invalid trust mode 'kernle'; expected kernel, native, or auto
-/
#guard_msgs in
example : Real.log 2 < 7/10 := by interval_decide (trust := kernle)

/-! ### Invalid option values error up front -/

/--
error: invalid value 'kernle' for option 'leancert.trust'; expected "native", "kernel", or "auto"
-/
#guard_msgs in
set_option leancert.trust "kernle" in
example : Real.log 2 < 7/10 := by interval_decide
