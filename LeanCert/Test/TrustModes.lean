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

/-! ### Invalid option values error up front -/

/--
error: invalid value 'kernle' for option 'leancert.trust'; expected "native", "kernel", or "auto"
-/
#guard_msgs in
set_option leancert.trust "kernle" in
example : Real.log 2 < 7/10 := by interval_decide
