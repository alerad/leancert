import Mathlib.Util.AssertNoSorry
import LeanCert
-- Library modules not reachable from the root `LeanCert` module are imported
-- explicitly so the whole-library axiom sweep below actually covers them.
-- `LeanCert.Test.*` and `LeanCert.Examples.*` are deliberately excluded:
-- `native_decide` is a legitimate user-facing engine there.
-- Exception: `Li2Bounds` (the PNT+-facing lightweight interface) IS imported,
-- so the sorryAx sweep below can pin its sanctioned sorries exactly.
-- `EulerMascheroniBounds` is also imported: it is sorry-free (native_decide
-- inline), so the sweep verifies it stays that way, and its axiom set is
-- pinned explicitly below.
import LeanCert.Engine.Eval
import LeanCert.Engine.Pisano
import LeanCert.Engine.PentagonLucas
import LeanCert.Engine.TaylorModel.Log1p
import LeanCert.Engine.TaylorModel.TrigReduced
import LeanCert.Core.HermiteBounds
import LeanCert.Core.LogBounds
import LeanCert.Examples.Li2Bounds
import LeanCert.Examples.EulerMascheroniBounds
import LeanCert.Bridge

/-!
Axiom/sorry guardrail for the certified interval evaluation path.

Two layers of protection:

1. `assert_no_sorry` — rejects `sorryAx`.
2. `#guard_msgs in #print axioms` — pins the FULL axiom set of the flagship
   theorems to the three standard Lean/Mathlib axioms. This catches
   `native_decide` (`Lean.ofReduceBool`) creep, which `assert_no_sorry` cannot
   see. A library-internal `native_decide` once leaked into
   `evalIntervalCore_correct` via the Euler–Mascheroni interval proof; these
   guards make that class of regression a build failure.

`native_decide` remains a legitimate *user-facing* verification engine for
certificate checks; the invariant enforced here is that the *library theorems
themselves* do not depend on it.
-/

assert_no_sorry LeanCert.Engine.evalIntervalCore_correct
assert_no_sorry LeanCert.Engine.evalIntervalCore1_correct
assert_no_sorry LeanCert.Core.IntervalRat.mem_logComputable
assert_no_sorry LeanCert.Core.IntervalRat.mem_sinComputableReduced
assert_no_sorry LeanCert.Core.IntervalRat.mem_cosComputableReduced
assert_no_sorry LeanCert.Engine.mem_erfPointComputable
assert_no_sorry LeanCert.Engine.evalIntervalChecked_correct
assert_no_sorry LeanCert.Engine.evalIntervalAffineChecked_correct
assert_no_sorry LeanCert.Engine.evalIntervalDyadicChecked_correct
assert_no_sorry LeanCert.Internal.Eval.dispatch_rational_correct
assert_no_sorry LeanCert.Internal.Eval.dispatch_dyadic_correct
assert_no_sorry LeanCert.Internal.Eval.dispatch_affine_correct
assert_no_sorry LeanCert.Internal.Eval.dispatch_correct
assert_no_sorry LeanCert.evalInterval_correct
assert_no_sorry LeanCert.evalInterval1_correct
assert_no_sorry LeanCert.Backend.Rational.eval_correct
assert_no_sorry LeanCert.Backend.Dyadic.eval_correct
assert_no_sorry LeanCert.Backend.Affine.eval_correct
assert_no_sorry LeanCert.ML.mem_erfGELUIntervalRat
assert_no_sorry LeanCert.ML.mem_erfGELUInterval
assert_no_sorry LeanCert.ML.AffineLayer.forwardInterval_correct
assert_no_sorry LeanCert.ML.ErfGELUFFN.forwardInterval_correct
assert_no_sorry LeanCert.Engine.Optimization.globalMinimizeCheckedWith_lower_correct
assert_no_sorry LeanCert.Engine.Optimization.globalMinimizeRationalChecked_lo_correct
assert_no_sorry LeanCert.Engine.Optimization.globalMinimizeDyadicChecked_lo_correct
assert_no_sorry LeanCert.Engine.Optimization.globalMinimizeAffineChecked_lo_correct
assert_no_sorry LeanCert.Engine.Optimization.globalMinimizeWith_lower_correct
assert_no_sorry LeanCert.Engine.Optimization.globalMaximizeWith_upper_correct
assert_no_sorry LeanCert.Engine.bezoutCheck_sound
assert_no_sorry LeanCert.Validity.Algebra.verify_real_roots_simple
assert_no_sorry LeanCert.Engine.cubicCountCheckSubdiv_sound
assert_no_sorry LeanCert.Validity.Algebra.verify_cubic_root_count_subdiv
assert_no_sorry LeanCert.Engine.Algebra.cubic_root_gap_gt_of_discr_bound
assert_no_sorry LeanCert.Engine.Algebra.cubic_roots_pairwise_gap_gt_of_discr_bound_and_radius
assert_no_sorry LeanCert.Validity.Algebra.cubicIsolationCheck_sound
assert_no_sorry LeanCert.Validity.Algebra.verify_complete_cubic_isolation
assert_no_sorry LeanCert.Engine.QCubic.root_abs_le_cauchyRadius
assert_no_sorry LeanCert.Engine.QCubic.automaticSeparationMesh_check
assert_no_sorry LeanCert.Engine.QCubic.separationMeshCheck_sound
assert_no_sorry LeanCert.Validity.Algebra.verify_cubic_separation_mesh
assert_no_sorry LeanCert.Validity.Algebra.verify_cubic_distinct_roots_separated
assert_no_sorry LeanCert.Validity.combine_upper_bound_general_split
assert_no_sorry LeanCert.Validity.combine_lower_bound_general_split
assert_no_sorry LeanCert.Validity.combine_strict_upper_bound_general_split
assert_no_sorry LeanCert.Validity.combine_strict_lower_bound_general_split

/-! ### Exact axiom pinning (catches `native_decide` / `ofReduceBool` creep) -/

/--
info: 'LeanCert.Engine.evalIntervalCore_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.evalIntervalCore_correct

/--
info: 'LeanCert.Engine.evalIntervalChecked_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.evalIntervalChecked_correct

/--
info: 'LeanCert.Engine.evalIntervalAffineChecked_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.evalIntervalAffineChecked_correct

/--
info: 'LeanCert.Engine.evalIntervalDyadicChecked_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.evalIntervalDyadicChecked_correct

/--
info: 'LeanCert.Engine.Optimization.globalMinimizeWith_lower_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.Optimization.globalMinimizeWith_lower_correct

/--
info: 'LeanCert.Engine.Optimization.globalMaximizeWith_upper_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.Optimization.globalMaximizeWith_upper_correct

/--
info: 'LeanCert.Internal.Eval.dispatch_affine_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Internal.Eval.dispatch_affine_correct

/--
info: 'LeanCert.evalInterval_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.evalInterval_correct

/--
info: 'LeanCert.ML.ErfGELUFFN.forwardInterval_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.ML.ErfGELUFFN.forwardInterval_correct

/--
info: 'LeanCert.Core.MathConst.mem_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.MathConst.mem_interval

/--
info: 'LeanCert.Core.IntervalRat.mem_logComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_logComputable

/--
info: 'LeanCert.Core.IntervalRat.mem_expComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_expComputable

/--
info: 'LeanCert.Core.IntervalRat.mem_sinComputableReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_sinComputableReduced

/--
info: 'LeanCert.Core.IntervalRat.mem_cosComputableReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_cosComputableReduced

/--
info: 'LeanCert.Validity.RootFinding.verify_no_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.RootFinding.verify_no_root

/--
info: 'LeanCert.Engine.bezoutCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.bezoutCheck_sound

/--
info: 'LeanCert.Validity.Algebra.verify_real_roots_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.Algebra.verify_real_roots_simple

/--
info: 'LeanCert.Validity.Algebra.verify_cubic_root_count_subdiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.Algebra.verify_cubic_root_count_subdiv

/--
info: 'LeanCert.Validity.Algebra.verify_complete_cubic_isolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.Algebra.verify_complete_cubic_isolation

/--
info: 'LeanCert.Validity.Algebra.verify_cubic_separation_mesh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.Algebra.verify_cubic_separation_mesh

/--
info: 'LeanCert.Validity.verify_upper_bound_affine1_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.verify_upper_bound_affine1_strict

/--
info: 'LeanCert.Validity.verify_upper_bound_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.verify_upper_bound_dyadic

/--
info: 'LeanCert.Validity.Integration.integratePartitionChecked_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.Integration.integratePartitionChecked_correct

/--
info: 'LeanCert.Engine.QPoly.integral_eq_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.QPoly.integral_eq_of_check

/-! ### Whole-library sweep: no axioms minted inside LeanCert

Every `native_decide` use inside the library mints a per-declaration axiom
(`<decl>._native.native_decide.ax_*`). This sweep walks the entire environment
(the audit imports the full `LeanCert` root module) and fails if ANY axiom
lives in the LeanCert namespace — including private-mangled names, which
per-theorem pinning cannot see. `native_decide` in tactic *quotations* is
unaffected: those axioms are minted in end-user proofs, not in the library. -/

open Lean in
run_meta do
  let env ← getEnv
  let mut offenders : Array Name := #[]
  for (n, info) in env.constants.toList do
    if let .axiomInfo _ := info then
      if (n.toString.splitOn "LeanCert").length > 1 then
        offenders := offenders.push n
  unless offenders.isEmpty do
    throwError "Axioms minted inside LeanCert (library-internal native_decide leak?):\n\
      {offenders.toList}"

/-! ### Euler–Mascheroni bounds: exact axiom pinning

`EulerMascheroni.gamma_lower` / `gamma_upper` are sorry-free but verified via
inline `native_decide` (a `2^20`-term reflective harmonic sum), so their axiom
set is the three standard axioms plus `Lean.ofReduceBool` — the same trust
shape as `PNT_PsiBounds` and the BKLNW bounds. The check below fails if the
set ever grows (in particular, if a `sorry` sneaks in). -/

open Lean in
run_meta do
  let allowedAxioms : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound, ``Lean.ofReduceBool]
  -- `native_decide` mints one auxiliary axiom per declaration, named
  -- `<decl>._native.native_decide.ax_*` and backed by `Lean.ofReduceBool`.
  let isNativeDecideAux (a : Name) : Bool :=
    match a with
    | .str (.str _ "native_decide") _ => true
    | _ => false
  for n in [``EulerMascheroni.gamma_lower, ``EulerMascheroni.gamma_upper,
      ``EulerMascheroni.gamma_bounds, ``EulerMascheroni.gamma_approx] do
    let axs ← collectAxioms n
    for a in axs do
      unless allowedAxioms.contains a || isNativeDecideAux a do
        throwError "{n} depends on unexpected axiom {a} \
          (allowed: propext, Classical.choice, Quot.sound, Lean.ofReduceBool, \
          native_decide auxiliaries)"
    unless axs.contains ``Lean.ofReduceBool || axs.any isNativeDecideAux do
      -- Sanity: the bounds are *supposed* to be native_decide-verified; if
      -- that dependency vanishes, the proof changed shape — re-review.
      logInfo m!"note: {n} no longer depends on native_decide"

/-! ### Whole-library sorryAx sweep (exact allowlist)

`lake build` only *warns* on `sorry`, and the textual CI guard cannot see
inline `:= by sorry` forms or tactic-generated holes. This sweep runs
`collectAxioms` (the `#print axioms` engine) on every public constant declared
in a `LeanCert.*` module and fails if any of them depends on `sorryAx` —
except the four legacy `Li2` interface declarations and their four canonical
`LeanCert.CertifiedBounds.Li2` aliases (the lightweight-interface/heavy-
verification split used by PNT+; see `LeanCert/Examples/Li2Bounds.lean`).
Their verified counterparts and a statement-identity check live in the
`Li2Verified` CI target.

Internal (name-mangled) constants are skipped: a sorry inside an internal
auxiliary taints every public declaration that uses it, so the public sweep
already covers everything importable. -/

open Lean in
run_meta do
  let env ← getEnv
  let allowed : Array Name :=
    #[``Li2.li2_lower, ``Li2.li2_upper, ``Li2.li2_bounds, ``Li2.li2_approx_1045,
      ``LeanCert.CertifiedBounds.Li2.lower,
      ``LeanCert.CertifiedBounds.Li2.upper,
      ``LeanCert.CertifiedBounds.Li2.bounds,
      ``LeanCert.CertifiedBounds.Li2.approx_1045]
  let moduleNames := env.header.moduleNames
  let isLeanCertModule (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
      match moduleNames[idx]? with
      | some m => m.getRoot == `LeanCert
      | none => false
    | none => false
  let mut offenders : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isLeanCertModule n && !n.isInternal && !allowed.contains n then
      let axs ← collectAxioms n
      if axs.contains ``sorryAx then
        offenders := offenders.push n
  unless offenders.isEmpty do
    throwError "Declarations depending on sorryAx outside the sanctioned Li2 \
      interface (see LeanCert/Examples/Li2Bounds.lean):\n{offenders.toList}"
