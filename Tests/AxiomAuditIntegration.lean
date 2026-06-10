import LeanCert.Validity.CertificateIntegration

/-!
Axiom guardrail for the certified-integration cluster
(`Validity.Integration` + `Validity.CertificateIntegration`).

This lives in its own file because `Validity.Integration` duplicates
declarations from the `Validity.Bounds` monolith and the two cannot be
imported into one environment (see the note in `Tests/AxiomAudit.lean`).

Same invariant as the main audit: no axiom may be minted inside the LeanCert
namespace (each library-internal `native_decide` would mint a
`<decl>._native.native_decide.ax_*` axiom).
-/

/--
info: 'LeanCert.Validity.Integration.integratePartitionWithInv_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.Integration.integratePartitionWithInv_correct

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
