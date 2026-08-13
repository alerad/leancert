/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Extension

/-! # Stable downstream enclosure-extension API and import boundary -/

open Lean Elab Command

#check LeanCert.Tactic.Extension.UnaryEnclosureRequest
#check LeanCert.Tactic.Extension.EnclosureCandidateFailure
#check LeanCert.Tactic.Extension.UnaryEnclosureCandidate
#check LeanCert.Tactic.Extension.UnaryEnclosureChecker
#check LeanCert.Tactic.Extension.UnaryEnclosureRule
#check LeanCert.Tactic.Extension.RegisteredEnclosureCertificateEntry
#check LeanCert.Tactic.Extension.RegisteredEnclosureCertificateTree
#check LeanCert.Tactic.Extension.RegisteredEnclosureCertificate
#check LeanCert.Tactic.Extension.getUnaryEnclosureRules
#check LeanCert.Tactic.Extension.getAllUnaryEnclosureRules

run_meta do
  let env ← getEnv
  for name in [
      `LeanCert.Tactic.LeanCert.trySolver,
      `LeanCert.Tactic.LeanCert.proveWithTypedSolver] do
    if env.contains name then
      throwError "extension API leaked semantic-router declaration {name}"
  for moduleName in env.header.moduleNames do
    if (`LeanCert.Tactic.LeanCert.Router).isPrefixOf moduleName then
      throwError "extension API imported semantic-router module {moduleName}"
