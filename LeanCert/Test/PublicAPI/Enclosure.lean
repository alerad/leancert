/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Enclosure

/-! # Lightweight executable enclosure API and import boundary -/

open Lean Elab Command

#check LeanCert.Tactic.elabEnclosureBound
#check LeanCert.Tactic.elabEnclosureBoundQuestion
#check LeanCert.Tactic.Extension.registeredEnclosureBoundSubdivCoreTyped
#check LeanCert.Tactic.Extension.replayRegisteredEnclosureBoundCoreTyped
#check LeanCert.Tactic.Extension.discoverRegisteredEnclosureBoundMeta
#check LeanCert.Tactic.Extension.replayRegisteredEnclosureBoundMeta

run_meta do
  let env ← getEnv
  if env.header.moduleNames.contains `Mathlib.Tactic then
    throwError "focused enclosure tactic imported the Mathlib tactic umbrella"
  for forbidden in [
      `LeanCert.Tactic.LeanCert.Router,
      `LeanCert.Tactic.Discovery,
      `LeanCert.Tactic.EventualBound,
      `LeanCert.Tactic.FinSumBound,
      `LeanCert.Tactic.Krawczyk,
      `LeanCert.Tactic.Refute] do
    for moduleName in env.header.moduleNames do
      if forbidden.isPrefixOf moduleName then
        throwError "focused enclosure tactic imported unrelated module {moduleName}"
