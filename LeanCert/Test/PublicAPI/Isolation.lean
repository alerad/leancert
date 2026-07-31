/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Bounds
import LeanCert.API.Backend
import LeanCert.API.Optimization

/-! # Stable programmatic API import-isolation contract -/

open Lean Elab Command

run_meta do
  let env ← getEnv
  for name in [
      `LeanCert.Tactic.closeCertificateGoalTyped,
      `LeanCert.Tactic.Auto.intervalDecideCore] do
    if env.contains name then
      throwError "programmatic API leaked tactic declaration {name}"
  for moduleName in env.header.moduleNames do
    if (`LeanCert.Tactic).isPrefixOf moduleName then
      throwError "programmatic API imported tactic module {moduleName}"
    if (`LeanCert.ANT).isPrefixOf moduleName ||
        (`LeanCert.ML).isPrefixOf moduleName ||
        (`LeanCert.Examples).isPrefixOf moduleName ||
        (`LeanCert.Engine.Chebyshev.Psi).isPrefixOf moduleName ||
        (`LeanCert.Engine.Chebyshev.Theta).isPrefixOf moduleName then
      throwError "programmatic API imported heavyweight domain module {moduleName}"
