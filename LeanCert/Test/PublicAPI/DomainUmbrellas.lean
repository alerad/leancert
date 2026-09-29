/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert
import LeanCert.ANT

/-!
Compile-time contract for the selected stable domain umbrellas.
-/

#check LeanCert.ANT.StepFn
#check LeanCert.ANT.verify_stepSum_interval

-- Domain libraries extracted into downstream packages must not become
-- dependencies of the retained domain umbrella again.
open Lean in
run_meta do
  for moduleName in (← getEnv).header.moduleNames do
    if (`LeanCert.QProduct).isPrefixOf moduleName ||
        (`LeanCert.ConstantFactory).isPrefixOf moduleName ||
        moduleName.getRoot == `QProduct then
      throwError "Upstream domain umbrella imports extracted module {moduleName}"
