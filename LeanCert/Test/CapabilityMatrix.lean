/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Capabilities

namespace LeanCert.Test.CapabilityMatrix

open LeanCert

#guard capabilityRegistryComplete
#guard capabilityEngineMatchesDispatcher

run_cmd do
  let docs ← IO.FS.readFile "docs/architecture/backend-selection.md"
  unless (docs.splitOn capabilityMatrixMarkdown).length > 1 do
    throwError
      "docs/architecture/backend-selection.md does not contain the generated capability matrix"

end LeanCert.Test.CapabilityMatrix
