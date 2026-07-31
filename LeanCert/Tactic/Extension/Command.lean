/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Extension.Registry

/-!
# Inspection command for registered enclosure rules
-/

open Lean Elab Command

namespace LeanCert.Tactic.Extension

/-- Print every enclosure rule, or only rules registered for the supplied function. -/
syntax (name := printLeanCertRules) "#print_leancert_rules" (ppSpace ident)? : command

elab_rules : command
  | `(command| #print_leancert_rules $[$functionStx:ident]?) => do
      let env ← getEnv
      let rules ← match functionStx with
        | none => pure <| getAllUnaryEnclosureRules env
        | some stx =>
            let functionName ← resolveGlobalConstNoOverload stx
            pure <| getUnaryEnclosureRules env functionName
      if rules.isEmpty then
        logInfo "No registered LeanCert enclosure rules."
      else
        let mut message : MessageData := "Registered LeanCert enclosure rules:"
        for rule in rules do
          message := message ++ m!"\n{rule.functionName}\n  theorem: {rule.theoremName}\n  \
            checker: {rule.checkerName}\n  candidate: {rule.candidateName}\n  \
            priority: {rule.rulePriority}\n  kind: unary ℝ → ℝ enclosure"
        logInfo message

end LeanCert.Tactic.Extension
