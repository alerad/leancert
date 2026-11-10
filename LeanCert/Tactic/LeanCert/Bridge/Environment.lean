/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Core.IntervalRat.Basic

/-! # Environments shared by proof-carrying reification -/

@[expose] public section

namespace LeanCert.Tactic.Bridge

/-- Real environment used by proof-carrying reification. The unary case keeps
the historical constant-environment convention; higher arities use zero beyond
the supplied arguments. -/
def realEnvironment (values : List ℝ) (index : Nat) : ℝ :=
  match values with
  | [value] => value
  | _ => values.getD index 0

end LeanCert.Tactic.Bridge
