/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean.Elab.Tactic.Config

/-!
# LeanCert Router Configuration

Configuration for the semantic `leancert` front door.  `budget` controls how
many deterministic solver strategies may be attempted; it never changes
Lean's heartbeat limit.
-/

namespace LeanCert.Tactic

/-- Configuration shared by `leancert` and `leancert?`. -/
structure LeanCertConfig where
  /-- Maximum number of strategies tried from the intent-specific portfolio. -/
  budget : Nat := 3
  /-- Initial Taylor-model depth used by numerical tactics. -/
  taylorDepth : Nat := 10
  /-- Maximum bisection depth for the subdivision strategy. -/
  subdivisions : Nat := 4
  /-- Iteration limit passed to global optimization strategies. -/
  maxIterations : Nat := 1000
  /-- Enable monotonicity pruning in global optimization strategies. -/
  useMonotonicity : Bool := true
  deriving Inhabited, Repr

/-- Elaborate standard tactic configuration syntax for `LeanCertConfig`. -/
declare_config_elab elabLeanCertConfig LeanCertConfig

end LeanCert.Tactic
