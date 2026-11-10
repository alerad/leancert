/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Tactic.Extension.Protocol
public import LeanCert.Tactic.Extension.Registry
public import LeanCert.Tactic.Extension.Command

/-!
# LeanCert downstream tactic extensions

Stable import for registering and inspecting checked downstream enclosure rules.
Automatic execution by `leancert` is intentionally provided by a separate layer.
-/
