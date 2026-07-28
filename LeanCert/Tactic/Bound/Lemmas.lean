/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Bounds.Lemmas

/-!
# Compatibility import for interval-bound lemmas

The semantic lemmas formerly implemented in this module now live in
`LeanCert.Engine.Bounds.Lemmas`. This forwarding import preserves the old
module path for downstream code while keeping semantic APIs independent of
the tactic layer.
-/
