/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.DyadicAuto
import LeanCert.Meta.ProveSupported
import LeanCert.Engine.IntervalEvalReal

/-!
# Hardening Regression Tests

Small tests for trust-boundary and support-predicate hardening.
-/

open LeanCert.Core
open LeanCert.Engine

namespace LeanCert.Test.Hardening

def hyperbolicWithInvExpr : Expr :=
  Expr.add
    (Expr.sinh (Expr.inv (Expr.add (Expr.var 0) (Expr.const 2))))
    (Expr.add (Expr.cosh (Expr.var 0)) (Expr.tanh (Expr.var 0)))

example : ExprSupportedWithInv hyperbolicWithInvExpr := by
  unfold hyperbolicWithInvExpr
  repeat constructor

def fullUsesOnlyVar0Expr : Expr :=
  Expr.add
    (Expr.sqrt (Expr.add (Expr.var 0) (Expr.const 4)))
    (Expr.add
      (Expr.erf (Expr.tanh (Expr.var 0)))
      (Expr.namedConst .pi))

#guard fullUsesOnlyVar0Expr.usesOnlyVar0 = true

example : UsesOnlyVar0 fullUsesOnlyVar0Expr :=
  Expr.usesOnlyVar0_iff_UsesOnlyVar0.mp (by native_decide)

def realEndpointExtExpr : Expr :=
  Expr.add
    (Expr.tanh (Expr.var 0))
    (Expr.add
      (Expr.sinc (Expr.var 0))
      (Expr.add (Expr.erf (Expr.var 0)) (Expr.namedConst .eulerMascheroni)))

example : ExprSupportedExt realEndpointExtExpr := by
  unfold realEndpointExtExpr
  exact ExprSupportedExt.add
    (ExprSupportedExt.tanh (ExprSupportedExt.var 0))
    (ExprSupportedExt.add
      (ExprSupportedExt.sinc (ExprSupportedExt.var 0))
      (ExprSupportedExt.add
        (ExprSupportedExt.erf (ExprSupportedExt.var 0))
        (ExprSupportedExt.namedConst .eulerMascheroni)))

def I01Real : IntervalReal :=
  ⟨0, 1, by norm_num⟩

example :
    evalIntervalReal1? (Expr.log (Expr.var 0)) I01Real = none := by
  rfl

example :
    evalIntervalReal1? (Expr.tanh (Expr.log (Expr.var 0))) I01Real =
      some ⟨-1, 1, by norm_num⟩ := by
  rfl

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ (2 : ℚ) := by
  certify_kernel_fallback

end LeanCert.Test.Hardening
