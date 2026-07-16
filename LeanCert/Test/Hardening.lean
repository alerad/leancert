/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.DyadicAuto
import LeanCert.Meta.ProveSupported
import LeanCert.Engine.AD.Eval
import LeanCert.Engine.IntervalEvalReal
import LeanCert.Engine.IntervalEvalAffine
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.Eval.Extended
import LeanCert.Engine.Optimization.Global
import LeanCert.Validity.AffineBounds

/-!
# Hardening Regression Tests

Small tests for trust-boundary and support-predicate hardening.
-/

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

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

example :
    evalIntervalRefined1? (Expr.log (Expr.var 0)) ⟨0, 1, by norm_num⟩ = none := by
  rfl

example :
    evalIntervalRefined1? (Expr.sinc (Expr.log (Expr.var 0))) ⟨0, 1, by norm_num⟩ =
      some ⟨-1, 1, by norm_num⟩ := by
  rfl

def affineHardeningEnv : AffineEnv :=
  toAffineEnv [⟨-1, 1, by norm_num⟩]

example :
    (evalIntervalAffine? (Expr.arsinh (Expr.var 0)) affineHardeningEnv).isSome := by
  native_decide

example :
    LeanCert.Validity.checkUpperBoundAffine1Strict
      (Expr.arsinh (Expr.var 0)) ⟨-1, 1, by norm_num⟩ 2 = true := by
  native_decide

def IHalf : IntervalRat := ⟨1 / 2, 1 / 2, by norm_num⟩

def IZeroOne : IntervalRat := ⟨0, 1, by norm_num⟩

#guard (match evalIntervalChecked (Expr.atanh (Expr.var 0)) (fun _ => IHalf) with
  | .ok I => 0 < I.lo ∧ I.lo ≤ I.hi
  | .error _ => false)

#guard (match evalIntervalChecked (Expr.inv (Expr.var 0)) (fun _ => IZeroOne) with
  | .error (.reciprocalContainsZero _) => true
  | _ => false)

#guard (match evalIntervalChecked (Expr.log (Expr.var 0)) (fun _ => IZeroOne) with
  | .error (.logNonpositive _) => true
  | _ => false)

#guard (match evalIntervalAffineChecked (Expr.atanh (Expr.var 0))
    (toAffineEnv [IHalf]) with
  | .ok a => 0 < a.toInterval.lo ∧ a.toInterval.lo ≤ a.toInterval.hi
  | .error _ => false)

#guard (match evalIntervalAffineChecked (Expr.inv (Expr.var 0))
    (toAffineEnv [IZeroOne]) with
  | .error (.reciprocalContainsZero _) => true
  | _ => false)

#guard (match evalIntervalDyadicChecked (Expr.log (Expr.var 0))
    (toDyadicEnv (fun _ => IZeroOne)) with
  | .error (.logNonpositive _) => true
  | _ => false)

#guard (match globalMinimizeRationalChecked (Expr.inv (Expr.var 0)) [IZeroOne] with
  | .error _ => true
  | .ok _ => false)

example :
    LeanCert.Validity.checkUpperBoundAffine1Strict
      (Expr.log (Expr.var 0)) ⟨0, 1, by norm_num⟩ 1 = false := by
  native_decide

example :
    ∀ x ∈ (⟨1, 2, by norm_num⟩ : IntervalRat),
      Expr.eval (fun _ => x) (Expr.log (Expr.var 0)) ≤ 2 :=
  LeanCert.Validity.verify_upper_bound_affine1_strict
    (Expr.log (Expr.var 0))
    (ExprSupportedCore.log (ExprSupportedCore.var 0))
    ⟨1, 2, by norm_num⟩ 2 {} (by native_decide)

example :
    evalDual?1 (Expr.tanh (Expr.var 0)) ⟨-1, 1, by norm_num⟩ = none := by
  rfl

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ (2 : ℚ) := by
  certify_kernel_fallback

end LeanCert.Test.Hardening
