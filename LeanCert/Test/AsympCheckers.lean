/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp

/-!
# Tests for CAEE dyadic checker wrappers
-/

namespace LeanCert.Test.AsympCheckers

open LeanCert.ANT.Asymp
open LeanCert.Core

def slab010 : IntervalRat := ⟨0, 10, by norm_num⟩

def lhsX : Expr := Expr.var 0

def rhsEleven : Expr := Expr.const 11

def lhsLeRhsSupport : ExprSupportedWithInv (Expr.sub lhsX rhsEleven) := by
  unfold lhsX rhsEleven Expr.sub
  exact ExprSupportedWithInv.add
    (ExprSupportedWithInv.var 0)
    (ExprSupportedWithInv.neg (ExprSupportedWithInv.const 11))

example :
    checkExprLeOnIntervalDyadic lhsX rhsEleven slab010 (-53) 10 = true := by
  native_decide

example :
    ∀ x ∈ Set.Icc (0 : ℝ) 10,
      Expr.eval (fun _ => x) lhsX ≤ Expr.eval (fun _ => x) rhsEleven := by
  simpa [slab010] using
    verify_expr_le_on_interval_dyadic lhsX rhsEleven slab010 (-53) 10
      lhsLeRhsSupport (by norm_num) (by native_decide)

example :
    checkExprLeOnSlabsDyadic lhsX rhsEleven [slab010] (-53) 10 = true := by
  native_decide

end LeanCert.Test.AsympCheckers
