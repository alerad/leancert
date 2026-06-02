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

def lhsLeRhsIntervalCert :
    ExprLeOnIntervalDyadicCert lhsX rhsEleven slab010 (-53) 10 where
  supported := lhsLeRhsSupport
  prec_ok := by norm_num
  checked := by native_decide

example :
    ∀ x ∈ Set.Icc (0 : ℝ) 10,
      Expr.eval (fun _ => x) lhsX ≤ Expr.eval (fun _ => x) rhsEleven := by
  simpa [slab010] using lhsLeRhsIntervalCert.verify

def slab05 : IntervalRat := ⟨0, 5, by norm_num⟩

def lhsZero : Expr := Expr.const 0

def rhsOne : Expr := Expr.const 1

def zeroLeOneSupport : ExprSupportedWithInv (Expr.sub lhsZero rhsOne) := by
  unfold lhsZero rhsOne Expr.sub
  exact ExprSupportedWithInv.add
    (ExprSupportedWithInv.const 0)
    (ExprSupportedWithInv.neg (ExprSupportedWithInv.const 1))

def slabTailZeroLeOne : SlabTailCert lhsZero rhsOne where
  cutoff := 0
  tailStart := 5
  slabs := [slab05]
  coversSlabs := by
    intro N hcut htail
    refine ⟨slab05, by simp, ?_⟩
    simp [slab05]
    have hle5 : N ≤ 5 := (Nat.le_of_lt_succ htail).trans (by norm_num)
    exact_mod_cast hle5
  tailBound := by
    intro N _hN
    simp [evalAtNat, lhsZero, rhsOne]

def zeroLeOneSlabsCert :
    ExprLeOnSlabsDyadicCert lhsZero rhsOne slabTailZeroLeOne.slabs (-53) 10 where
  supported := zeroLeOneSupport
  prec_ok := by norm_num
  checked := by native_decide

example (N : Nat) :
    evalAtNat lhsZero N ≤ evalAtNat rhsOne N := by
  exact verify_expr_le_with_slab_tail_dyadic lhsZero rhsOne slabTailZeroLeOne
    (-53) 10 zeroLeOneSlabsCert.supported zeroLeOneSlabsCert.prec_ok
    zeroLeOneSlabsCert.checked N (Nat.zero_le N)

example (N : Nat) :
    evalAtNat lhsZero N ≤ evalAtNat rhsOne N := by
  exact zeroLeOneSlabsCert.verify_with_slab_tail slabTailZeroLeOne rfl
    N (Nat.zero_le N)

end LeanCert.Test.AsympCheckers
