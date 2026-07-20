/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT

/-!
# PrimeNumberTheoremAnd extended Table 4 checker pattern

A reduced copy of the cell-checking flow in
`IEANTN/FKS2Tables/Table4ExtCore.lean`. This protects the elaboration shape of
the dyadic asymptotic checker, including extraction of its Boolean result and
application of the support-free checked-evaluator theorem.
-/

namespace LeanCert.Test.DownstreamPatterns.Table4Ext

open LeanCert.Core LeanCert.ANT.Asymp

private def lhs : Expr :=
  Expr.exp (Expr.mul (Expr.const (1 / 64)) (Expr.var 0))

private def rhs (q : ℚ) : Expr :=
  Expr.mul (Expr.const q)
    (Expr.mul (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.var 0))

private structure Cell where
  b : ℕ
  b' : ℕ
  eps : ℚ
  lo : ℚ
  hi : ℚ

private def checkCell (c : Cell) : Bool :=
  if h : c.lo ≤ c.hi then
    decide (0 < c.eps) && decide (0 ≤ c.lo) &&
    decide (c.lo * c.lo ≤ (c.b : ℚ)) &&
    decide ((c.b' : ℚ) ≤ c.hi * c.hi) &&
    checkExprLeOnIntervalDyadic lhs (rhs (1 / c.eps))
      ⟨c.lo, c.hi, h⟩ (-50) 8
  else false

/-- A checked table cell yields the expression inequality on its entire slab. -/
private theorem checkedCell_bound (c : Cell) (hc : checkCell c = true) :
    ∀ x ∈ Set.Icc (c.lo : ℝ) c.hi,
      Expr.eval (fun _ => x) lhs ≤ Expr.eval (fun _ => x) (rhs (1 / c.eps)) := by
  unfold checkCell at hc
  split at hc
  case isFalse => simp at hc
  case isTrue hle =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hcheck⟩ := hc
    exact verify_expr_le_on_interval_dyadic lhs (rhs (1 / c.eps))
      ⟨c.lo, c.hi, hle⟩ (-50) 8 (by norm_num) hcheck

end LeanCert.Test.DownstreamPatterns.Table4Ext
