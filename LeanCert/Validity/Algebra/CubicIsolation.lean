/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.CubicRadius
import LeanCert.Validity.Bounds

/-!
# Complete isolation certificates for exact rational cubics

This Validity-layer module composes the algebraic three-root count with three
computable interval-Newton certificates.  The Engine algebra modules remain
independent of Golden-Theorem imports.
-/

namespace LeanCert.Validity.Algebra

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Algebra
open LeanCert.Validity.RootFinding

/-- Check the global count, the three local Newton contractions, and interval
disjointness. -/
def cubicIsolationCheck (P : QCubic) (cert : CubicIsolationCert) : Bool :=
  P.threeRootCountCheck && cert.intervalsOrdered &&
    checkNewtonContractsCore P.toExpr cert.left cert.cfg &&
    checkNewtonContractsCore P.toExpr cert.middle cert.cfg &&
    checkNewtonContractsCore P.toExpr cert.right cert.cfg

/-- Soundness theorem for complete cubic isolation. -/
theorem cubicIsolationCheck_sound (P : QCubic) (cert : CubicIsolationCert)
    (h : cubicIsolationCheck P cert = true) :
    (∃! x, x ∈ cert.left ∧ Expr.eval (fun _ => x) P.toExpr = 0) ∧
    (∃! x, x ∈ cert.middle ∧ Expr.eval (fun _ => x) P.toExpr = 0) ∧
    (∃! x, x ∈ cert.right ∧ Expr.eval (fun _ => x) P.toExpr = 0) ∧
    cubicZeroSet P.toReal ⊆
      intervalSet cert.left ∪ intervalSet cert.middle ∪ intervalSet cert.right := by
  rw [cubicIsolationCheck] at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hcount, hordered⟩, hleft⟩, hmiddle⟩, hright⟩
  have hcont (I : IntervalRat) :
      ContinuousOn (fun x : ℝ => Expr.eval (fun _ => x) P.toExpr) (Set.Icc I.lo I.hi) :=
    P.toExpr_continuous.continuousOn
  have huLeft := verify_unique_root_computable P.toExpr P.toExpr_supported
    P.toExpr_usesOnlyVar0 cert.left cert.cfg (hcont cert.left) hleft
  have huMiddle := verify_unique_root_computable P.toExpr P.toExpr_supported
    P.toExpr_usesOnlyVar0 cert.middle cert.cfg (hcont cert.middle) hmiddle
  have huRight := verify_unique_root_computable P.toExpr P.toExpr_supported
    P.toExpr_usesOnlyVar0 cert.right cert.cfg (hcont cert.right) hright
  refine ⟨huLeft, huMiddle, huRight, ?_⟩
  have hdisj := cert.ordered_disjoint hordered
  apply three_unique_roots_exhaust (P.threeRootCountCheck_sound hcount)
  · simpa only [mem_intervalSet_iff, cubicZeroSet, Set.mem_setOf_eq, QCubic.toReal,
      QCubic.eval_toExpr] using huLeft
  · simpa only [mem_intervalSet_iff, cubicZeroSet, Set.mem_setOf_eq, QCubic.toReal,
      QCubic.eval_toExpr] using huMiddle
  · simpa only [mem_intervalSet_iff, cubicZeroSet, Set.mem_setOf_eq, QCubic.toReal,
      QCubic.eval_toExpr] using huRight
  · exact hdisj.1
  · exact hdisj.2.1
  · exact hdisj.2.2

/-- A successful complete-isolation check proves one unique root in each of
three ordered intervals and proves that those intervals contain every real
root of the exact rational cubic. -/
theorem verify_complete_cubic_isolation (P : QCubic) (cert : CubicIsolationCert)
    (h : cubicIsolationCheck P cert = true) :
    (∃! x, x ∈ cert.left ∧ Expr.eval (fun _ => x) P.toExpr = 0) ∧
    (∃! x, x ∈ cert.middle ∧ Expr.eval (fun _ => x) P.toExpr = 0) ∧
    (∃! x, x ∈ cert.right ∧ Expr.eval (fun _ => x) P.toExpr = 0) ∧
    cubicZeroSet P.toReal ⊆
      intervalSet cert.left ∪ intervalSet cert.middle ∪ intervalSet cert.right :=
  cubicIsolationCheck_sound P cert h

end LeanCert.Validity.Algebra
