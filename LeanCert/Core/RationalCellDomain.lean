/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.CertifiedCellDomain
import LeanCert.Core.IntervalRat.Basic

/-!
# Certified rational interval subdivision

The ordinary rational backend shares the same closed-cell geometry interface as
the dyadic backend. Numerical representation is deliberately absent from the
generic coverage proofs.
-/

namespace LeanCert.Core

namespace IntervalRat

/-- The two exact closed rational halves used by generic subdivision. -/
def certifiedChildren (I : IntervalRat) : List IntervalRat :=
  [I.bisect.1, I.bisect.2]

instance : CertifiedCellDomain IntervalRat ℝ where
  children := certifiedChildren
  contains I x := x ∈ I
  diameter := IntervalRat.width
  childSubset := by
    intro parent child x hchild hx
    simp only [certifiedChildren, List.mem_cons, List.not_mem_nil, or_false] at hchild
    rcases hchild with rfl | rfl
    · exact mem_of_mem_bisect_left hx
    · exact mem_of_mem_bisect_right hx
  childrenCover := by
    intro parent x hx
    rcases mem_bisect_or hx with hleft | hright
    · exact ⟨parent.bisect.1, by simp [certifiedChildren], hleft⟩
    · exact ⟨parent.bisect.2, by simp [certifiedChildren], hright⟩
  diameter_nonneg := IntervalRat.width_nonneg

@[simp] theorem certifiedCell_children (I : IntervalRat) :
    CertifiedCellDomain.children I = [I.bisect.1, I.bisect.2] := rfl

@[simp] theorem certifiedCell_contains (I : IntervalRat) (x : ℝ) :
    CertifiedCellDomain.contains I x ↔ x ∈ I := Iff.rfl

@[simp] theorem certifiedCell_diameter (I : IntervalRat) :
    CertifiedCellDomain.diameter I = I.width := rfl

end IntervalRat

end LeanCert.Core
