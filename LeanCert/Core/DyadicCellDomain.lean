/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.CertifiedCellDomain
import LeanCert.Core.IntervalDyadic

/-!
# Certified dyadic interval subdivision

Exact midpoint bisection supplies the first `CertifiedCellDomain` instance.
Both children are closed: their shared midpoint seam is deliberately retained.
-/

namespace LeanCert.Core

namespace IntervalDyadic

/-- The two exact closed halves used by generic certified subdivision. -/
def certifiedChildren (I : IntervalDyadic) : List IntervalDyadic :=
  [I.bisect.1, I.bisect.2]

instance : CertifiedCellDomain IntervalDyadic ℝ where
  children := certifiedChildren
  contains I x := x ∈ I
  diameter I := I.width.toRat
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
  diameter_nonneg := by
    intro I
    rw [width_toRat]
    exact sub_nonneg.mpr I.le

@[simp] theorem certifiedCell_children (I : IntervalDyadic) :
    CertifiedCellDomain.children I = [I.bisect.1, I.bisect.2] := rfl

@[simp] theorem certifiedCell_contains (I : IntervalDyadic) (x : ℝ) :
    CertifiedCellDomain.contains I x ↔ x ∈ I := Iff.rfl

@[simp] theorem certifiedCell_diameter (I : IntervalDyadic) :
    CertifiedCellDomain.diameter I = I.width.toRat := rfl

end IntervalDyadic

end LeanCert.Core
