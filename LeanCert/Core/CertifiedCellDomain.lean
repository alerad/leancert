/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import Mathlib.Data.Rat.Defs

/-!
# Certified cell domains

This module isolates the geometric facts required by certified subdivision.
Search policy, addresses, ownership, measures, and numerical evaluation remain
separate capabilities.

Unlike an interface with a distinguished `root`, every cell here may be used as
the root of a refinement. This is necessary for recursive and nested searches.
-/

namespace LeanCert.Core

/-- Geometry required by a certified finite subdivision step.

`childrenCover` is the trusted fact that turns a search tree into a geometric
cover. The shape of the tree alone is not sufficient. -/
class CertifiedCellDomain (Cell : Type u) (Point : outParam (Type v)) where
  /-- Closed proof cells produced by one refinement step. -/
  children : Cell → List Cell
  /-- Semantic point membership in a closed proof cell. -/
  contains : Cell → Point → Prop
  /-- A rational size bound used to guide refinement. -/
  diameter : Cell → ℚ
  /-- A child never contains a point outside its parent. -/
  childSubset : ∀ {parent child : Cell} {x : Point},
    child ∈ children parent → contains child x → contains parent x
  /-- The closed children cover their parent, including shared seams. -/
  childrenCover : ∀ {parent : Cell} {x : Point},
    contains parent x → ∃ child, child ∈ children parent ∧ contains child x
  /-- Geometric diameters are nonnegative. -/
  diameter_nonneg : ∀ cell, 0 ≤ diameter cell

namespace CertifiedCellDomain

variable {Cell : Type u} {Point : Type v} [CertifiedCellDomain Cell Point]

/-- Refine every cell at a level, producing the complete closed frontier after
exactly `depth` subdivision steps. -/
def refineLevel : Nat → Cell → List Cell
  | 0, cell => [cell]
  | depth + 1, cell =>
      (CertifiedCellDomain.children cell).flatMap (refineLevel depth)

@[simp] theorem refineLevel_zero (cell : Cell) :
    refineLevel (Point := Point) 0 cell = [cell] := rfl

@[simp] theorem refineLevel_succ (depth : Nat) (cell : Cell) :
    refineLevel (Point := Point) (depth + 1) cell =
      (CertifiedCellDomain.children cell).flatMap (refineLevel depth) := rfl

/-- Every descendant in a complete level remains semantically inside its root. -/
theorem contains_of_mem_refineLevel {depth : Nat} {root child : Cell} {x : Point}
    (hchild : child ∈ refineLevel (Point := Point) depth root)
    (hx : CertifiedCellDomain.contains child x) :
    CertifiedCellDomain.contains root x := by
  induction depth generalizing root with
  | zero =>
      simp only [refineLevel, List.mem_singleton] at hchild
      subst child
      exact hx
  | succ depth ih =>
      simp only [refineLevel, List.mem_flatMap] at hchild
      obtain ⟨parent, hparent, hchild⟩ := hchild
      exact CertifiedCellDomain.childSubset hparent (ih hchild)

/-- Complete finite refinement preserves coverage at every depth. -/
theorem exists_mem_refineLevel {depth : Nat} {root : Cell} {x : Point}
    (hx : CertifiedCellDomain.contains root x) :
    ∃ child, child ∈ refineLevel (Point := Point) depth root ∧
      CertifiedCellDomain.contains child x := by
  induction depth generalizing root with
  | zero =>
      exact ⟨root, by simp [refineLevel], hx⟩
  | succ depth ih =>
      obtain ⟨parent, hparent, hxParent⟩ :=
        CertifiedCellDomain.childrenCover hx
      obtain ⟨child, hchild, hxChild⟩ := ih hxParent
      refine ⟨child, ?_, hxChild⟩
      simp only [refineLevel, List.mem_flatMap]
      exact ⟨parent, hparent, hchild⟩

end CertifiedCellDomain

end LeanCert.Core
