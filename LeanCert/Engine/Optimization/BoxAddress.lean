/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicCell
import LeanCert.Engine.Optimization.Box

/-!
# Addressed multidimensional box subdivision

Adaptive paths record both the selected coordinate and the left/right branch.
Morton addresses are deliberately separate: they describe balanced fixed-level
refinement with the regular coordinate schedule `0, 1, ..., dimension - 1`.
-/

namespace LeanCert.Engine.Optimization

open LeanCert.Core

/-- One adaptive box decision: a bounded coordinate and a branch side. -/
abbrev BoxDecision (dimension : Nat) := Fin dimension × Bool

/-- Root-relative provenance for adaptive multidimensional subdivision. -/
abbrev BoxPath (dimension : Nat) := List (BoxDecision dimension)

namespace BoxPath

/-- Address the child selected by the optimizer's widest-axis policy.
Empty boxes have no bounded coordinate and therefore return `none`. -/
def widestDecision? (B : Box) (upper : Bool) : Option (BoxDecision B.length) :=
  if h : B.widestDim < B.length then some (⟨B.widestDim, h⟩, upper) else none

/-- Follow one addressed child. `false` selects the lower child. -/
def descend {dimension : Nat} (B : Box) (decision : BoxDecision dimension) : Box :=
  if decision.2 then (B.split decision.1.val).2 else (B.split decision.1.val).1

theorem descend_widestDecision?_eq {B : Box} {upper : Bool} {decision : BoxDecision B.length}
    (hdecision : widestDecision? B upper = some decision) :
    descend B decision = if upper then B.splitWidest.2 else B.splitWidest.1 := by
  unfold widestDecision? at hdecision
  split at hdecision
  · simp only [Option.some.injEq] at hdecision
    subst decision
    simp [descend, Box.splitWidest]
  · simp at hdecision

/-- Replay an adaptive path from a root box. -/
def decode {dimension : Nat} (root : Box) : BoxPath dimension → Box
  | [] => root
  | decision :: rest => decode (descend root decision) rest

/-- Dimension-checked replay for data arriving across an API or serialization boundary. -/
def decode? {dimension : Nat} (root : Box) (path : BoxPath dimension) : Option Box :=
  if root.length = dimension then some (decode root path) else none

@[simp] theorem decode_nil {dimension : Nat} (root : Box) :
    decode (dimension := dimension) root [] = root := rfl

@[simp] theorem decode_cons {dimension : Nat} (root : Box)
    (decision : BoxDecision dimension) (rest : BoxPath dimension) :
    decode root (decision :: rest) = decode (descend root decision) rest := rfl

theorem descend_length {dimension : Nat} (B : Box) (decision : BoxDecision dimension) :
    (descend B decision).length = B.length := by
  unfold descend
  split <;> simp only [Box.split_length_eq]

/-- Address replay preserves the dimension of the root box. -/
theorem decode_length {dimension : Nat} (root : Box) (path : BoxPath dimension) :
    (decode root path).length = root.length := by
  induction path generalizing root with
  | nil => rfl
  | cons decision rest ih =>
      rw [decode_cons, ih, descend_length]

/-- Every addressed leaf remains a semantic sub-box of its root. -/
theorem envMem_decode_subset {dimension : Nat} (root : Box) (path : BoxPath dimension)
    (ρ : Nat → ℝ) : Box.envMem ρ (decode root path) → Box.envMem ρ root := by
  induction path generalizing root with
  | nil => exact id
  | cons decision rest ih =>
      intro hmem
      have hchild : Box.envMem ρ (descend root decision) := ih _ hmem
      unfold descend at hchild
      split at hchild
      · exact Box.envMem_of_envMem_split_right root decision.1.val ρ hchild
      · exact Box.envMem_of_envMem_split root decision.1.val ρ hchild

end BoxPath

/-- A balanced fixed-level Morton address. Its bits are interleaved by level:
axis `0`, ..., axis `dimension - 1`, then the same schedule at the next level. -/
structure MortonAddress where
  dimension : Nat
  dimension_pos : 0 < dimension
  depth : Nat
  bits : List Bool
  bits_length : bits.length = dimension * depth
  deriving Repr

namespace MortonAddress

def ofBits (dimension depth : Nat) (bits : List Bool) (dimension_pos : 0 < dimension)
    (bits_length : bits.length = dimension * depth) : MortonAddress :=
  ⟨dimension, dimension_pos, depth, bits, bits_length⟩

/-- Numeric Morton/Z-order identifier obtained from the interleaved bit string. -/
def code (address : MortonAddress) : Fin (2 ^ (address.dimension * address.depth)) :=
  ⟨DyadicPath.index address.bits, by
    rw [← address.bits_length]
    exact DyadicPath.index_lt_pow_length address.bits⟩

/-- Expand a Morton address into the primary adaptive path representation. -/
def toBoxPath (address : MortonAddress) : BoxPath address.dimension :=
  address.bits.zipIdx.map fun (bit, index) =>
    (⟨index % address.dimension, Nat.mod_lt _ address.dimension_pos⟩, bit)

@[simp] theorem toBoxPath_length (address : MortonAddress) :
    address.toBoxPath.length = address.dimension * address.depth := by
  simp [toBoxPath, address.bits_length]

/-- Does an adaptive path follow the regular Morton coordinate schedule? -/
def followsSchedule (dimension : Nat) (_dimension_pos : 0 < dimension)
    (path : BoxPath dimension) : Bool :=
  path.zipIdx.all fun (decision, index) =>
    decision.1.val == index % dimension

/-- Convert a balanced regularly scheduled adaptive path to a Morton address.
Irregular adaptive paths are rejected instead of being assigned a misleading ID. -/
def ofBoxPath? (dimension depth : Nat) (dimension_pos : 0 < dimension)
    (path : BoxPath dimension) : Option MortonAddress :=
  if hlength : path.length = dimension * depth then
    if followsSchedule dimension dimension_pos path then
      some ⟨dimension, dimension_pos, depth, path.map (·.2), by simpa using hlength⟩
    else none
  else none

/-- Replay the balanced address through ordinary box splits. -/
def decode (address : MortonAddress) (root : Box) : Box :=
  address.toBoxPath.decode root

/-- Reject a root whose dimension does not match the Morton address. -/
def decode? (address : MortonAddress) (root : Box) : Option Box :=
  address.toBoxPath.decode? root

end MortonAddress

end LeanCert.Engine.Optimization
