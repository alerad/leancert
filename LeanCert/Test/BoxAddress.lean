/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.BoxAddress

/-! # Multidimensional subdivision address regression tests -/

namespace LeanCert.Test.BoxAddress

open LeanCert.Core
open LeanCert.Engine.Optimization

private def unitSquare : Box := Box.unit 2

private def axis0 : Fin 2 := ⟨0, by omega⟩
private def axis1 : Fin 2 := ⟨1, by omega⟩

/-- An irregular adaptive schedule: x-left, y-right, x-right. -/
private def adaptivePath : BoxPath 2 :=
  [(axis0, false), (axis1, true), (axis0, true)]

example : BoxPath.widestDecision? unitSquare false = some (axis0, false) := by
  native_decide

example (decision : BoxDecision unitSquare.length)
    (h : BoxPath.widestDecision? unitSquare true = some decision) :
    BoxPath.descend unitSquare decision = unitSquare.splitWidest.2 := by
  simpa using BoxPath.descend_widestDecision?_eq h

example : (adaptivePath.decode unitSquare).length = 2 := by native_decide
example : adaptivePath.decode? unitSquare = some (adaptivePath.decode unitSquare) := by
  native_decide
example : adaptivePath.decode? (Box.unit 1) = none := by native_decide
example : (adaptivePath.decode unitSquare)[0].lo = 1 / 4 := by native_decide
example : (adaptivePath.decode unitSquare)[0].hi = 1 / 2 := by native_decide
example : (adaptivePath.decode unitSquare)[1].lo = 1 / 2 := by native_decide
example : (adaptivePath.decode unitSquare)[1].hi = 1 := by native_decide

example (ρ : Nat → ℝ) (hρ : Box.envMem ρ (adaptivePath.decode unitSquare)) :
    Box.envMem ρ unitSquare :=
  BoxPath.envMem_decode_subset unitSquare adaptivePath ρ hρ

/-- Two balanced levels in two dimensions: x-left, y-right, x-right, y-left. -/
private def morton : MortonAddress :=
  MortonAddress.ofBits 2 2 [false, true, true, false] (by omega) (by decide)

example : morton.code.val = 6 := by native_decide
example : morton.toBoxPath =
    [(axis0, false), (axis1, true), (axis0, true), (axis1, false)] := by
  native_decide
example : morton.toBoxPath.length = 4 := by native_decide
example : (morton.decode unitSquare)[0].lo = 1 / 4 := by native_decide
example : (morton.decode unitSquare)[0].hi = 1 / 2 := by native_decide
example : (morton.decode unitSquare)[1].lo = 1 / 2 := by native_decide
example : (morton.decode unitSquare)[1].hi = 3 / 4 := by native_decide
example : morton.decode? unitSquare = some (morton.decode unitSquare) := by native_decide
example : morton.decode? (Box.unit 3) = none := by native_decide

example : MortonAddress.followsSchedule 2 (by omega) morton.toBoxPath := by native_decide
example : (MortonAddress.ofBoxPath? 2 2 (by omega) morton.toBoxPath).isSome := by
  native_decide
example : MortonAddress.ofBoxPath? 2 2 (by omega) adaptivePath = none := by
  native_decide

end LeanCert.Test.BoxAddress
