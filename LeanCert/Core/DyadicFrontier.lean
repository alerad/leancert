/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicCell

/-!
# Checked addressed dyadic frontiers

An inductive tree makes coverage structural. A flat list of paths is convenient
for untrusted search, serialization, and parallel replay. This module connects
the two with a small checker that reconstructs a tree and accepts only its exact
canonical leaf list. Acceptance certifies that the decoded paths form a complete
binary cover; correspondence between those paths and any external proof or
evaluation records must be maintained by the producer of those records.
-/

namespace LeanCert.Core

/-- A complete binary subdivision tree. A leaf means that the corresponding
closed cell is part of the certificate frontier. -/
inductive DyadicSubdivisionTree where
  | leaf
  | split (left right : DyadicSubdivisionTree)
  deriving Repr, DecidableEq

namespace DyadicSubdivisionTree

/-- Canonical root-relative paths of all leaves, ordered left to right. -/
def paths : DyadicSubdivisionTree → List DyadicPath
  | .leaf => [[]]
  | .split left right =>
      left.paths.map (false :: ·) ++ right.paths.map (true :: ·)

@[simp] theorem paths_leaf : DyadicSubdivisionTree.leaf.paths = [[]] := rfl

@[simp] theorem paths_split (left right : DyadicSubdivisionTree) :
    (DyadicSubdivisionTree.split left right).paths =
      left.paths.map (false :: ·) ++ right.paths.map (true :: ·) := rfl

/-- Every point in the root belongs to at least one closed leaf cell. -/
theorem exists_mem_decode (tree : DyadicSubdivisionTree) (root : IntervalDyadic)
    {x : ℝ} (hx : x ∈ root) :
    ∃ path ∈ tree.paths, x ∈ path.decodeByBisection root := by
  induction tree generalizing root with
  | leaf => exact ⟨[], by simp, hx⟩
  | split left right ihLeft ihRight =>
      rcases IntervalDyadic.mem_bisect_or hx with hleft | hright
      · obtain ⟨path, hpath, hmem⟩ := ihLeft (root := root.bisect.1) hleft
        refine ⟨false :: path, ?_, ?_⟩
        · simp [hpath]
        · simpa [DyadicPath.decodeByBisection] using hmem
      · obtain ⟨path, hpath, hmem⟩ := ihRight (root := root.bisect.2) hright
        refine ⟨true :: path, ?_, ?_⟩
        · simp [hpath]
        · simpa [DyadicPath.decodeByBisection] using hmem

end DyadicSubdivisionTree

namespace DyadicFrontier

/-- Maximum submitted path length, used only as reconstruction fuel. -/
def maxDepth : List DyadicPath → Nat
  | [] => 0
  | path :: rest => max path.length (maxDepth rest)

private def leftTails (leaves : List DyadicPath) : List DyadicPath :=
  leaves.filterMap fun
    | false :: rest => some rest
    | _ => none

private def rightTails (leaves : List DyadicPath) : List DyadicPath :=
  leaves.filterMap fun
    | true :: rest => some rest
    | _ => none

/-- Reconstruct a candidate tree. The final checker below separately verifies
that no submitted leaf was lost, duplicated, reordered, or made redundant. -/
private def reconstructFuel : Nat → List DyadicPath → Option DyadicSubdivisionTree
  | 0, leaves => if leaves = [[]] then some .leaf else none
  | fuel + 1, leaves =>
      if leaves = [[]] then
        some .leaf
      else if leaves.any List.isEmpty then
        none
      else
        match reconstructFuel fuel (leftTails leaves),
            reconstructFuel fuel (rightTails leaves) with
        | some left, some right => some (.split left right)
        | _, _ => none

/-- Structurally check a flat, canonically ordered list of addressed leaves. On
success the returned tree is a proof-friendly reconstruction of precisely those
leaves. This does not independently associate the paths with external leaf
evidence. -/
def check (leaves : List DyadicPath) : Option DyadicSubdivisionTree :=
  match reconstructFuel (maxDepth leaves + 1) leaves with
  | some tree => if tree.paths = leaves then some tree else none
  | none => none

/-- Successful checking pins the reconstructed tree to the submitted paths. -/
theorem check_eq_some_paths {leaves : List DyadicPath} {tree : DyadicSubdivisionTree}
    (hcheck : check leaves = some tree) : tree.paths = leaves := by
  unfold check at hcheck
  split at hcheck <;> try contradiction
  next candidate hcandidate =>
    split at hcheck <;> simp_all

/-- Golden coverage theorem for an accepted flat frontier. -/
theorem exists_mem_decode_of_check {leaves : List DyadicPath}
    {tree : DyadicSubdivisionTree} (hcheck : check leaves = some tree)
    (root : IntervalDyadic) {x : ℝ} (hx : x ∈ root) :
    ∃ path ∈ leaves, x ∈ path.decodeByBisection root := by
  obtain ⟨path, hpath, hmem⟩ := tree.exists_mem_decode root hx
  exact ⟨path, by simpa [check_eq_some_paths hcheck] using hpath, hmem⟩

end DyadicFrontier

end LeanCert.Core
