/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.Core.DyadicFrontier

/-!
# Exact dyadic subdivision benchmarks

These cases establish the construction baseline for complete closed-cell
bisection trees. Future addressed-cell and direct-decoding implementations can
be compared against the same depths and semantic total-width check.
-/

namespace LeanCert.Benchmark.DyadicSubdivision

open LeanCert.Core

private def unitInterval : IntervalDyadic :=
  ⟨LeanCert.Core.Dyadic.ofInt 0, LeanCert.Core.Dyadic.ofInt 1,
    by norm_num [LeanCert.Core.Dyadic.toRat_ofInt]⟩

/-- Materialize every closed leaf after `depth` complete bisection levels. -/
def leavesAtDepth (I : IntervalDyadic) : Nat → List IntervalDyadic
  | 0 => [I]
  | depth + 1 =>
      (leavesAtDepth I depth).flatMap fun cell =>
        [cell.bisect.1, cell.bisect.2]

private def runCompleteTree (depth : Nat) : IO Outcome := do
  let leaves := leavesAtDepth unitInterval depth
  let totalWidth := leaves.foldl (fun total cell => total.add cell.width)
    (0 : LeanCert.Core.Dyadic)
  if leaves.length != 2 ^ depth then
    return {
      status := "wrong_leaf_count"
      backendUsed := some "dyadic"
      error := some s!"expected {2 ^ depth} leaves, got {leaves.length}"
    }
  if totalWidth.toRat != unitInterval.width.toRat then
    return {
      status := "wrong_total_width"
      backendUsed := some "dyadic"
      error := some s!"expected width {unitInterval.width.toRat}, got {totalWidth.toRat}"
    }
  return { status := "success", backendUsed := some "dyadic" }

/-- Materialize every fixed-depth leaf directly from its bounded address. -/
def directLeavesAtDepth (I : IntervalDyadic) (depth : Nat) : List IntervalDyadic :=
  List.ofFn fun index : Fin (2 ^ depth) =>
    (DyadicCell.mk depth index).decodeDirect I

/-- Random-access materialization after preparing the shared level width once. -/
def preparedLeavesAtDepth (I : IntervalDyadic) (depth : Nat) : List IntervalDyadic :=
  let level := DyadicCell.PreparedDyadicLevel.prepare I depth
  List.ofFn fun index : Fin level.cellCount => level.intervalAt index

/-- Sequential adjacent-cell materialization from a prepared level. -/
def sequentialLeavesAtDepth (I : IntervalDyadic) (depth : Nat) : List IntervalDyadic :=
  (DyadicCell.PreparedDyadicLevel.prepare I depth).materialize

private def validateLeaves (leaves : List IntervalDyadic) (depth : Nat) : IO Outcome := do
  let totalWidth := leaves.foldl (fun total cell => total.add cell.width)
    (0 : LeanCert.Core.Dyadic)
  if leaves.length != 2 ^ depth then
    return {
      status := "wrong_leaf_count"
      backendUsed := some "dyadic"
      error := some s!"expected {2 ^ depth} leaves, got {leaves.length}"
    }
  if totalWidth.toRat != unitInterval.width.toRat then
    return {
      status := "wrong_total_width"
      backendUsed := some "dyadic"
      error := some s!"expected width {unitInterval.width.toRat}, got {totalWidth.toRat}"
    }
  return { status := "success", backendUsed := some "dyadic" }

private def runDirectCells (depth : Nat) : IO Outcome := do
  validateLeaves (directLeavesAtDepth unitInterval depth) depth

private def runPreparedCells (depth : Nat) : IO Outcome := do
  validateLeaves (preparedLeavesAtDepth unitInterval depth) depth

private def runSequentialCells (depth : Nat) : IO Outcome := do
  validateLeaves (sequentialLeavesAtDepth unitInterval depth) depth

private def runAddressesOnly (depth : Nat) : IO Outcome := do
  let cells := List.ofFn fun index : Fin (2 ^ depth) => DyadicCell.mk depth index
  if cells.length != 2 ^ depth then
    return {
      status := "wrong_cell_count"
      backendUsed := some "dyadic"
      error := some s!"expected {2 ^ depth} cells, got {cells.length}"
    }
  match cells.getLast? with
  | none => return { status := "empty_addresses", backendUsed := some "dyadic" }
  | some last =>
      if last.index.val + 1 != 2 ^ depth then
        return { status := "wrong_last_address", backendUsed := some "dyadic" }
      return { status := "success", backendUsed := some "dyadic" }

/-- Canonically ordered complete frontier at a fixed depth. -/
def pathsAtDepth : Nat → List DyadicPath
  | 0 => [[]]
  | depth + 1 =>
      (pathsAtDepth depth).map (false :: ·) ++
        (pathsAtDepth depth).map (true :: ·)

private def runFrontierCheck (depth : Nat) : IO Outcome := do
  let paths := pathsAtDepth depth
  if paths.length != 2 ^ depth then
    return {
      status := "wrong_path_count"
      backendUsed := some "dyadic"
      error := some s!"expected {2 ^ depth} paths, got {paths.length}"
    }
  match DyadicFrontier.check paths with
  | none =>
      return {
        status := "frontier_rejected"
        backendUsed := some "dyadic"
        error := some "complete fixed-depth frontier failed validation"
      }
  | some tree =>
      if tree.paths != paths then
        return {
          status := "frontier_changed"
          backendUsed := some "dyadic"
          error := some "frontier checker changed the submitted leaf order"
        }
      return { status := "success", backendUsed := some "dyadic" }

private def subdivisionCase (depth innerIterations : Nat) : Case := {
  name := s!"dyadic_subdivision.complete_tree.depth_{depth}"
  family := "dyadic_subdivision"
  tier := if depth < 10 then "micro" else "scaling"
  layer := .algorithm
  backendRequested := "dyadic"
  suites := ["dyadic-subdivision", "all"]
  parameters := [
    ("representation", "closed_interval_tree"),
    ("depth", s!"{depth}"),
    ("expected_leaves", s!"{2 ^ depth}")
  ]
  input := { astNodes := 0, astDepth := depth, variableCount := 1 }
  innerIterations
  run := runCompleteTree depth
}

private def directCellCase (depth innerIterations : Nat) : Case := {
  name := s!"dyadic_subdivision.direct_cells.depth_{depth}"
  family := "dyadic_subdivision"
  tier := if depth < 10 then "micro" else "scaling"
  layer := .algorithm
  backendRequested := "dyadic"
  suites := ["dyadic-subdivision", "all"]
  parameters := [
    ("representation", "direct_addressed_cells"),
    ("depth", s!"{depth}"),
    ("expected_leaves", s!"{2 ^ depth}")
  ]
  input := { astNodes := 0, astDepth := depth, variableCount := 1 }
  innerIterations
  run := runDirectCells depth
}

private def preparedCellCase (depth innerIterations : Nat) : Case := {
  name := s!"dyadic_subdivision.prepared_cells.depth_{depth}"
  family := "dyadic_subdivision"
  tier := if depth < 10 then "micro" else "scaling"
  layer := .algorithm
  backendRequested := "dyadic"
  suites := ["dyadic-subdivision", "all"]
  parameters := [
    ("representation", "prepared_random_access"),
    ("depth", s!"{depth}"),
    ("expected_leaves", s!"{2 ^ depth}")
  ]
  input := { astNodes := 0, astDepth := depth, variableCount := 1 }
  innerIterations
  run := runPreparedCells depth
}

private def sequentialCellCase (depth innerIterations : Nat) : Case := {
  name := s!"dyadic_subdivision.sequential_cells.depth_{depth}"
  family := "dyadic_subdivision"
  tier := if depth < 10 then "micro" else "scaling"
  layer := .algorithm
  backendRequested := "dyadic"
  suites := ["dyadic-subdivision", "all"]
  parameters := [
    ("representation", "prepared_sequential"),
    ("depth", s!"{depth}"),
    ("expected_leaves", s!"{2 ^ depth}")
  ]
  input := { astNodes := 0, astDepth := depth, variableCount := 1 }
  innerIterations
  run := runSequentialCells depth
}

private def addressCase (depth innerIterations : Nat) : Case := {
  name := s!"dyadic_subdivision.addresses_only.depth_{depth}"
  family := "dyadic_subdivision"
  tier := if depth < 10 then "micro" else "scaling"
  layer := .algorithm
  backendRequested := "dyadic"
  suites := ["dyadic-subdivision", "all"]
  parameters := [
    ("representation", "addresses_only"),
    ("depth", s!"{depth}"),
    ("expected_cells", s!"{2 ^ depth}")
  ]
  input := { astNodes := 0, astDepth := depth, variableCount := 1 }
  innerIterations
  run := runAddressesOnly depth
}

private def frontierCheckCase (depth innerIterations : Nat) : Case := {
  name := s!"dyadic_subdivision.frontier_check.depth_{depth}"
  family := "dyadic_subdivision"
  tier := if depth < 10 then "micro" else "scaling"
  layer := .algorithm
  backendRequested := "dyadic"
  suites := ["dyadic-subdivision", "all"]
  parameters := [
    ("representation", "checked_addressed_frontier"),
    ("depth", s!"{depth}"),
    ("expected_leaves", s!"{2 ^ depth}")
  ]
  input := { astNodes := 0, astDepth := depth, variableCount := 1 }
  innerIterations
  run := runFrontierCheck depth
}

def cases : List Case := [
  subdivisionCase 4 100,
  directCellCase 4 100,
  preparedCellCase 4 100,
  sequentialCellCase 4 100,
  addressCase 4 100,
  frontierCheckCase 4 100,
  subdivisionCase 8 10,
  directCellCase 8 10,
  preparedCellCase 8 10,
  sequentialCellCase 8 10,
  addressCase 8 10,
  frontierCheckCase 8 10,
  subdivisionCase 12 1,
  directCellCase 12 1,
  preparedCellCase 12 1,
  sequentialCellCase 12 1,
  addressCase 12 1,
  frontierCheckCase 12 1
]

end LeanCert.Benchmark.DyadicSubdivision
