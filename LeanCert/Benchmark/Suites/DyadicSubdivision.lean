/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Harness
import LeanCert.Core.IntervalDyadic

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

def cases : List Case := [
  subdivisionCase 4 100,
  subdivisionCase 8 10,
  subdivisionCase 12 1
]

end LeanCert.Benchmark.DyadicSubdivision
