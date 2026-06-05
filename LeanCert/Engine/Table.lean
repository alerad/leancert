/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

/-!
# Finite Table Certificates

This module provides generic infrastructure for data-driven certificates over
finite tables. The table data and row predicates are project-specific; LeanCert
supplies reusable boolean traversal checkers and their soundness theorems.

The intended workflow is:

1. An untrusted oracle generates an `Array Row`.
2. A project defines a small computable `checkRow : Row → Bool`.
3. A project proves row-level soundness once.
4. `native_decide` proves `TableCert.checkAll table checkRow = true`.

This avoids one theorem per row while keeping the proof boundary small and
fully verified.
-/

namespace LeanCert.Engine

universe u v

/-! ## Row-wise table checking -/

/-- A finite table certificate. The row type and row semantics are supplied by
the project instantiating the table. -/
structure TableCert (Row : Type u) where
  rows : Array Row
  deriving Repr

namespace TableCert

/-- Check every row with a project-provided boolean checker.

This is defined through `Array.toList` so the soundness theorem can reuse simple
list induction while the executable behavior is still a linear traversal. -/
def checkAll (T : TableCert Row) (checker : Row → Bool) : Bool :=
  T.rows.toList.all checker

/-- Return the row indices that fail a checker. This is diagnostic data only; it
is not part of the trusted proof boundary. -/
def failingIndicesFrom (checker : Row → Bool) : List Row → Nat → List Nat
  | [], _ => []
  | row :: rows, i =>
      let rest := failingIndicesFrom checker rows (i + 1)
      if checker row then rest else i :: rest

/-- Return all failing row indices for audit output. -/
def failingIndices (T : TableCert Row) (checker : Row → Bool) : List Nat :=
  failingIndicesFrom checker T.rows.toList 0

theorem row_checked_of_list_all {checker : Row → Bool} {rows : List Row} {row : Row}
    (hall : rows.all checker = true) (hmem : row ∈ rows) :
    checker row = true := by
  exact (List.all_eq_true.mp hall) row hmem

/-- Golden theorem for a checked table: if every row's boolean checker is true
and each true checker implies the semantic row claim, then every row in the
table satisfies that claim. -/
theorem verify
    {Claim : Row → Prop} {checker : Row → Bool} (T : TableCert Row)
    (hsound : ∀ row, checker row = true → Claim row)
    (hall : T.checkAll checker = true) :
    ∀ row, row ∈ T.rows.toList → Claim row := by
  intro row hmem
  exact hsound row (row_checked_of_list_all hall hmem)

end TableCert

/-! ## Adjacent-row and next-entry certificates -/

variable {Row : Type u} {Key : Type v}

/-- `AdjacentAll Rel rows` means `Rel` holds for every adjacent pair in `rows`.
Unlike `List.Pairwise`, this intentionally does not require all earlier rows to
relate to all later rows. That matches table successor certificates. -/
inductive AdjacentAll {Row : Type u} (Rel : Row → Row → Prop) : List Row → Prop
  | nil : AdjacentAll Rel []
  | singleton (row : Row) : AdjacentAll Rel [row]
  | cons {a b : Row} {rest : List Row} :
      Rel a b → AdjacentAll Rel (b :: rest) → AdjacentAll Rel (a :: b :: rest)

/-- Boolean adjacent-pair checker over lists. -/
def checkAdjacentList (rel : Row → Row → Bool) : List Row → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => rel a b && checkAdjacentList rel (b :: rest)

/-- Boolean adjacent-pair checker over arrays. -/
def checkAdjacent (rows : Array Row) (rel : Row → Row → Bool) : Bool :=
  checkAdjacentList rel rows.toList

theorem adjacentAll_of_checkAdjacentList
    {Rel : Row → Row → Prop} {rel : Row → Row → Bool}
    (hsound : ∀ a b, rel a b = true → Rel a b) :
    ∀ {rows : List Row},
      checkAdjacentList rel rows = true → AdjacentAll Rel rows
  | [], _ => AdjacentAll.nil
  | [_], _ => AdjacentAll.singleton _
  | a :: b :: rest, hcheck => by
      simp only [checkAdjacentList] at hcheck
      have hab : rel a b = true := by
        cases h : rel a b <;> simp [h] at hcheck ⊢
      have htail : checkAdjacentList rel (b :: rest) = true := by
        cases h : rel a b <;> simp [h] at hcheck
        exact hcheck
      exact AdjacentAll.cons (hsound a b hab)
        (adjacentAll_of_checkAdjacentList hsound htail)

/-- Soundness theorem for array adjacent-pair checkers. -/
theorem adjacentAll_of_checkAdjacent
    {Rel : Row → Row → Prop} {rel : Row → Row → Bool} {rows : Array Row}
    (hsound : ∀ a b, rel a b = true → Rel a b)
    (hcheck : checkAdjacent rows rel = true) :
    AdjacentAll Rel rows.toList :=
  adjacentAll_of_checkAdjacentList hsound hcheck

/-- Check that every adjacent pair satisfies `nextKey current = key nextRow`, using
a boolean equality supplied by the project. -/
def checkLinkedRows
    (rows : Array Row) (key : Row → Key) (nextKey : Row → Key) (eqKey : Key → Key → Bool) : Bool :=
  checkAdjacent rows fun current following => eqKey (nextKey current) (key following)

/-- Soundness theorem for explicit next-entry witnesses. -/
theorem linkedRows_of_checkLinkedRows
    {rows : Array Row} {key nextKey : Row → Key} {eqKey : Key → Key → Bool}
    (heq : ∀ a b, eqKey a b = true → a = b)
    (hcheck : checkLinkedRows rows key nextKey eqKey = true) :
    AdjacentAll (fun current following => nextKey current = key following) rows.toList := by
  exact adjacentAll_of_checkAdjacent
    (fun current following h =>
      heq (nextKey current) (key following) h)
    hcheck

/-- Check that adjacent row keys are strictly increasing. -/
def checkStrictlyIncreasingBy [LT Key] [DecidableRel (fun a b : Key => a < b)]
    (rows : Array Row) (key : Row → Key) : Bool :=
  checkAdjacent rows fun current following => decide (key current < key following)

/-- Soundness theorem for adjacent strict-increase checks. -/
theorem adjacentIncreasing_of_checkStrictlyIncreasingBy
    [LT Key] [DecidableRel (fun a b : Key => a < b)]
    {rows : Array Row} {key : Row → Key}
    (hcheck : checkStrictlyIncreasingBy rows key = true) :
    AdjacentAll (fun current following => key current < key following) rows.toList := by
  exact adjacentAll_of_checkAdjacent
    (fun current following h => of_decide_eq_true h)
    hcheck

end LeanCert.Engine
