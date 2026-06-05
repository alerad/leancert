import LeanCert.Engine.Table

namespace LeanCert.Tests.Table

open LeanCert.Engine

structure Row where
  b : Nat
  next : Nat
  bound : Nat
  deriving Repr, DecidableEq

def rows : Array Row :=
  #[
    { b := 10, next := 20, bound := 7 },
    { b := 20, next := 30, bound := 8 },
    { b := 30, next := 40, bound := 9 }
  ]

def badRows : Array Row :=
  #[
    { b := 10, next := 30, bound := 7 },
    { b := 20, next := 30, bound := 11 },
    { b := 15, next := 40, bound := 9 }
  ]

def table : TableCert Row :=
  { rows := rows }

def checkRow (row : Row) : Bool :=
  row.bound <= 10

def RowValid (row : Row) : Prop :=
  row.bound <= 10

theorem checkRow_sound (row : Row) :
    checkRow row = true → RowValid row := by
  intro h
  unfold checkRow at h
  unfold RowValid
  exact of_decide_eq_true h

example : table.checkAll checkRow = true := by
  native_decide

example : ∀ row, row ∈ table.rows.toList → RowValid row :=
  TableCert.verify table checkRow_sound (by native_decide)

example :
    table.failingIndices checkRow = [] := by
  native_decide

example :
    checkLinkedRows rows (key := Row.b) (nextKey := Row.next) (eqKey := Nat.beq) = true := by
  native_decide

example :
    AdjacentAll (fun current following : Row => current.next = following.b) rows.toList :=
  linkedRows_of_checkLinkedRows (by
    intro a b h
    exact Nat.beq_eq.mp h) (by native_decide)

example :
    checkStrictlyIncreasingBy rows Row.b = true := by
  native_decide

example :
    AdjacentAll (fun current following : Row => current.b < following.b) rows.toList :=
  adjacentIncreasing_of_checkStrictlyIncreasingBy (by native_decide)

example :
    table.failingIndices (fun row => row.bound < 9) = [2] := by
  native_decide

example :
    checkLinkedRows badRows (key := Row.b) (nextKey := Row.next) (eqKey := Nat.beq) = false := by
  native_decide

example :
    checkStrictlyIncreasingBy badRows Row.b = false := by
  native_decide

example :
    (TableCert.mk badRows).failingIndices checkRow = [1] := by
  native_decide

end LeanCert.Tests.Table
