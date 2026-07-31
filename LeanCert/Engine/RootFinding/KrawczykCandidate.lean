/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.RootFinding.Krawczyk

/-!
# Untrusted automatic Krawczyk candidates

This module constructs rational centers and preconditioners for the checked
Krawczyk engine.  None of the search code is trusted: a successful candidate
is useful only after `krawczykCheck` accepts it and the Krawczyk golden theorem
turns that Boolean result into a proof.

The initial center is the rational midpoint of the target box.  At every
attempt we enclose the Jacobian on the singleton center, take entrywise
midpoints, invert that rational matrix by pivoted Gauss--Jordan elimination,
and test the resulting certificate on the original box.  Rejected candidates
may be refined by an interval-Newton midpoint step; the target box itself is
never subdivided.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-- User-independent limits for automatic candidate construction. -/
structure AutomaticKrawczykConfig where
  maxIterations : Nat := 8
  maxDimension : Nat := 4
  /-- Candidate values are rounded to this dyadic precision after every
  untrusted Newton step to prevent rational denominator explosion. -/
  precisionBits : Nat := 20
  deriving Repr, Inhabited

/-- Stable failure classes returned by the untrusted generator. -/
inductive AutomaticKrawczykFailure where
  | invalidDimension
  | dimensionLimit (actual limit : Nat)
  | unsupportedAD
  | singularPointJacobian (attempt : Nat)
  | centerEscaped (attempt : Nat)
  | stagnated (attempt : Nat)
  | exhausted (attempts : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- Dimension-erased output suitable for tactic evaluation and reporting. -/
structure AutomaticKrawczykReport where
  dimension : Nat
  attempts : Nat := 0
  refinements : Nat := 0
  center : List ℚ := []
  preconditioner : List (List ℚ) := []
  contractionBound : ℚ := 0
  failure : Option AutomaticKrawczykFailure := none
  deriving Repr, Inhabited

def AutomaticKrawczykReport.succeeded (report : AutomaticKrawczykReport) : Bool :=
  report.failure.isNone

private def arrayGetD [Inhabited α] (values : Array α) (index : Nat) : α :=
  (values[index]?).getD default

private def matrixArrayGet (rows : Array (Array ℚ)) (i j : Nat) : ℚ :=
  ((rows[i]?).bind fun row => row[j]?).getD 0

private def matrixArraySet (rows : Array (Array ℚ)) (i j : Nat) (value : ℚ) :
    Array (Array ℚ) :=
  match rows[i]? with
  | none => rows
  | some row => rows.set! i (row.set! j value)

private def swapRows (rows : Array (Array ℚ)) (i j : Nat) : Array (Array ℚ) :=
  if i == j then rows
  else
    let left := arrayGetD rows i
    let right := arrayGetD rows j
    (rows.set! i right).set! j left

private def findPivot (rows : Array (Array ℚ)) (column start size : Nat) : Option Nat :=
  (List.range (size - start)).findSome? fun offset =>
    let row := start + offset
    if matrixArrayGet rows row column != 0 then some row else none

private def eliminateColumn (rows : Array (Array ℚ)) (column size : Nat) :
    Array (Array ℚ) :=
  (List.range size).foldl (fun current row =>
    if row == column then current
    else
      let factor := matrixArrayGet current row column
      if factor == 0 then current
      else
        (List.range (2 * size)).foldl (fun updated entry =>
          matrixArraySet updated row entry
            (matrixArrayGet current row entry -
              factor * matrixArrayGet current column entry)) current) rows

private partial def gaussJordanLoop (rows : Array (Array ℚ)) (column size : Nat) :
    Option (Array (Array ℚ)) :=
  if column < size then
    match findPivot rows column column size with
    | none => none
    | some pivotRow =>
        let swapped := swapRows rows column pivotRow
        let pivot := matrixArrayGet swapped column column
        if pivot == 0 then none
        else
          let normalized := (arrayGetD swapped column).map fun value => value / pivot
          let rows := swapped.set! column normalized
          gaussJordanLoop (eliminateColumn rows column size) (column + 1) size
  else
    some rows

private def augmentedMatrix {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ) :
    Array (Array ℚ) :=
  Array.ofFn fun i : Fin n =>
    Array.ofFn fun j : Fin (2 * n) =>
      if h : j.val < n then
        matrix i ⟨j.val, h⟩
      else if j.val - n == i.val then 1 else 0

private def arrayToMatrix {n : Nat} (rows : Array (Array ℚ)) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => matrixArrayGet rows i.val (n + j.val)

/-- Exact rational inversion with row pivoting.  This is candidate-generation
machinery only; `krawczykCheck` independently requires the returned
preconditioner to be nonsingular. -/
def invertRatMatrix? {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ) :
    Option (Matrix (Fin n) (Fin n) ℚ) := do
  if n == 0 then none
  else
    let reduced ← gaussJordanLoop (augmentedMatrix matrix) 0 n
    pure (arrayToMatrix reduced)

def KrawczykCert.ofLists (n : Nat) (center : List ℚ)
    (preconditioner : List (List ℚ)) : KrawczykCert n where
  center i := (center[i.val]?).getD 0
  preconditioner i j := ((preconditioner[i.val]?).bind fun row => row[j.val]?).getD 0

private def roundRat (precisionBits : Nat) (value : ℚ) : ℚ :=
  let bits := min precisionBits 60
  let scale : Nat := 2 ^ bits
  let magnitude := value.num.natAbs
  let rounded := (2 * magnitude * scale + value.den) / (2 * value.den)
  let signed : Int := if value.num < 0 then -(rounded : Int) else (rounded : Int)
  (signed : ℚ) / scale

private def roundMatrix {n : Nat} (precisionBits : Nat)
    (matrix : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => roundRat precisionBits (matrix i j)

private def pointJacobianMidpoint {n : Nat} (F : Fin n → Expr)
    (center : Fin n → ℚ) (cfg : EvalConfig) (precisionBits : Nat) :
    Matrix (Fin n) (Fin n) ℚ :=
  let pointBox : Fin n → IntervalRat := fun i => IntervalRat.singleton (center i)
  fun i j => roundRat precisionBits (intervalJacobian F pointBox cfg i j).midpoint

private def rationalMatVec {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (vector : Fin n → ℚ) : Fin n → ℚ :=
  fun i => ∑ j, matrix i j * vector j

private def refinedCenter {n : Nat} (F : Fin n → Expr) (center : Fin n → ℚ)
    (preconditioner : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (precisionBits : Nat) : Fin n → ℚ :=
  let residual : Fin n → ℚ := fun i => (pointEvalIntervals F center cfg i).midpoint
  let correction := rationalMatVec preconditioner residual
  fun i => roundRat precisionBits (center i - correction i)

private def matrixRows {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ) :
    List (List ℚ) :=
  List.ofFn fun i => List.ofFn fun j => matrix i j

private def contractionFor {n : Nat} (F : Fin n → Expr)
    (X : Fin n → IntervalRat) (preconditioner : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig) : ℚ :=
  intervalMatrixBound (preconditionedJacobian preconditioner (intervalJacobian F X cfg))

private def reportFailure {n : Nat} (failure : AutomaticKrawczykFailure)
    (attempts refinements : Nat) (center : Fin n → ℚ)
    (preconditioner : Option (Matrix (Fin n) (Fin n) ℚ) := none)
    (contraction : ℚ := 0) : AutomaticKrawczykReport := {
  dimension := n
  attempts
  refinements
  center := List.ofFn center
  preconditioner := preconditioner.map matrixRows |>.getD []
  contractionBound := contraction
  failure := some failure
}

private partial def automaticKrawczykLoop {n : Nat} (F : Fin n → Expr)
    (X : Fin n → IntervalRat) (cfg : EvalConfig) (maximum precisionBits attempt : Nat)
    (center : Fin n → ℚ) : AutomaticKrawczykReport :=
  let attemptNumber := attempt + 1
  let jacobian := pointJacobianMidpoint F center cfg precisionBits
  match invertRatMatrix? jacobian with
  | none => reportFailure (.singularPointJacobian attemptNumber)
      attemptNumber attempt center
  | some rawPreconditioner =>
      let preconditioner := roundMatrix precisionBits rawPreconditioner
      if decide (preconditioner.det = 0) then
        reportFailure (.singularPointJacobian attemptNumber)
          attemptNumber attempt center (some preconditioner)
      else
       let cert : KrawczykCert n := { center, preconditioner }
       let contraction := contractionFor F X preconditioner cfg
       if krawczykCheck F X cert cfg then
        {
          dimension := n
          attempts := attemptNumber
          refinements := attempt
          center := List.ofFn center
          preconditioner := matrixRows preconditioner
          contractionBound := contraction
        }
       else if attemptNumber >= maximum then
        reportFailure (.exhausted attemptNumber) attemptNumber attempt center
          (some preconditioner) contraction
       else
        let next := refinedCenter F center preconditioner cfg precisionBits
        if !decide (centerInside X next) then
          reportFailure (.centerEscaped attemptNumber) attemptNumber attempt center
            (some preconditioner) contraction
        else if decide (next = center) then
          reportFailure (.stagnated attemptNumber) attemptNumber attempt center
            (some preconditioner) contraction
        else
          automaticKrawczykLoop F X cfg maximum precisionBits attemptNumber next

/-- Generate a dimension-erased automatic candidate report.  On success its
center and preconditioner can be reconstructed with `KrawczykCert.ofLists` and
must then be submitted to `krawczykCheck`. -/
def generateAutomaticKrawczyk {n : Nat} (F : Fin n → Expr)
    (X : Fin n → IntervalRat) (cfg : EvalConfig := {})
    (search : AutomaticKrawczykConfig := {}) : AutomaticKrawczykReport :=
  if n == 0 then
    { dimension := n, failure := some .invalidDimension }
  else if n > search.maxDimension then
    { dimension := n, failure := some (.dimensionLimit n search.maxDimension) }
  else if search.maxIterations == 0 then
    { dimension := n, failure := some (.exhausted 0) }
  else if !(decide (∀ i, (F i).checkADSupported = true)) then
    { dimension := n, failure := some .unsupportedAD }
  else
    let center : Fin n → ℚ := fun i => (X i).midpoint
    automaticKrawczykLoop F X cfg search.maxIterations search.precisionBits 0 center

end LeanCert.Engine
