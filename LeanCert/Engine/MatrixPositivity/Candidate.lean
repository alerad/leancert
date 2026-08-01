/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.MatrixPositivity.Certificate

/-!
# Untrusted exact LDLᵀ discovery

The algorithm in this file is candidate-generation machinery only. It uses
exact rational arithmetic, but its output remains untrusted until accepted by
`matrixPSDCheck` or `matrixPosDefCheck`.
-/

namespace LeanCert.Engine

/-- Which semantic property automatic discovery is trying to establish. -/
inductive MatrixPositivityKind where
  | posSemidef
  | posDef
  deriving Repr, Inhabited, DecidableEq

/-- Conservative limits for exact rational LDLᵀ discovery. -/
structure AutomaticMatrixPositivityConfig where
  maxDimension : Nat := 8
  deriving Repr, Inhabited

/-- Stable failure classes for candidate generation. -/
inductive AutomaticMatrixPositivityFailure where
  | dimensionLimit (actual limit : Nat)
  | zeroPivotObstruction (pivot row : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- Dimension-erased telemetry retained from the single discovery pass. -/
structure AutomaticMatrixPositivityReport where
  dimension : Nat
  positivePivots : Nat := 0
  zeroPivots : Nat := 0
  negativePivots : Nat := 0
  diagonal : List ℚ := []
  lower : List (List ℚ) := []
  failure : Option AutomaticMatrixPositivityFailure := none
  deriving Repr, Inhabited

/-- A retained typed candidate together with its dimension-erased report. -/
structure AutomaticMatrixPositivityResult (n : Nat) where
  certificate : Option (LDLTCertificate n)
  report : AutomaticMatrixPositivityReport

private def matrixGet (rows : Array (Array ℚ)) (i j : Nat) : ℚ :=
  ((rows[i]?).bind fun row => row[j]?).getD 0

private def matrixSet (rows : Array (Array ℚ)) (i j : Nat) (value : ℚ) :
    Array (Array ℚ) :=
  match rows[i]? with
  | none => rows
  | some row => rows.set! i (row.set! j value)

private def identityRows (n : Nat) : Array (Array ℚ) :=
  Array.ofFn fun i : Fin n =>
    Array.ofFn fun j : Fin n => if i = j then 1 else 0

private def sourceRows {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ) :
    Array (Array ℚ) :=
  Array.ofFn fun i : Fin n => Array.ofFn fun j : Fin n => matrix i j

private def previousContribution (lower : Array (Array ℚ)) (diagonal : Array ℚ)
    (row column pivot : Nat) : ℚ :=
  (List.range pivot).foldl (fun total j =>
    total + matrixGet lower row j * (diagonal[j]?).getD 0 * matrixGet lower column j) 0

private structure LDLTState where
  lower : Array (Array ℚ)
  diagonal : Array ℚ
  positivePivots : Nat := 0
  zeroPivots : Nat := 0
  negativePivots : Nat := 0

private def classifyPivot (state : LDLTState) (pivot : ℚ) : LDLTState :=
  if 0 < pivot then
    { state with positivePivots := state.positivePivots + 1 }
  else if pivot = 0 then
    { state with zeroPivots := state.zeroPivots + 1 }
  else
    { state with negativePivots := state.negativePivots + 1 }

private def fillPivotColumn (source : Array (Array ℚ)) (size pivot : Nat)
    (state : LDLTState) (pivotValue : ℚ) :
    Except AutomaticMatrixPositivityFailure LDLTState :=
  (List.range (size - (pivot + 1))).foldlM (fun current offset =>
    let row := pivot + 1 + offset
    let residual := matrixGet source row pivot -
      previousContribution current.lower current.diagonal row pivot pivot
    if pivotValue = 0 then
      if residual = 0 then pure current
      else throw (.zeroPivotObstruction pivot row)
    else
      pure { current with
        lower := matrixSet current.lower row pivot (residual / pivotValue) }) state

private partial def ldltLoop (source : Array (Array ℚ)) (size pivot : Nat)
    (state : LDLTState) : Except AutomaticMatrixPositivityFailure LDLTState :=
  if pivot < size then
    let pivotValue := matrixGet source pivot pivot -
      previousContribution state.lower state.diagonal pivot pivot pivot
    let state := classifyPivot
      { state with diagonal := state.diagonal.set! pivot pivotValue } pivotValue
    match fillPivotColumn source size pivot state pivotValue with
    | .error failure => .error failure
    | .ok next => ldltLoop source size (pivot + 1) next
  else
    .ok state

private def rowsToMatrix {n : Nat} (rows : Array (Array ℚ)) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => matrixGet rows i.val j.val

private def arrayToVector {n : Nat} (values : Array ℚ) : Fin n → ℚ :=
  fun i => (values[i.val]?).getD 0

private def matrixRows {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ) :
    List (List ℚ) :=
  List.ofFn fun i => List.ofFn fun j => matrix i j

/-- Reconstruct a typed certificate from dimension-erased telemetry. Missing
entries are interpreted as zero; the independent checker rejects malformed
data. -/
def LDLTCertificate.ofLists (n : Nat) (lower : List (List ℚ)) (diagonal : List ℚ) :
    LDLTCertificate n where
  lower i j := ((lower[i.val]?).bind fun row => row[j.val]?).getD 0
  diagonal i := (diagonal[i.val]?).getD 0

private def successfulResult {n : Nat} (state : LDLTState) :
    AutomaticMatrixPositivityResult n :=
  let certificate : LDLTCertificate n := {
    lower := rowsToMatrix state.lower
    diagonal := arrayToVector state.diagonal
  }
  {
    certificate := some certificate
    report := {
      dimension := n
      positivePivots := state.positivePivots
      zeroPivots := state.zeroPivots
      negativePivots := state.negativePivots
      diagonal := state.diagonal.toList
      lower := matrixRows certificate.lower
    }
  }

/-- Generate one exact rational LDLᵀ candidate. The checker is intentionally
not executed here, so tactic and router callers can retain and certify the
candidate without duplicate work. -/
def discoverMatrixPositivity {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (config : AutomaticMatrixPositivityConfig := {}) :
    AutomaticMatrixPositivityResult n :=
  if n > config.maxDimension then
    {
      certificate := none
      report := {
        dimension := n
        failure := some (.dimensionLimit n config.maxDimension)
      }
    }
  else
    let initial : LDLTState := {
      lower := identityRows n
      diagonal := Array.replicate n 0
    }
    match ldltLoop (sourceRows matrix) n 0 initial with
    | .ok state => successfulResult state
    | .error failure => {
        certificate := none
        report := { dimension := n, failure := some failure }
      }

end LeanCert.Engine
