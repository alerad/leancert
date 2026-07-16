/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.ANT.Asymp.Checkers
import LeanCert.Engine.Table

/-!
# PNT-facing inequality certificates

This module packages the existing dyadic slab checker into small certificate
objects intended for explicit PNT-style inequalities and generated numerical
tables.  The trusted core remains the checker soundness theorem in
`LeanCert.ANT.Asymp.Checkers`; this file only gives the standard user-facing
shape.
-/

namespace LeanCert.ANT.Asymp

open LeanCert.Core
open LeanCert.Engine

/-- Certificate that `lhs ≤ rhs` on every rational slab in `slabs`. -/
structure SlabInequalityCert where
  lhs : Expr
  rhs : Expr
  slabs : List IntervalRat
  prec : Int
  depth : Nat
  prec_ok : prec ≤ 0
  checked : checkExprLeOnSlabsDyadic lhs rhs slabs prec depth = true

namespace SlabInequalityCert

/-- Soundness of a packaged slab inequality certificate. -/
theorem verify (C : SlabInequalityCert) :
    ∀ I ∈ C.slabs, ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      Expr.eval (fun _ => x) C.lhs ≤ Expr.eval (fun _ => x) C.rhs :=
  verify_expr_le_on_slabs_dyadic C.lhs C.rhs C.slabs C.prec C.depth
    C.prec_ok C.checked

end SlabInequalityCert

/--
One generated table row for a closed interval inequality.

Rows are intentionally proof-free data.  The table certificate below carries
the precision hypotheses needed to use the dyadic checker.
-/
structure InequalityTableRow where
  lhs : Expr
  rhs : Expr
  interval : IntervalRat
  prec : Int
  depth : Nat
  deriving Repr

/-- Boolean checker for one inequality table row. -/
def checkInequalityTableRow (row : InequalityTableRow) : Bool :=
  checkExprLeOnIntervalDyadic row.lhs row.rhs row.interval row.prec row.depth

/--
Generated table certificate for row-wise interval inequalities.

This is the PNT/table-oriented specialization of `TableCert`: data rows are
checked by `native_decide`, while support/precision side conditions are proved
once over table membership.
-/
structure InequalityTableCert where
  table : TableCert InequalityTableRow
  prec_ok :
    ∀ row, row ∈ table.rows.toList → row.prec ≤ 0
  checked : table.checkAll checkInequalityTableRow = true

namespace InequalityTableCert

/-- Soundness of a generated inequality table certificate. -/
theorem verify (C : InequalityTableCert) :
    ∀ row, row ∈ C.table.rows.toList →
      ∀ x ∈ Set.Icc (row.interval.lo : ℝ) row.interval.hi,
        Expr.eval (fun _ => x) row.lhs ≤ Expr.eval (fun _ => x) row.rhs := by
  intro row hrow x hx
  have hchecked :
      checkInequalityTableRow row = true :=
    TableCert.row_checked_of_list_all C.checked hrow
  exact verify_expr_le_on_interval_dyadic row.lhs row.rhs row.interval row.prec row.depth
    (C.prec_ok row hrow) hchecked x hx

/-- Diagnostic list of failing row indices for a generated inequality table. -/
def failingIndices (C : InequalityTableCert) : List Nat :=
  C.table.failingIndices checkInequalityTableRow

end InequalityTableCert

end LeanCert.ANT.Asymp
