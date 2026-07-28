# Table Certificates

LeanCert's table certificate layer is for data-driven verification: many rows,
one checker, one soundness theorem.

The goal is not to encode a specific PNT or BKLNW table in LeanCert. The goal is
to make project-level tables natural to verify by providing generic finite-table
infrastructure.

## Design

Projects provide:

- a row type;
- generated row data;
- a boolean row checker;
- a theorem that a successful row check implies the desired row claim.

LeanCert provides:

- `TableCert`, a wrapper around `Array Row`;
- `TableCert.checkAll`, a linear row-wise checker;
- `TableCert.verify`, the generic table soundness theorem;
- adjacent-row checkers for explicit successor witnesses;
- failure-index reporting for audit output.

The core theorem is:

```lean
#check LeanCert.Engine.TableCert.verify
```
This supports the standard workflow:

```lean
def smallTable : LeanCert.Engine.TableCert Nat := { rows := #[0, 2, 4] }

example : ∀ row, row ∈ smallTable.rows.toList → row ≤ 4 := by
  exact LeanCert.Engine.TableCert.verify
    (Claim := fun row => row ≤ 4)
    (checker := fun row => decide (row ≤ 4))
    smallTable
    (by intro row checked; exact of_decide_eq_true checked)
    (by native_decide)
```
## Linked Rows

Large numerical tables often need "next row" data. LeanCert should not ask the
kernel to discover a successor by searching a finite set or evaluating an
`sInf`. The oracle should provide the successor witness, and Lean should verify
local adjacency:

```text
checkLinkedRows rows key nextKey eqKey = true
```
Its theorem proves:

```text
AdjacentAll (fun current following => nextKey current = key following) rows.toList
```
The executable checker performs a single linear pass over adjacent pairs.

## Audit Data

`TableCert.failingIndices` returns the row indices that fail a checker. This is
diagnostic output only; the trusted proof path remains the boolean checker plus
the soundness theorem.

## Trust Boundary

Search scripts and data generators are untrusted oracles. They may generate row
values, margins, successor witnesses, or precision choices. Their output becomes
trusted only when checked by LeanCert's verified checkers.

Checked-in Lean source should not contain proof placeholders in production
imports. The CI soundness guard checks production LeanCert directories and
keeps legacy prototype examples out of production import paths.
