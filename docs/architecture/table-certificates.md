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
TableCert.verify :
  (∀ row, checker row = true → Claim row) →
  T.checkAll checker = true →
  ∀ row, row ∈ T.rows.toList → Claim row
```

This supports the standard workflow:

```lean
def rows : Array Row := #[...]
def table : TableCert Row := { rows := rows }

theorem all_rows_valid :
    ∀ row, row ∈ table.rows.toList → RowValid row :=
  TableCert.verify table row_checker_sound (by native_decide)
```

## Linked Rows

Large numerical tables often need "next row" data. LeanCert should not ask the
kernel to discover a successor by searching a finite set or evaluating an
`sInf`. The oracle should provide the successor witness, and Lean should verify
local adjacency:

```lean
checkLinkedRows rows key nextKey eqKey = true
```

Its theorem proves:

```lean
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
imports. CI runs `scripts/check_no_sorry.py` over the production LeanCert
directories, and the same script can be run repo-wide while cleaning legacy
prototype examples.
