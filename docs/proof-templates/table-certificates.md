# Table Certificates

Use table certificates when a theorem is proved row-by-row over generated finite
data:

```text
generated rows
+ row checker
+ row soundness theorem
= theorem for every row
```

Core API:

```text
TableCert
TableCert.checkAll
TableCert.verify
TableCert.failingIndices
```
For linked or sorted rows:

```text
checkLinkedRows
checkStrictlyIncreasingBy
AdjacentAll
```
`TableCert` is a generic trust pattern, not a domain-specific API.  Domain
projects provide the row type and row checker.  LeanCert provides the finite
row traversal and soundness theorem.

For numerical inequality rows, see:

```text
InequalityTableRow
InequalityTableCert
InequalityTableCert.verify
```
Architecture deep dive: [Table Certificates](../architecture/table-certificates.md).
