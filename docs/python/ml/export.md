# Exporting Network Definitions to Lean

Network classes can emit Lean source definitions after rationalizing Python or
PyTorch parameters.

!!! info "Capability status"
    **Stability:** Model-dependent · **Authority:** Untrusted source generation
    until compiled and connected to a theorem · **Standalone replay:** Not by
    `export_lean()` alone

```python
from pathlib import Path

lean_source = network.export_lean("ControllerNet")
Path("ControllerNet.lean").write_text(lean_source, encoding="utf-8")
```

`TwoLayerReLUNetwork`, `SequentialNetwork`, and selected Transformer structures
provide `export_lean()` methods. `float_to_rational()` and conversion helpers
approximate floating parameters with bounded-denominator rationals.

Record the source model digest and framework version, layer ordering,
rationalization policy, generated-source digest, and LeanCert/Bridge revisions
used for later checks.

Generated definitions are inputs to Lean development, not proof that the
rational model matches the original floating runtime or that a property holds.
Compile the source, state the intended theorem, and use checked operations or
Lean proofs for authority.

This differs from `Verified.export_lean_project()`: that method packages a
specific semantic claim and fixed replay certificate for independent kernel
verification.
