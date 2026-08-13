# Quantifier and Witness Synthesis

The experimental synthesizer reduces structured goals to optimization, bound,
root, or derivative operations and proposes witnesses.

!!! warning "Authority boundary"
    **Stability:** Experimental · **Authority:** Mixed search and checked
    numerical subclaims · **Standalone replay:** No for generated `lean_proof`

```python
import leancert as lc

x = lc.var("x")
with lc.Solver() as solver:
    result = lc.synthesize_bound(
        solver,
        x * x,
        {"x": (-1, 1)},
        abs_bound=True,
    )

if result.success:
    witness = result.witnesses[0]
    print(witness.variable, witness.value, witness.rigorous_bounds)
```

Convenience functions include `synthesize_bound`, `synthesize_minimum`,
`synthesize_maximum`, `prove_sign`, and `prove_limit`. `QuantifierResult`
exposes `pattern`, `success`, `witnesses`, `message`, an optional legacy
certificate, and optional generated `lean_proof` text.

The name `prove_limit` is historical: its workflow searches and checks selected
numeric obligations, and generated proof text is not automatically compiled.
A finite set of epsilon checks is not a theorem quantified over every positive
epsilon. Treat the result as synthesis output until a concrete theorem is
independently accepted by Lean.

The direct `Solver.synthesize_min_witness`, `synthesize_max_witness`, and
`synthesize_root_witness` methods expose lower-level candidate results. Keep
candidate coordinates separate from rigorous value enclosures in reports.
