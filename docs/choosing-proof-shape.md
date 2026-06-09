# Choosing A Proof Shape

Start from the theorem you want to prove, not from a module name.

## Direct Goals

Use direct automation when the target theorem is already a concrete numerical
claim:

```lean
∀ x ∈ I, f x ≤ c
∀ x ∈ I, f x ≠ 0
∃ x ∈ I, f x = 0
∃! x ∈ I, f x = 0
∃ M, ∀ x ∈ I, f x ≤ M
∫ x in a..b, f x ∈ B
```

Go to [Direct Automation](direct/bounds.md).

## Structured Certificate Goals

Use proof templates when the proof has repeatable structure:

```text
generated rows + row checker + row soundness = theorem for every row
main term + nonnegative error = envelope theorem
base kernels + perturbation algebra = many related constants
rectangle identities + vanishing + limits = contour shift
```

Go to [Proof Templates](proof-templates/overview.md).

## Domain Goals

Use domain libraries when the theorem is naturally about a mathematical domain:

- Chebyshev `ψ`/`θ`;
- Abel summation and finite ANT transforms;
- Euler/log products;
- Dirichlet and Mertens sums;
- explicit-PNT transfer schemas;
- q-product prime-limit certificates.

Go to [Domain Libraries](domains/overview.md).

## Trust Questions

If the question is “why does this checker prove a theorem?” or “what is trusted
when data is generated externally?”, go to [Architecture and Trust](architecture/golden-theorems.md).
