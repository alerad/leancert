# Model Distillation Verification

LeanCert can certify that a student network differs from a teacher network by
at most a rational tolerance on a specified interval box.

## Certified statement

For every real input represented by the certified box, the theorem bounds each
corresponding output coordinate:

\[
\left|T(x)_i-S(x)_i\right| \leq \varepsilon.
\]

This is a guarantee for every input in that box, not for inputs outside the
declared domain.

## API shape

```lean
import LeanCert.ML.Distillation

open LeanCert.ML
open LeanCert.ML.Distillation

#check SequentialNet
#check checkEquivalence
#check verify_equivalence
```

`checkEquivalence teacher student domain eps prec` is the executable Boolean
certificate. `verify_equivalence` is its Golden Theorem. Applying it also
requires:

- a concrete real input;
- nonpositive Dyadic precision;
- well-formedness proofs for both networks;
- equality between the input and box dimensions;
- componentwise membership of the input in the box; and
- a proof that `checkEquivalence ... = true`.

The complete compiled example is
`LeanCert/Examples/ML/Distillation.lean`. Its final application has the
following shape:

```lean
exact verify_equivalence teacherNet studentNet inputDomain epsilon (-53)
  [x, y] (by norm_num) teacherNet_wf studentNet_wf
  hdom hmem distillationCheck_passes
```

Use exact rational tolerances such as `(1 : ℚ) / 100`, rather than treating a
decimal presentation as part of the API.

## How the checker works

The current checker:

1. propagates the input box through the teacher;
2. propagates the same box through the student;
3. subtracts the two output interval vectors; and
4. checks that every difference interval lies in `[-eps, eps]`.

Because the two networks are enclosed independently before subtraction, the
current implementation does not preserve cross-network correlations or perform
symbolic cancellation between shared teacher and student computations. This
can make its bound conservative.

## Workflow

1. Define each network as a `SequentialNet`.
2. Prove that the layer dimensions are well formed.
3. Define an `IntervalVector` input box and a rational tolerance.
4. prove `checkEquivalence ... = true`, normally by computation.
5. Apply `verify_equivalence` to obtain the semantic bound for an arbitrary
   input satisfying the box-membership hypotheses.

## Limitations

- Wide boxes and deep networks can produce inconclusive interval bounds.
- Teacher and student output dimensions must agree.
- The theorem bounds corresponding output coordinates; it does not claim
  structural or parameter equality.
- The current checker does not exploit correlations between the two networks.

## Files

| File | Description |
|---|---|
| `LeanCert/ML/Distillation.lean` | Checker, sequential-network infrastructure, and Golden Theorem |
| `LeanCert/Examples/ML/Distillation.lean` | Complete compiled application |
