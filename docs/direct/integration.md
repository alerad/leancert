# Integration

For ordinary definite-integral equalities and inequalities, start with
[`leancert`](leancert.md). Use this page for the supported routes and
lower-level certificate APIs.

Typical goals:

```text
∫ x in a..b, f x ∈ B
lo ≤ ∫ x in a..b, f x
∫ x in a..b, f x ≤ hi
```
Primary workflow:

```text
leancert
leancert?
```

Advanced and programmatic controls:

```text
integral_exact
integrateInterval
integrateUniform
```
For ordinary mathematical syntax, start with `leancert`:

```lean
import LeanCert.Tactic

open MeasureTheory

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert

example : (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  leancert
```

The exact path recognizes rational polynomials, computes their antiderivative
with `QPoly`, and checks the endpoint result using exact rational arithmetic.
For supported non-polynomial inequalities, the router uses the existing
certified Rational partition search. Search retains the first successful
partition count, attempt count, and enclosure; verification then checks that
fixed partition candidate rather than rerunning the search procedure.
Search exhaustion, domain obstruction, certificate rejection, and
infrastructure failure are distinct typed outcomes, and failed routes restore
the complete tactic state. Exact rational arithmetic and partition
search describe computation strategies; they are not certificate-verification
routes. Exact transcendental equalities are intentionally not inferred from an
interval enclosure.

For programmatic checked integration, `integrateUniform` provides one result
boundary for the existing Rational and Dyadic partition engines:

```lean
import LeanCert

open LeanCert LeanCert.Core

def unit : IntervalRat := ⟨0, 1, by norm_num⟩

#eval integrateUniform (.exp (.var 0)) unit 32
#eval integrateUniform (.exp (.var 0)) unit 32 { backend := .dyadic }
```

The successful `IntegralOutcome` contains a Rational enclosure, partition
count, requested backend, and selected backend. `integrateUniform_correct`
lifts either backend's retained checked computation to membership of the real
integral. Automatic selection remains Rational while the benchmark suite is
used to establish where Dyadic integration is consistently preferable; an
explicit Dyadic request is already fully checked.

For lower-level Taylor-model generated integral certificates, see
[Proof Templates → ConstantFactory](../proof-templates/constant-factory.md) and the
Taylor integration notes there.
