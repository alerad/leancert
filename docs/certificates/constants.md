# ConstantFactory Certificates

`LeanCert.ConstantFactory` certifies exact finite observer identities for
q-product constants.

## Import

```lean
import LeanCert.ConstantFactory
```

For approximate kernel banks, import:

```lean
import LeanCert.ConstantFactory.IntervalBank
```

or through the aggregate API:

```lean
import LeanCert
```

## Observer Sums

The base q-product moment is already provided by `LeanCert.QProduct`:

```lean
moment R m = ∫ u in (0 : ℝ)..1, qProd R u * u ^ m
momentRat R m
```

`ConstantFactory` adds a finite perturbation compiler. For a base set `R` and
a disjoint perturbation set `Q`, it computes:

```lean
observerIntegralRat R Q =
  ∑ A ∈ Q.powerset, subsetSign A * momentRat R (subsetWeight A)
```

The Golden Theorem is:

```lean
theorem observerIntegralRat_eq_F_union
    (R Q : Finset Nat) (hdisj : Disjoint R Q) :
    (observerIntegralRat R Q : ℝ) = F (R ∪ Q)
```

This is the finite observer identity:

\[
F_{R \cup Q}
=
\sum_{A \subseteq Q} (-1)^{|A|} K_R\!\left(\sum_{q \in A} q\right),
\]

where \(K_R(m)\) is the `m`th q-product moment of `R`.

## Boolean Certificates

The checker is exact rational arithmetic:

```lean
checkConstantFactoryInterval
checkConstantFactoryUpper
checkConstantFactoryLower
```

The public interval bridge is:

```lean
theorem verify_constantFactory_interval
    (R Q : Finset Nat) (lo hi : ℚ)
    (hcheck : checkConstantFactoryInterval R Q lo hi = true) :
    (lo : ℝ) ≤ F (R ∪ Q) ∧ F (R ∪ Q) ≤ (hi : ℝ)
```

The checker includes the disjointness condition, so a successful certificate
proves both the finite observer algebra side condition and the rational bound.

## Interval Kernel Banks

Exact rational moments are convenient for small finite products, but large
constant factories often need approximate or externally generated kernel
enclosures. `LeanCert.ConstantFactory.IntervalBank` provides that layer:

```lean
structure KernelIntervalBank (R : Finset Nat) where
  interval : Nat → IntervalRat
  correct : ∀ m, moment R m ∈ interval m
```

Given a certified bank for the base profile `R`, the interval observer sums the
signed perturbation terms:

```lean
observerInterval Q bank
```

The Golden Theorem is:

```lean
theorem F_union_mem_observerInterval
    {R Q : Finset Nat} (hdisj : Disjoint R Q)
    (bank : KernelIntervalBank R) :
    F (R ∪ Q) ∈ observerInterval Q bank
```

This is the interval analogue of the exact observer identity:

\[
K_R(m) \in I_m
\quad\Longrightarrow\quad
F_{R \cup Q}
\in
\sum_{A \subseteq Q} (-1)^{|A|}
I_{\sum_{q \in A} q}.
\]

The current implementation uses the existing powerset observer basis. A later
coefficient-compressed perturbation polynomial can reuse the same bank theorem
without changing the trust boundary.

There is also a degenerate exact bank:

```lean
exactKernelIntervalBank R
```

which wraps `momentRat R m` in singleton intervals.

## Taylor Integration Bridge

Taylor models can generate kernel enclosures. The first verified bridge lives at:

```lean
import LeanCert.Engine.TaylorModel.Integral
```

and exposes:

```lean
TaylorModel.integralBoundCoarse
TaylorModel.integral_mem_bound_coarse
```

If a Taylor model semantically encloses `f` on `tm.domain`, then
`integral_mem_bound_coarse` certifies the definite integral of `f` over that
domain using the global Taylor-model range bound. This is deliberately
conservative; exact polynomial-plus-remainder Taylor integration is the natural
next tightening layer.

## Example

```lean
import LeanCert.ConstantFactory.IntervalBank

open LeanCert.ConstantFactory
open LeanCert.QProduct

example :
    observerIntegralRat ({2} : Finset Nat) ({3} : Finset Nat) = 7 / 12 := by
  native_decide

example :
    ((7 / 12 : ℚ) : ℝ) ≤ F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ∧
      F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ≤ ((7 / 12 : ℚ) : ℝ) :=
  verify_constantFactory_interval ({2} : Finset Nat) ({3} : Finset Nat)
    (7 / 12) (7 / 12) (by native_decide)

example :
    F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ∈
      observerInterval ({3} : Finset Nat)
        (exactKernelIntervalBank ({2} : Finset Nat)) := by
  exact F_union_mem_observerInterval (by simp)
    (exactKernelIntervalBank ({2} : Finset Nat))
```

## Current Scope

The first implementation is finite and exact, with an approximate interval-bank
extension:

- finite perturbation observers;
- exact rational moment reuse from `QProduct`;
- exact interval, upper, and lower certificates;
- a semantic identity reducing `F (R ∪ Q)` to moments of `R`.
- interval kernel banks for approximate or externally generated moment
  enclosures;
- a coarse Taylor-model integral bridge for producing verified integral
  intervals.

Beta/Gamma kernels and infinite eta-product observer banks are natural later
extensions, but they are not part of this finite MVP.
