# QProduct Certificates

`LeanCert.QProduct` certifies finite product-integral invariants of the form

```text
F S = ∫ u in (0 : ℝ)..1, ∏ n ∈ S, (1 - u ^ n)
```
for finite exponent sets `S : Finset Nat`.  The finite checker does not perform
numerical integration. It expands the product into a signed subset-sum
polynomial and integrates each monomial exactly over `[0, 1]`.

## Import

```lean
import LeanCert.QProduct
```

or, for examples:

```lean
import LeanCert.Examples.QProduct.Basic
import LeanCert.Examples.QProduct.PrimeLambda
```

## Finite Product Integrals

The core definitions are:

```text
qProd (S : Finset Nat) (u : ℝ)
F (S : Finset Nat)
finiteIntegralRat (S : Finset Nat)
```
The theorem `finiteIntegralRat_correct` connects the computable rational value
to the semantic real integral:

```lean
#check finiteIntegralRat_correct
```
For example, the exact integral for `{2, 3}` is `7 / 12`:

```lean
import LeanCert.QProduct

open LeanCert.QProduct

example : finiteIntegralRat ({2, 3} : Finset Nat) = 7 / 12 := by
  native_decide

example : F ({2, 3} : Finset Nat) = ((7 / 12 : ℚ) : ℝ) := by
  rw [← finiteIntegralRat_correct]
  have h : finiteIntegralRat ({2, 3} : Finset Nat) = 7 / 12 := by
    native_decide
  exact_mod_cast h
```

## Finite Golden Theorems

The finite certificate API follows the usual LeanCert pattern:

```text
checkFiniteIntegralInterval
verify_finiteIntegral_interval
checkFiniteIntegralUpper
verify_finiteIntegral_upper
checkFiniteIntegralLower
verify_finiteIntegral_lower
```
The checker is boolean and exact over `ℚ`; the verifier lifts a successful
check to a real statement about the integral.

```lean
example :
    ((7 / 12 : ℚ) : ℝ) ≤ F ({2, 3} : Finset Nat) ∧
      F ({2, 3} : Finset Nat) ≤ ((7 / 12 : ℚ) : ℝ) := by
  exact verify_finiteIntegral_interval ({2, 3} : Finset Nat)
    (7 / 12) (7 / 12) (by native_decide)
```

## Moments

`momentRat` and `moment` certify weighted integrals:

```text
moment S k = ∫ u in (0 : ℝ)..1, qProd S u * u ^ k
```
The bridge theorem is:

```lean
#check momentRat_correct
```
## Stability Lemmas

`LeanCert.QProduct.Stability` proves the elementary finite inequalities used by
tail certificates:

```text
qProd_nonneg
qProd_le_one
F_nonneg
F_le_one
F_antitone
qProd_sub_le_commonPrefix_sum
odd_tail_telescope_bound
odd_tail_sum_le_geom
```
These are not boolean checkers. They are reusable analytic lemmas for building
certificates from finite truncations and explicit tail estimates.

## Prime-Indexed Limit

`LeanCert.QProduct.PrimeLambda` defines prime truncations and the directed
prime limit:

```text
primesLE (N : Nat)
primeFRat (N : Nat)
primeLambda
```
The upper side is a standard checker-to-theorem bridge:

```lean
#check verify_primeLambda_upper
```
For example:

```lean
example : primeLambda ≤ ((133 / 240 : ℚ) : ℝ) := by
  exact verify_primeLambda_upper 7 (133 / 240) (by native_decide)
```

The lower side of a prime interval needs mathematical tail control.  The helper
`primeLambda_lower_of_forall` says that any rational lower bound valid for all
finite prime truncations is also valid for the directed limit:

```lean
#check primeLambda_lower_of_forall
```
The reusable odd-prime tail theorem is `primeLambda_sandwich`:

```lean
#check primeLambda_sandwich
```
The rational endpoint form is `primeLambda_rational_sandwich`, where
`primeSandwichLowerRat N m = primeFRat N - primeSandwichErrorRat N m`.

The module includes the elementary odd-tail certificate:

```lean
#check primeSandwichLowerRat_three_five
```
So the qualitative bound is available directly:

```lean
example : (1 : ℝ) / 2 < primeLambda := by
  exact primeLambda_gt_half
```

## Current Scope

The implemented framework certifies:

- exact finite q-product integrals by rational arithmetic;
- exact finite monomial moments;
- finite interval, upper, and lower certificates;
- positivity, boundedness, antitonicity, and common-prefix tail bounds;
- prime truncation upper certificates;
- reusable odd-prime tail sandwich certificates;
- the formal lower bound `19 / 36 ≤ primeLambda`, hence `1 / 2 < primeLambda`.

High-precision prime-limit sandwiches and eta-function closed-form benchmarks
fit the same API shape, but are not part of this initial module.
