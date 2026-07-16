/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.Global

/-!
# Counter-Example Search

This file provides machinery for finding counter-examples to bound claims.
Finding a counter-example is just global optimization: to disprove `f(x) ≤ C`,
we maximize `f(x)` and check if the result exceeds `C`.

## Main definitions

* `CounterExample` - A concretely checked point that violates a bound
* `findViolation` - Search for counter-examples to `f(x) ≤ limit`
* `findViolationLower` - Search for counter-examples to `limit ≤ f(x)`

## Counter-Example Types

* **Certified point**: checked singleton evaluation places the complete output
  enclosure in the violating region.

Overlap between an optimizer enclosure and the violating region is deliberately
not returned as a counter-example.  The reported midpoint is re-evaluated on a
singleton box with the checked Rational evaluator before it is exposed.

## Usage

```lean
-- Check if x² ≤ 3 on [-2, 2]
let result := findViolation (Expr.mul (Expr.var 0) (Expr.var 0)) [⟨-2, 2, by norm_num⟩] 3
-- Returns a checked concrete witness near x = -2 or x = 2.
```
-/

namespace LeanCert.Engine.Search

open LeanCert.Core
open LeanCert.Engine.Optimization

/-! ### Counter-example types -/

/-- A counter-example to a bound claim -/
structure CounterExample where
  /-- The input point (midpoint of the best box) -/
  point : List ℚ
  /-- The checked output interval at the singleton point -/
  valueLo : ℚ
  valueHi : ℚ
  /-- The box containing the counter-example -/
  box : Box
  /-- Number of iterations used -/
  iterations : Nat
  deriving Repr

namespace CounterExample

/-- Get the midpoint of each interval in the box -/
def boxMidpoint (B : Box) : List ℚ :=
  B.map (·.midpoint)

/-- The singleton box corresponding to `boxMidpoint`. -/
def midpointBox (B : Box) : Box :=
  B.map (fun I => IntervalRat.singleton I.midpoint)

/-- Construct an upper-bound counter-example only when checked point evaluation
proves that the concrete midpoint violates `f(x) ≤ limit`. -/
def checkedUpper? (e : Expr) (B : Box) (limit : ℚ) (iterations : Nat) :
    EvalResult (Option CounterExample) := do
  let value ← evalOnBoxRationalChecked e (midpointBox B)
  if value.lo > limit then
    return some {
      point := boxMidpoint B
      valueLo := value.lo
      valueHi := value.hi
      box := B
      iterations
    }
  return none

/-- Construct a lower-bound counter-example only when checked point evaluation
proves that the concrete midpoint violates `limit ≤ f(x)`. -/
def checkedLower? (e : Expr) (B : Box) (limit : ℚ) (iterations : Nat) :
    EvalResult (Option CounterExample) := do
  let value ← evalOnBoxRationalChecked e (midpointBox B)
  if value.hi < limit then
    return some {
      point := boxMidpoint B
      valueLo := value.lo
      valueHi := value.hi
      box := B
      iterations
    }
  return none

/-- Strict upper-bound counterpart of `checkedUpper?`. -/
def checkedStrictUpper? (e : Expr) (B : Box) (limit : ℚ) (iterations : Nat) :
    EvalResult (Option CounterExample) := do
  let value ← evalOnBoxRationalChecked e (midpointBox B)
  if value.lo ≥ limit then
    return some {
      point := boxMidpoint B
      valueLo := value.lo
      valueHi := value.hi
      box := B
      iterations
    }
  return none

/-- Strict lower-bound counterpart of `checkedLower?`. -/
def checkedStrictLower? (e : Expr) (B : Box) (limit : ℚ) (iterations : Nat) :
    EvalResult (Option CounterExample) := do
  let value ← evalOnBoxRationalChecked e (midpointBox B)
  if value.hi ≤ limit then
    return some {
      point := boxMidpoint B
      valueLo := value.lo
      valueHi := value.hi
      box := B
      iterations
    }
  return none

end CounterExample

/-! ### Upper bound violation (f(x) ≤ limit) -/

/--
Search for a counter-example to the claim `∀ x ∈ domain, f(x) ≤ limit`.

Returns a counter-example only when checked evaluation proves that the concrete
midpoint of the optimizer's best box violates the bound.  `none` means that no
concrete witness was certified; it does not prove the bound.

**Algorithm**: maximize `f`, then checked-evaluate the midpoint of the best box.
An optimizer overlap alone never produces a result.
-/
def findViolation (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : EvalResult (Option CounterExample) := do
  -- Maximize f to find the highest value
  let result := globalMaximizeCore e domain cfg

  let max_lo := result.bound.lo
  let best_box := result.bound.bestBox

  if max_lo > limit then
    CounterExample.checkedUpper? e best_box limit result.bound.iterations
  else
    return none

/--
Variant of `findViolation` with division support.
-/
def findViolationDiv (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : EvalResult (Option CounterExample) := do
  let result ← globalMaximizeRationalChecked e domain cfg

  let max_lo := result.bound.lo
  let best_box := result.bound.bestBox

  if max_lo > limit then
    CounterExample.checkedUpper? e best_box limit result.bound.iterations
  else
    return none

/-! ### Lower bound violation (limit ≤ f(x)) -/

/--
Search for a counter-example to the claim `∀ x ∈ domain, limit ≤ f(x)`.

Returns a result only when the checked midpoint enclosure lies below `limit`.
`none` means no concrete witness was certified.

**Algorithm**: Minimize `f(x)` over the domain. If `min(f).hi < limit`,
the bound is definitely false.
-/
def findViolationLower (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : EvalResult (Option CounterExample) := do
  -- Minimize f to find the lowest value
  let result := globalMinimizeCore e domain cfg

  let min_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if min_hi < limit then
    CounterExample.checkedLower? e best_box limit result.bound.iterations
  else
    return none

/--
Variant with division support.
-/
def findViolationLowerDiv (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : EvalResult (Option CounterExample) := do
  let result ← globalMinimizeRationalChecked e domain cfg

  let min_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if min_hi < limit then
    CounterExample.checkedLower? e best_box limit result.bound.iterations
  else
    return none

/-! ### Strict bound violations -/

/--
Search for a counter-example to `∀ x ∈ domain, f(x) < limit`.
A violation means `f(x) ≥ limit` for some `x`.
-/
def findViolationStrict (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : EvalResult (Option CounterExample) := do
  let result := globalMaximizeCore e domain cfg

  let max_lo := result.bound.lo
  let best_box := result.bound.bestBox

  -- For strict inequality, we need max(f) ≥ limit (not just >)
  if max_lo ≥ limit then
    CounterExample.checkedStrictUpper? e best_box limit result.bound.iterations
  else
    return none

/--
Search for a counter-example to `∀ x ∈ domain, limit < f(x)`.
A violation means `f(x) ≤ limit` for some `x`.
-/
def findViolationStrictLower (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : EvalResult (Option CounterExample) := do
  let result := globalMinimizeCore e domain cfg

  let min_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if min_hi ≤ limit then
    CounterExample.checkedStrictLower? e best_box limit result.bound.iterations
  else
    return none

/-! ### Pretty printing -/

/-- Format a counter-example for display -/
def CounterExample.format (ce : CounterExample) (limit : ℚ) : String :=
  let pointStr := ce.point.map toString |>.intersperse ", " |> String.join
  let intervalStr := s!"[{ce.valueLo}, {ce.valueHi}]"
  s!"Certified counter-example:\n\
     • Point: ({pointStr})\n\
     • Value: {intervalStr}\n\
     • Limit: {limit}\n\
     • Iterations: {ce.iterations}"

end LeanCert.Engine.Search
