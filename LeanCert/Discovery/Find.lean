/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Discovery.Types
import LeanCert.Validity.Bounds
import LeanCert.Engine.Integrate
import LeanCert.Engine.RootFinding.Bisection

/-!
# Discovery Mode: Finder Functions

This module provides high-level "finder" functions that:
1. Run the appropriate algorithm (optimization, root finding, etc.)
2. Generate certificate parameters automatically
3. Assemble the proof term using the "Golden Theorems" from Certificate.lean

These functions produce proof-carrying results (`Verified*` types) that bundle
computed data with semantic proofs.

## Main Definitions

* `findGlobalMin` - Find and verify a global minimum
* `findGlobalMax` - Find and verify a global maximum
* `searchRoots` - Find root candidates (not formally verified)
* `quickBounds` - Quick interval evaluation

## Design

The finders work in two stages:
1. **Computation**: Run the raw algorithm (e.g., `globalMinimizeCore`)
2. **Certification**: Apply the corresponding Golden Theorem to get the proof

The proof is assembled by `native_decide` evaluating the boolean certificate checker.
-/

namespace LeanCert.Discovery

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization
open LeanCert.Validity

/-! ## Global Minimum Finding -/

/-- Find a verified global minimum of an expression over a box.

This function:
1. Runs `globalMinimizeCore` to compute the bound
2. Uses `globalMinimizeCore_lo_correct` to produce a proof

The returned `VerifiedGlobalMin` bundles:
- The computed lower bound
- The best box containing a near-minimizer
- A proof that the bound is valid for all points in the domain

**Usage**:
```lean
def result := findGlobalMin expr support domain cfg
-- result.bound is the minimum bound
-- result.is_lower_bound is the proof
```
-/
def findGlobalMin (expr : Expr) (hsupp : ExprSupported expr)
    (domain : Box) (cfg : DiscoveryConfig := {}) : VerifiedGlobalMin expr domain :=
  -- Run the optimization algorithm
  let optCfg := cfg.toGlobalOptConfig
  let result := globalMinimizeCore expr domain optCfg
  -- Extract bounds from result
  let lo := result.bound.lo
  let hi := result.bound.hi
  let bestBox := result.bound.bestBox
  let iters := result.bound.iterations
  -- Build the proof using the correctness theorem (with automatic domain validity)
  let hdom : ∀ (B' : Box), B'.length = domain.length → evalDomainValid expr B'.toEnv { taylorDepth := optCfg.taylorDepth } :=
    fun B' _ => ExprSupported.domainValid hsupp B'.toEnv { taylorDepth := optCfg.taylorDepth }
  let proof : ∀ (ρ : Nat → ℝ), Box.envMem ρ domain →
              (∀ i, i ≥ domain.length → ρ i = 0) →
              (lo : ℝ) ≤ Expr.eval ρ expr :=
    globalMinimizeCore_lo_correct expr hsupp.toCore domain optCfg hdom
  -- Assemble the result
  { bound := lo
    upperBound := hi
    minimizerBox := bestBox
    iterations := iters
    is_lower_bound := proof }

/-- Find a verified global maximum of an expression over a box.

Symmetric to `findGlobalMin`, using maximization instead.
-/
def findGlobalMax (expr : Expr) (hsupp : ExprSupported expr)
    (domain : Box) (cfg : DiscoveryConfig := {}) : VerifiedGlobalMax expr domain :=
  -- Run the optimization algorithm
  let optCfg := cfg.toGlobalOptConfig
  let result := globalMaximizeCore expr domain optCfg
  -- Extract bounds from result
  let hi := result.bound.hi
  let lo := result.bound.lo
  let bestBox := result.bound.bestBox
  let iters := result.bound.iterations
  -- Build the proof using the negation trick with domain validity
  let hsupp_neg : ExprSupportedCore (Expr.neg expr) := ExprSupportedCore.neg hsupp.toCore
  let hdom_neg : ∀ (B' : Box), B'.length = domain.length → evalDomainValid (Expr.neg expr) B'.toEnv { taylorDepth := optCfg.taylorDepth } :=
    fun B' _ => by simp only [evalDomainValid]; exact ExprSupported.domainValid hsupp B'.toEnv { taylorDepth := optCfg.taylorDepth }
  -- Direct proof: globalMaximizeCore negates and flips, so hi = -min(-e).lo
  let proof : ∀ (ρ : Nat → ℝ), Box.envMem ρ domain →
              (∀ i, i ≥ domain.length → ρ i = 0) →
              Expr.eval ρ expr ≤ (hi : ℝ) := fun ρ hρ hzero => by
    have hlo_neg := globalMinimizeCore_lo_correct (Expr.neg expr) hsupp_neg domain optCfg hdom_neg ρ hρ hzero
    simp only [Expr.eval_neg] at hlo_neg
    have h1 : Expr.eval ρ expr ≤ -((globalMinimizeCore (Expr.neg expr) domain optCfg).bound.lo : ℝ) := by
      linarith
    show Expr.eval ρ expr ≤ (hi : ℝ)
    have hhi : hi = -((globalMinimizeCore (Expr.neg expr) domain optCfg).bound.lo) := rfl
    rw [hhi]
    push_cast
    exact h1
  -- Assemble the result
  { bound := hi
    lowerBound := lo
    maximizerBox := bestBox
    iterations := iters
    is_upper_bound := proof }

/-! ## Bound Verification -/

/-- Verify an upper bound using interval arithmetic.

Returns `some proof` if the bound is verified, `none` otherwise.
-/
def verifyUpperBound (expr : Expr) (hsupp : ExprSupported expr)
    (domain : IntervalRat) (bound : ℚ) (cfg : DiscoveryConfig := {}) :
    Option (VerifiedUpperBound expr domain) :=
  let evalCfg := cfg.toEvalConfig
  if h : checkUpperBoundSmart expr domain bound evalCfg then
    some {
      bound := bound
      is_upper_bound := verify_upper_bound_smart expr hsupp domain bound evalCfg h
    }
  else
    none

/-- Verify a lower bound using interval arithmetic.

Returns `some proof` if the bound is verified, `none` otherwise.
-/
def verifyLowerBound (expr : Expr) (hsupp : ExprSupported expr)
    (domain : IntervalRat) (bound : ℚ) (cfg : DiscoveryConfig := {}) :
    Option (VerifiedLowerBound expr domain) :=
  let evalCfg := cfg.toEvalConfig
  if h : checkLowerBoundSmart expr domain bound evalCfg then
    some {
      bound := bound
      is_lower_bound := verify_lower_bound_smart expr hsupp domain bound evalCfg h
    }
  else
    none

/-! ## Root Finding -/

/-- Result of root search before certification -/
structure RootSearchResult (expr : Expr) where
  /-- Intervals that may contain roots -/
  intervals : List IntervalRat
  /-- Status for each interval -/
  statuses : List RootStatus
  /-- Iteration count -/
  iterations : Nat
  deriving Repr

/-- Find roots of an expression on an interval using bisection.

This searches for roots but doesn't provide formal proofs of existence.
The results indicate where roots may exist based on sign changes.

Note: For formal verification, use the sign change theorems from Certificate.lean
with the returned intervals that have `hasRoot` status.
-/
noncomputable def searchRoots (expr : Expr) (domain : IntervalRat)
    (cfg : DiscoveryConfig := {}) : RootSearchResult expr :=
  -- Use a positive tolerance (default is 1/1000)
  let tol : ℚ := if cfg.tolerance > 0 then cfg.tolerance else 1/1000
  -- Run bisection with proof that tolerance is positive
  let result := bisectRoot expr domain cfg.maxBisectionDepth tol (by
    unfold tol
    split_ifs with h
    · exact h
    · norm_num
  )
  let intervals := result.intervals.map Prod.fst
  let statuses := result.intervals.map Prod.snd
  { intervals := intervals
    statuses := statuses
    iterations := result.iterations }

/-! ## Convenience Functions -/

/-- Quick bounds check: returns `(lo, hi)` interval containing all values of expr on domain -/
def quickBounds (expr : Expr) (domain : IntervalRat)
    (cfg : DiscoveryConfig := {}) : ℚ × ℚ :=
  let result := evalIntervalCore1 expr domain cfg.toEvalConfig
  (result.lo, result.hi)

/-- Quick global bounds: returns `(min, max)` bounds using optimization -/
def quickGlobalBounds (expr : Expr) (hsupp : ExprSupported expr)
    (domain : Box) (cfg : DiscoveryConfig := {}) : ℚ × ℚ :=
  let minResult := findGlobalMin expr hsupp domain cfg
  let maxResult := findGlobalMax expr hsupp domain cfg
  (minResult.bound, maxResult.bound)

/-! ## Adaptive Verification

These functions automatically increase precision until verification succeeds.
-/

/-- Try to verify an upper bound with increasing Taylor depths.
Returns `some` with the verified bound if successful, `none` otherwise. -/
def tryVerifyUpperBound (expr : Expr) (hsupp : ExprSupported expr)
    (domain : IntervalRat) (bound : ℚ) (maxDepth : Nat := 40) :
    Option (VerifiedUpperBound expr domain) :=
  let depths := [10, 15, 20, 30, 40].filter (· ≤ maxDepth)
  depths.findSome? fun d =>
    let cfg : DiscoveryConfig := { taylorDepth := d }
    verifyUpperBound expr hsupp domain bound cfg

/-- Try to verify a lower bound with increasing Taylor depths.
Returns `some` with the verified bound if successful, `none` otherwise. -/
def tryVerifyLowerBound (expr : Expr) (hsupp : ExprSupported expr)
    (domain : IntervalRat) (bound : ℚ) (maxDepth : Nat := 40) :
    Option (VerifiedLowerBound expr domain) :=
  let depths := [10, 15, 20, 30, 40].filter (· ≤ maxDepth)
  depths.findSome? fun d =>
    let cfg : DiscoveryConfig := { taylorDepth := d }
    verifyLowerBound expr hsupp domain bound cfg

end LeanCert.Discovery
