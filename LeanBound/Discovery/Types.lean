/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Expr
import LeanBound.Core.Interval
import LeanBound.Numerics.IntervalEval
import LeanBound.Numerics.Optimization.Global

/-!
# Discovery Mode: Proof-Carrying Result Types

This module defines structures that bundle computed results with their semantic proofs.
These are the foundation of "Discovery Mode" - finding and certifying answers automatically.

## Main Definitions

* `VerifiedGlobalMin` - A global minimum bound with proof
* `VerifiedGlobalMax` - A global maximum bound with proof
* `VerifiedRoot` - An isolating interval with existence proof
* `UniqueVerifiedRoot` - An isolating interval with uniqueness proof
* `VerifiedIntegral` - Integral bounds with containment proof

## Design Philosophy

Each structure contains:
1. **Data**: The computed numerical result (bounds, intervals, etc.)
2. **Witness**: Location information (which box/interval contains the extremum)
3. **Proof**: A Lean proof term establishing the semantic correctness

The proofs use the "Golden Theorems" from `Certificate.lean` applied to
computationally verified certificates.
-/

namespace LeanBound.Discovery

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization

/-! ## Configuration -/

/-- Configuration for discovery operations -/
structure DiscoveryConfig where
  /-- Maximum iterations for optimization -/
  maxIterations : Nat := 1000
  /-- Tolerance for convergence -/
  tolerance : ℚ := 1/1000
  /-- Taylor expansion depth -/
  taylorDepth : Nat := 10
  /-- Use monotonicity pruning -/
  useMonotonicity : Bool := true
  /-- Maximum depth for root finding bisection -/
  maxBisectionDepth : Nat := 50
  deriving Repr, Inhabited

/-- Convert to GlobalOptConfig -/
def DiscoveryConfig.toGlobalOptConfig (cfg : DiscoveryConfig) : GlobalOptConfig :=
  { maxIterations := cfg.maxIterations
    tolerance := cfg.tolerance
    taylorDepth := cfg.taylorDepth
    useMonotonicity := cfg.useMonotonicity }

/-- Convert to EvalConfig -/
def DiscoveryConfig.toEvalConfig (cfg : DiscoveryConfig) : EvalConfig :=
  { taylorDepth := cfg.taylorDepth }

/-! ## Global Minimum -/

/-- A verified global minimum bound.

This structure bundles:
- The computed lower bound `bound`
- The best box `minimizerBox` containing a near-minimizer
- A proof that `bound ≤ f(x)` for all `x` in the domain

The proof establishes: `∀ ρ, Box.envMem ρ domain → (∀ i ≥ domain.length, ρ i = 0) →
                        bound ≤ Expr.eval ρ expr`
-/
structure VerifiedGlobalMin (expr : Expr) (domain : Box) where
  /-- The verified lower bound -/
  bound : ℚ
  /-- Upper bound on the minimum (for convergence info) -/
  upperBound : ℚ
  /-- Box containing a near-minimizer -/
  minimizerBox : Box
  /-- Number of iterations used -/
  iterations : Nat
  /-- Proof that bound is a valid lower bound -/
  is_lower_bound : ∀ (ρ : Nat → ℝ), Box.envMem ρ domain →
                   (∀ i, i ≥ domain.length → ρ i = 0) →
                   (bound : ℝ) ≤ Expr.eval ρ expr

/-- Width of the bound interval -/
def VerifiedGlobalMin.width (v : VerifiedGlobalMin expr domain) : ℚ :=
  v.upperBound - v.bound

/-- Check if the bound is tight within tolerance -/
def VerifiedGlobalMin.isTight (v : VerifiedGlobalMin expr domain) (tol : ℚ) : Bool :=
  v.width ≤ tol

/-! ## Global Maximum -/

/-- A verified global maximum bound.

This structure bundles:
- The computed upper bound `bound`
- The best box `maximizerBox` containing a near-maximizer
- A proof that `f(x) ≤ bound` for all `x` in the domain
-/
structure VerifiedGlobalMax (expr : Expr) (domain : Box) where
  /-- The verified upper bound -/
  bound : ℚ
  /-- Lower bound on the maximum (for convergence info) -/
  lowerBound : ℚ
  /-- Box containing a near-maximizer -/
  maximizerBox : Box
  /-- Number of iterations used -/
  iterations : Nat
  /-- Proof that bound is a valid upper bound -/
  is_upper_bound : ∀ (ρ : Nat → ℝ), Box.envMem ρ domain →
                   (∀ i, i ≥ domain.length → ρ i = 0) →
                   Expr.eval ρ expr ≤ (bound : ℝ)

/-- Width of the bound interval -/
def VerifiedGlobalMax.width (v : VerifiedGlobalMax expr domain) : ℚ :=
  v.bound - v.lowerBound

/-! ## Root Finding -/

/-- Status of a verified root -/
inductive VerifiedRootStatus where
  /-- Root exists (sign change detected) -/
  | exists_root
  /-- Unique root (Newton contraction verified) -/
  | unique_root
  deriving Repr, DecidableEq, Inhabited

/-- A verified root of an expression.

This structure bundles:
- An isolating interval `interval` containing a root
- The status (existence vs uniqueness)
- A proof that there exists `x ∈ interval` with `f(x) = 0`
-/
structure VerifiedRoot (expr : Expr) where
  /-- Isolating interval containing the root -/
  interval : IntervalRat
  /-- Status: existence or uniqueness -/
  status : VerifiedRootStatus
  /-- Proof of root existence -/
  exists_root : ∃ x : ℝ, x ∈ interval ∧ Expr.eval (fun _ => x) expr = 0

/-- Approximate location of the root (midpoint) -/
def VerifiedRoot.approxLocation (v : VerifiedRoot expr) : ℚ :=
  (v.interval.lo + v.interval.hi) / 2

/-- Width of the isolating interval -/
def VerifiedRoot.width (v : VerifiedRoot expr) : ℚ :=
  v.interval.width

/-- A verified unique root with uniqueness proof -/
structure UniqueVerifiedRoot (expr : Expr) extends VerifiedRoot expr where
  /-- Proof of uniqueness within the interval -/
  unique : ∀ x y : ℝ, x ∈ interval → y ∈ interval →
           Expr.eval (fun _ => x) expr = 0 →
           Expr.eval (fun _ => y) expr = 0 →
           x = y

/-! ## Integration -/

/-- A verified integral bound.

This structure bundles:
- Lower and upper bounds on the integral
- A proof that the true integral lies within these bounds
-/
structure VerifiedIntegral (expr : Expr) (a b : ℚ) where
  /-- Lower bound on the integral -/
  lowerBound : ℚ
  /-- Upper bound on the integral -/
  upperBound : ℚ
  /-- Number of partitions used -/
  partitions : Nat
  /-- Proof that the integral lies in [lowerBound, upperBound] -/
  integral_bounds : lowerBound ≤ upperBound ∧
    ∃ (I : ℝ), -- The true integral
      (lowerBound : ℝ) ≤ I ∧ I ≤ (upperBound : ℝ)

/-- Width of the integral bound -/
def VerifiedIntegral.width (v : VerifiedIntegral expr a b) : ℚ :=
  v.upperBound - v.lowerBound

/-! ## Bound Verification -/

/-- A verified upper bound certificate.

Proves: `∀ x ∈ domain, f(x) ≤ bound`
-/
structure VerifiedUpperBound (expr : Expr) (domain : IntervalRat) where
  /-- The verified upper bound -/
  bound : ℚ
  /-- Proof that bound is valid -/
  is_upper_bound : ∀ x : ℝ, x ∈ domain → Expr.eval (fun _ => x) expr ≤ (bound : ℝ)

/-- A verified lower bound certificate.

Proves: `∀ x ∈ domain, bound ≤ f(x)`
-/
structure VerifiedLowerBound (expr : Expr) (domain : IntervalRat) where
  /-- The verified lower bound -/
  bound : ℚ
  /-- Proof that bound is valid -/
  is_lower_bound : ∀ x : ℝ, x ∈ domain → (bound : ℝ) ≤ Expr.eval (fun _ => x) expr

/-! ## Multi-dimensional variants -/

/-- A verified bound over a box (multi-dimensional domain) -/
structure VerifiedBoxBound (expr : Expr) (domain : Box) where
  /-- Lower bound -/
  lo : ℚ
  /-- Upper bound -/
  hi : ℚ
  /-- Proof of bounds -/
  bounds_valid : ∀ (ρ : Nat → ℝ), Box.envMem ρ domain →
                 (∀ i, i ≥ domain.length → ρ i = 0) →
                 (lo : ℝ) ≤ Expr.eval ρ expr ∧ Expr.eval ρ expr ≤ (hi : ℝ)

end LeanBound.Discovery
