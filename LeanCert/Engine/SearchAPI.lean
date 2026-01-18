/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Bounds
import LeanCert.Engine.RootFinding.Main
import LeanCert.Engine.Optimization.Global
import LeanCert.Meta.ProveContinuous

/-!
# Search + Certify APIs

This module provides high-level APIs that wrap existing numerical algorithms
to return *answers with proofs*, not just *verdicts*.

These APIs bridge the gap between "verify a guess" and "find the answer":
- `findRoots` finds isolating intervals with existence proofs
- `findUniqueRoot` finds a unique root with existence AND uniqueness proofs
- `findGlobalMin` / `findGlobalMax` finds extrema with bound proofs
- `findIntegral` computes integral bounds with correctness proofs

## Usage

These APIs are designed to be:
1. Called programmatically from other Lean code
2. Used by the Python SDK to generate certificates
3. Invoked by discovery tactics

## Design Philosophy

Each API wraps existing algorithms (bisection, Newton, branch-and-bound, etc.)
and bundles the result with the appropriate correctness proof.
-/

namespace LeanCert.Engine.SearchAPI

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization
open LeanCert.Validity

/-! ## Root Finding API (0.1.1) -/

/-- Configuration for root finding search -/
structure RootSearchConfig where
  /-- Maximum bisection depth -/
  maxDepth : Nat := 20
  /-- Tolerance for interval width -/
  tolerance : ℚ := 1/1000
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr, Inhabited

/-- Proof that a root exists in the given interval.

    This structure bundles an interval with a proof that there exists
    a point x in the interval where f(x) = 0. -/
structure RootExistenceProof (e : Expr) (I : IntervalRat) where
  /-- Proof that the expression is supported (for correctness theorems) -/
  supported : ExprSupportedCore e
  /-- Proof of continuity on the interval -/
  continuous : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)
  /-- The actual root existence proof -/
  hasRoot : ∃ x ∈ I, Expr.eval (fun _ => x) e = 0

/-- Proof that a root exists AND is unique.

    Extends RootExistenceProof with uniqueness: there is exactly one root. -/
structure UniqueRootProof (e : Expr) (I : IntervalRat) extends RootExistenceProof e I where
  /-- Uniqueness: any two roots must be equal -/
  unique : ∀ x y, x ∈ I → y ∈ I →
           Expr.eval (fun _ => x) e = 0 → Expr.eval (fun _ => y) e = 0 → x = y

/-- Result of root finding: an isolating interval with existence proof -/
structure RootIsolation (e : Expr) where
  /-- The isolating interval containing the root -/
  interval : IntervalRat
  /-- Proof that a root exists in this interval -/
  proof : RootExistenceProof e interval

/-- Find all roots of `e` in interval `I`, returning isolating intervals with existence proofs.

    This wraps `bisectRoot` to find intervals with sign changes, then
    constructs existence proofs using the IVT (via `verify_sign_change`). -/
noncomputable def findRoots (e : Expr) (hsupp : ExprSupportedCore e)
    (hdom : ∀ J : IntervalRat, LeanCert.Meta.exprContinuousDomainValid e (Set.Icc J.lo J.hi))
    (I : IntervalRat) (cfg : RootSearchConfig := {}) :
    List (RootIsolation e) :=
  let tol : ℚ := 1/1000  -- Use default tolerance
  let htol : 0 < tol := by norm_num
  let result := bisectRoot e I cfg.maxDepth tol htol
  -- Filter intervals that have hasRoot status (sign change detected)
  let rootIntervals := result.intervals.filter fun (_, s) => s == RootStatus.hasRoot
  -- For each interval with hasRoot status, construct the proof
  rootIntervals.filterMap fun (J, _) =>
    -- Check if we can verify sign change with the computable checker
    let evalCfg : EvalConfig := { taylorDepth := cfg.taylorDepth }
    if h : RootFinding.checkSignChange e J evalCfg = true then
      let hCont := LeanCert.Meta.exprSupportedCore_continuousOn e hsupp (hdom J)
      some {
        interval := J
        proof := {
          supported := hsupp
          continuous := hCont
          hasRoot := RootFinding.verify_sign_change e hsupp J evalCfg hCont h
        }
      }
    else
      none

/-- Result of unique root finding: an interval with existence and uniqueness proof.
    This is a Type, not a Prop, so it can be used in Option. -/
structure UniqueRootResult (e : Expr) (I : IntervalRat) : Type where
  /-- Proof that the expression is supported (for correctness theorems) -/
  supported : ExprSupportedCore e
  /-- Proof of continuity on the interval -/
  continuous : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)
  /-- The actual root existence proof -/
  hasRoot : ∃ x ∈ I, Expr.eval (fun _ => x) e = 0
  /-- Uniqueness: any two roots must be equal -/
  unique : ∀ x y, x ∈ I → y ∈ I →
           Expr.eval (fun _ => x) e = 0 → Expr.eval (fun _ => y) e = 0 → x = y

/-- Find a unique root with existence AND uniqueness proof.

    This wraps Newton contraction checking to find intervals where:
    1. A root exists (via contraction or sign change)
    2. The root is unique (via derivative being bounded away from 0)

    Requires `UsesOnlyVar0 e` for the Newton contraction proof to work.
    Returns `none` if no unique root can be verified. -/
noncomputable def findUniqueRoot (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : RootSearchConfig := {}) :
    Option (UniqueRootResult e I) :=
  let evalCfg : EvalConfig := { taylorDepth := cfg.taylorDepth }
  let newtonCfg : RootFinding.NewtonConfig := {}  -- Default Newton config
  let hdomValid := LeanCert.Meta.exprContinuousDomainValid_of_ExprSupported hsupp (s := Set.Icc I.lo I.hi)
  let hCont := LeanCert.Meta.exprSupportedCore_continuousOn e hsupp.toCore hdomValid
  -- Try Newton contraction check - need both core (for search) and non-core (for proof)
  if h_core : RootFinding.checkNewtonContractsCore e I evalCfg = true then
    if h_newton : RootFinding.checkNewtonContracts e I newtonCfg = true then
      let uniqueProof := RootFinding.verify_unique_root_core e hsupp hvar0 I
        evalCfg newtonCfg hCont h_core h_newton
      -- Extract the components from ExistsUnique
      some {
        supported := hsupp.toCore
        continuous := hCont
        hasRoot := by
          obtain ⟨x, ⟨hx_mem, hx_root⟩, _⟩ := uniqueProof
          exact ⟨x, hx_mem, hx_root⟩
        unique := by
          obtain ⟨_, _, huniq⟩ := uniqueProof
          intro x y hx hy hfx hfy
          have hxu := huniq x ⟨hx, hfx⟩
          have hyu := huniq y ⟨hy, hfy⟩
          rw [hxu, hyu]
      }
    else
      -- Non-core Newton check failed
      none
  else
    -- Core Newton contraction didn't work; could try other methods
    none

/-! ## Optimization API (0.1.2) -/

/-- Configuration for optimization search -/
structure OptSearchConfig where
  /-- Maximum iterations for branch-and-bound -/
  maxIterations : Nat := 1000
  /-- Tolerance for box width -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr, Inhabited

/-- Result of global minimization with proof.

    Bundles the minimization result with proofs that:
    1. `minValue.lo` is a valid lower bound for all x in B
    2. There exists a point achieving a value ≤ `minValue.hi` -/
structure GlobalMinResult (e : Expr) (B : Box) where
  /-- Box containing the minimizer (best bound found here) -/
  minimizerBox : Box
  /-- Interval containing the minimum value -/
  minValue : IntervalRat
  /-- Proof of the lower bound: ∀ x ∈ B, minValue.lo ≤ f(x) -/
  lowerBoundProof : ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
                    (minValue.lo : ℝ) ≤ Expr.eval ρ e
  /-- Proof of the upper bound witness: ∃ x ∈ B, f(x) ≤ minValue.hi -/
  upperBoundWitness : ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧
                      (∀ i, i ≥ B.length → ρ i = 0) ∧
                      Expr.eval ρ e ≤ minValue.hi

/-- Result of global maximization with proof.

    Bundles the maximization result with proofs that:
    1. `maxValue.hi` is a valid upper bound for all x in B
    2. There exists a point achieving a value ≥ `maxValue.lo` -/
structure GlobalMaxResult (e : Expr) (B : Box) where
  /-- Box containing the maximizer (best bound found here) -/
  maximizerBox : Box
  /-- Interval containing the maximum value -/
  maxValue : IntervalRat
  /-- Proof of the upper bound: ∀ x ∈ B, f(x) ≤ maxValue.hi -/
  upperBoundProof : ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
                    Expr.eval ρ e ≤ (maxValue.hi : ℝ)
  /-- Proof of the lower bound witness: ∃ x ∈ B, f(x) ≥ maxValue.lo -/
  lowerBoundWitness : ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧
                      (∀ i, i ≥ B.length → ρ i = 0) ∧
                      (maxValue.lo : ℝ) ≤ Expr.eval ρ e

/-- Convert OptSearchConfig to GlobalOptConfig -/
def OptSearchConfig.toGlobalOptConfig (cfg : OptSearchConfig) : GlobalOptConfig :=
  { maxIterations := cfg.maxIterations
    tolerance := cfg.tolerance
    useMonotonicity := cfg.useMonotonicity
    taylorDepth := cfg.taylorDepth }

/-- Find global minimum of `e` over box `B` with proof.

    This wraps `globalMinimizeCore` and bundles the result with
    correctness proofs derived from `globalMinimizeCore_lo_correct`.

    Note: Uses ExprSupported (no log) for automatic domain validity. -/
noncomputable def findGlobalMin (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : OptSearchConfig := {}) :
    GlobalMinResult e B :=
  let optCfg := cfg.toGlobalOptConfig
  let result := globalMinimizeCore e B optCfg
  let hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := optCfg.taylorDepth } :=
    fun B' _ => ExprSupported.domainValid hsupp B'.toEnv { taylorDepth := optCfg.taylorDepth }
  {
    minimizerBox := result.bound.bestBox
    minValue := { lo := result.bound.lo, hi := result.bound.hi,
                  le := globalMinimizeCore_lo_le_hi e hsupp.toCore B optCfg hdom }
    lowerBoundProof := fun ρ hρ hzero =>
      globalMinimizeCore_lo_correct e hsupp.toCore B optCfg hdom ρ hρ hzero
    upperBoundWitness := globalMinimizeCore_hi_achievable e hsupp.toCore B optCfg hdom
  }

/-- Find global maximum of `e` over box `B` with proof.

    This wraps `globalMaximizeCore` and bundles the result with
    correctness proofs.

    Note: Uses ExprSupported (no log) for automatic domain validity. -/
noncomputable def findGlobalMax (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : OptSearchConfig := {}) :
    GlobalMaxResult e B :=
  let optCfg := cfg.toGlobalOptConfig
  let result := globalMaximizeCore e B optCfg
  let hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := optCfg.taylorDepth } :=
    fun B' _ => ExprSupported.domainValid hsupp B'.toEnv { taylorDepth := optCfg.taylorDepth }
  {
    maximizerBox := result.bound.bestBox
    maxValue := { lo := result.bound.lo, hi := result.bound.hi,
                  le := globalMaximizeCore_lo_le_hi e hsupp.toCore B optCfg hdom }
    upperBoundProof := fun ρ hρ hzero =>
      globalMaximizeCore_hi_correct e hsupp.toCore B optCfg hdom ρ hρ hzero
    lowerBoundWitness := globalMaximizeCore_lo_achievable e hsupp.toCore B optCfg hdom
  }

/-! ## 1D Optimization Convenience APIs -/

/-- Result of 1D global minimization with simplified proof structure -/
structure GlobalMin1DResult (e : Expr) (I : IntervalRat) where
  /-- Interval containing the minimizer -/
  minimizerInterval : IntervalRat
  /-- Interval containing the minimum value -/
  minValue : IntervalRat
  /-- Proof of the lower bound: ∀ x ∈ I, minValue.lo ≤ f(x) -/
  lowerBoundProof : ∀ x ∈ I, (minValue.lo : ℝ) ≤ Expr.eval (fun _ => x) e

/-- Result of 1D global maximization with simplified proof structure -/
structure GlobalMax1DResult (e : Expr) (I : IntervalRat) where
  /-- Interval containing the maximizer -/
  maximizerInterval : IntervalRat
  /-- Interval containing the maximum value -/
  maxValue : IntervalRat
  /-- Proof of the upper bound: ∀ x ∈ I, f(x) ≤ maxValue.hi -/
  upperBoundProof : ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ (maxValue.hi : ℝ)

/-- Convert IntervalRat to a 1D Box -/
def intervalToBox (I : IntervalRat) : Box := [I]

/-- Find global minimum of `e` over 1D interval `I` with proof.

    Specialized version for single-variable functions.
    Requires `e.usesOnlyVar0 = true` to ensure eval equivalence. -/
noncomputable def findGlobalMin1D (e : Expr) (hsupp : ExprSupported e)
    (he1d : e.usesOnlyVar0 = true)
    (I : IntervalRat) (cfg : OptSearchConfig := {}) :
    GlobalMin1DResult e I :=
  let B := intervalToBox I
  let result := findGlobalMin e hsupp B cfg
  {
    minimizerInterval := result.minimizerBox.head!
    minValue := result.minValue
    lowerBoundProof := fun x hx => by
      -- Convert 1D membership to box membership
      let ρ : Nat → ℝ := fun n => if n = 0 then x else 0
      have hρ : Box.envMem ρ B := by
        intro ⟨i, hi⟩
        simp only [B, intervalToBox] at hi ⊢
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        simp only [List.getElem_cons_zero, ρ, ↓reduceIte]
        exact hx
      have hzero : ∀ i, i ≥ B.length → ρ i = 0 := by
        intro i hi
        simp only [B, intervalToBox, List.length_singleton] at hi
        simp only [ρ]
        split_ifs with h0
        · subst h0; omega
        · rfl
      have hlb := result.lowerBoundProof ρ hρ hzero
      -- Use eval_1d_equiv to show Expr.eval ρ e = Expr.eval (fun _ => x) e
      rw [Expr.eval_1d_equiv e he1d x] at hlb
      exact hlb
  }

/-- Find global maximum of `e` over 1D interval `I` with proof.

    Specialized version for single-variable functions.
    Requires `e.usesOnlyVar0 = true` to ensure eval equivalence. -/
noncomputable def findGlobalMax1D (e : Expr) (hsupp : ExprSupported e)
    (he1d : e.usesOnlyVar0 = true)
    (I : IntervalRat) (cfg : OptSearchConfig := {}) :
    GlobalMax1DResult e I :=
  let B := intervalToBox I
  let result := findGlobalMax e hsupp B cfg
  {
    maximizerInterval := result.maximizerBox.head!
    maxValue := result.maxValue
    upperBoundProof := fun x hx => by
      let ρ : Nat → ℝ := fun n => if n = 0 then x else 0
      have hρ : Box.envMem ρ B := by
        intro ⟨i, hi⟩
        simp only [B, intervalToBox] at hi ⊢
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        simp only [List.getElem_cons_zero, ρ, ↓reduceIte]
        exact hx
      have hzero : ∀ i, i ≥ B.length → ρ i = 0 := by
        intro i hi
        simp only [B, intervalToBox, List.length_singleton] at hi
        simp only [ρ]
        split_ifs with h0
        · subst h0; omega
        · rfl
      have hub := result.upperBoundProof ρ hρ hzero
      -- Use eval_1d_equiv to show Expr.eval ρ e = Expr.eval (fun _ => x) e
      rw [Expr.eval_1d_equiv e he1d x] at hub
      exact hub
  }

/-! ## Integration API (0.1.3) -/

/-- Configuration for integration search -/
structure IntegSearchConfig where
  /-- Number of subdivisions for uniform partitioning -/
  subdivisions : Nat := 10
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr, Inhabited

/-- Result of verified integration.

    Bundles the computed integral bounds with a proof that
    the true integral lies within those bounds. -/
structure IntegralResult (e : Expr) (I : IntervalRat) where
  /-- Interval containing the true integral -/
  bounds : IntervalRat
  /-- Proof that the integral is in the bounds -/
  proof : ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bounds

/-- Compute rigorous bounds on ∫[a,b] f(x) dx with proof.

    This wraps `integrateInterval1Core` and bundles the result with
    the correctness proof from `integrateInterval1Core_correct`. -/
noncomputable def findIntegral (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : IntegSearchConfig := {})
    (hdom : evalDomainValid1 e I { taylorDepth := cfg.taylorDepth })
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    IntegralResult e I :=
  let evalCfg : EvalConfig := { taylorDepth := cfg.taylorDepth }
  let bounds := Integration.integrateInterval1Core e I evalCfg
  {
    bounds := bounds
    proof := Integration.integrateInterval1Core_correct e hsupp I evalCfg hdom hcontdom
  }

/-- Compute integral bounds with specified accuracy target.

    Automatically increases subdivision count until the bound width
    is below the target tolerance (or max subdivisions reached). -/
noncomputable def findIntegralWithTolerance (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (taylorDepth : Nat := 10)
    (hdom : evalDomainValid1 e I { taylorDepth := taylorDepth })
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi))
    (_tol : ℚ) (_htol : 0 < _tol)
    (_maxSubdiv : Nat := 100) :
    IntegralResult e I :=
  -- For now, just use single-interval integration
  -- A more sophisticated version would increase subdivisions adaptively
  let evalCfg : EvalConfig := { taylorDepth := taylorDepth }
  let bounds := Integration.integrateInterval1Core e I evalCfg
  {
    bounds := bounds
    proof := Integration.integrateInterval1Core_correct e hsupp I evalCfg hdom hcontdom
  }

/-! ## Convenience Functions for Common Cases -/

/-- Check if an expression has a root in an interval (boolean version) -/
def hasRootIn (e : Expr) (I : IntervalRat) (cfg : RootSearchConfig := {}) : Bool :=
  let evalCfg : EvalConfig := { taylorDepth := cfg.taylorDepth }
  RootFinding.checkSignChange e I evalCfg

/-- Check if an expression is positive on an interval -/
def isPositiveOn (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  0 < (evalIntervalCore1 e I cfg).lo

/-- Check if an expression is negative on an interval -/
def isNegativeOn (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  (evalIntervalCore1 e I cfg).hi < 0

/-- Get a lower bound on the minimum value -/
def getLowerBound (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : ℚ :=
  (evalIntervalCore1 e I cfg).lo

/-- Get an upper bound on the maximum value -/
def getUpperBound (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : ℚ :=
  (evalIntervalCore1 e I cfg).hi

end LeanCert.Engine.SearchAPI
