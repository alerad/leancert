/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

-- Core modules
import LeanCert.Core.Expr
import LeanCert.Core.Interval
import LeanCert.Core.IntervalReal
import LeanCert.Core.IntervalRealEndpoints
import LeanCert.Core.Taylor
import LeanCert.Core.DerivativeIntervals
-- v1.1: Dyadic arithmetic (high-performance alternative to Rat)
import LeanCert.Core.Dyadic
import LeanCert.Core.IntervalDyadic

-- Numerics modules
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalReal
import LeanCert.Engine.AD
import LeanCert.Engine.Integrate
import LeanCert.Engine.Optimize
import LeanCert.Engine.RootFinding.Main
import LeanCert.Engine.TaylorModel
import LeanCert.Engine.IntervalEvalRefined
import LeanCert.Validity.Bounds
-- v1.1: Dyadic evaluator (prevents denominator explosion)
import LeanCert.Engine.IntervalEvalDyadic

-- Global Optimization
import LeanCert.Engine.Optimization.Box
import LeanCert.Engine.Optimization.Gradient
import LeanCert.Engine.Optimization.Global
import LeanCert.Engine.Optimization.Guided

-- Affine Arithmetic
import LeanCert.Engine.Affine.Basic
import LeanCert.Engine.Affine.Nonlinear
import LeanCert.Engine.Affine.Transcendental
import LeanCert.Engine.Affine.Vector

-- Extended Numerics
import LeanCert.Engine.Extended

-- Search + Certify APIs
import LeanCert.Engine.SearchAPI

-- Meta (metaprogramming utilities)
import LeanCert.Meta.ProveContinuous
import LeanCert.Meta.ProveSupported
import LeanCert.Meta.ToExpr

-- Tactics
import LeanCert.Tactic.Interval
import LeanCert.Tactic.Discovery
-- v1.1: fast_bound tactic (uses Dyadic backend)
import LeanCert.Tactic.DyadicAuto
-- Counter-example hunting
import LeanCert.Tactic.Refute
-- Additional tactics
import LeanCert.Tactic.Bound
import LeanCert.Tactic.TestAuto
import LeanCert.Tactic.TestDiscovery
-- Vector simplification with explicit Fin constructors
import LeanCert.Tactic.VecSimp
-- Finset sum expansion (intervals and explicit sets)
import LeanCert.Tactic.FinSumExpand

-- Discovery Mode
import LeanCert.Discovery

-- Machine Learning
import LeanCert.ML.Network
import LeanCert.ML.IntervalVector
import LeanCert.ML.Distillation
import LeanCert.ML.Symbolic.ReLU
import LeanCert.ML.Symbolic.Sigmoid
import LeanCert.ML.Transformer
import LeanCert.ML.Softmax
import LeanCert.ML.Attention
import LeanCert.ML.LayerNormAffine
import LeanCert.ML.Optimized
import LeanCert.ML.Optimized.IntervalArray
import LeanCert.ML.Optimized.Matrix
import LeanCert.ML.Optimized.QuantizedLayer
import LeanCert.ML.Optimized.MatrixNetwork

-- ML Examples
import LeanCert.Examples.ML.Distillation
import LeanCert.Examples.ML.SineApprox
import LeanCert.Examples.ML.SineNetWeights

-- Examples
import LeanCert.Examples.Basic
import LeanCert.Examples.Calculus
import LeanCert.Examples.Numerics
import LeanCert.Examples.Tactics
import LeanCert.Examples.Certificate
import LeanCert.Examples.GlobalOptimization
import LeanCert.Examples.EdgeCases
import LeanCert.Examples.NeuralNet
import LeanCert.Examples.Showcase

-- Contrib (community contributions)
import LeanCert.Contrib.Sinc

/-! ## Public API

The `LeanCert` namespace re-exports the most commonly used definitions
so users can write `open LeanCert` and have immediate access to the core API.
-/

namespace LeanCert

-- Re-export core expression types
export LeanCert.Core (Expr)

-- Re-export interval types
export LeanCert.Core (IntervalRat)

-- v1.1: Re-export Dyadic types (high-performance arithmetic)
export LeanCert.Core (Dyadic IntervalDyadic)

-- Re-export evaluation and interval operations
export LeanCert.Engine (
  ExprSupported
  ExprSupportedCore
  EvalConfig
  evalInterval
  evalInterval1
  evalInterval_correct
  evalInterval1_correct
  evalIntervalCore
  evalIntervalCore1
  evalIntervalCore_correct
  evalIntervalCore1_correct
  -- Refined evaluation (uses Taylor models for tighter bounds)
  evalIntervalRefined
  evalIntervalRefined1
  evalIntervalRefined_correct
  evalIntervalRefined1_correct
  DualInterval
  evalDual
  derivInterval
  -- Refined AD evaluation
  evalDualRefined
  evalDualRefined1
  evalDualRefined_val_correct
  -- v1.1: Dyadic evaluation (prevents denominator explosion)
  DyadicConfig
  evalIntervalDyadic
  evalIntervalDyadic_correct
  checkUpperBoundDyadic
  checkLowerBoundDyadic
  checkBoundsDyadic
)

-- Re-export certificate verification
export LeanCert.Validity (
  checkUpperBound
  checkLowerBound
  checkStrictUpperBound
  checkStrictLowerBound
  checkBounds
  verify_upper_bound
  verify_lower_bound
  verify_strict_upper_bound
  verify_strict_lower_bound
  verify_bounds
)

-- Re-export root finding
export LeanCert.Engine (
  RootStatus
  bisectRoot
  BisectionResult
)

-- Re-export integration
export LeanCert.Engine (
  integrateInterval
)

-- Re-export optimization
export LeanCert.Engine (
  minimizeInterval
  maximizeInterval
  OptResult
)

-- Re-export global optimization
export LeanCert.Engine.Optimization (
  Box
  GlobalOptConfig
  GlobalBound
  GlobalResult
  globalMinimizeCore
  globalMaximizeCore
)

-- Re-export Discovery Mode
export LeanCert.Discovery (
  DiscoveryConfig
  VerifiedGlobalMin
  VerifiedGlobalMax
  VerifiedRoot
  VerifiedIntegral
  VerifiedUpperBound
  VerifiedLowerBound
  findGlobalMin
  findGlobalMax
  verifyUpperBound
  verifyLowerBound
  searchRoots
)

-- Re-export ML/Distillation API
export LeanCert.ML.Distillation (
  SequentialNet
  checkEquivalence
  verify_equivalence
)

-- Re-export Search + Certify APIs
export LeanCert.Engine.SearchAPI (
  -- Root Finding API
  RootSearchConfig
  RootExistenceProof
  UniqueRootProof
  RootIsolation
  UniqueRootResult
  findRoots
  findUniqueRoot
  -- Optimization API
  OptSearchConfig
  GlobalMinResult
  GlobalMaxResult
  GlobalMin1DResult
  GlobalMax1DResult
  findGlobalMin1D
  findGlobalMax1D
  -- Integration API
  IntegSearchConfig
  IntegralResult
  findIntegral
  findIntegralWithTolerance
  -- Convenience functions
  hasRootIn
  isPositiveOn
  isNegativeOn
  getLowerBound
  getUpperBound
)

/-! ### Convenience abbreviations -/

/-- Evaluate a single-variable expression at a real point.
    Shorthand for `Expr.eval (fun _ => x) e`. -/
noncomputable abbrev eval₀ (e : LeanCert.Core.Expr) (x : ℝ) : ℝ := LeanCert.Core.Expr.eval (fun _ => x) e

/-- Evaluate a single-variable expression at a rational point.
    Useful for `#eval` demonstrations. -/
def eval₀_rat (e : LeanCert.Core.Expr) (x : ℚ) : ℚ :=
  match e with
  | .const q => q
  | .var _ => x
  | .add e₁ e₂ => eval₀_rat e₁ x + eval₀_rat e₂ x
  | .mul e₁ e₂ => eval₀_rat e₁ x * eval₀_rat e₂ x
  | .neg e => -eval₀_rat e x
  | .inv e => (eval₀_rat e x)⁻¹
  | .exp _ => 0  -- Not computable over ℚ
  | .sin _ => 0  -- Not computable over ℚ
  | .cos _ => 0  -- Not computable over ℚ
  | .log _ => 0  -- Not computable over ℚ
  | .atan _ => 0  -- Not computable over ℚ
  | .arsinh _ => 0  -- Not computable over ℚ
  | .atanh _ => 0  -- Not computable over ℚ
  | .sinc _ => 0  -- Not computable over ℚ
  | .erf _ => 0  -- Not computable over ℚ
  | .sinh _ => 0  -- Not computable over ℚ
  | .cosh _ => 0  -- Not computable over ℚ
  | .tanh _ => 0  -- Not computable over ℚ
  | .sqrt _ => 0  -- Not computable over ℚ
  | .pi => 157 / 50  -- Rational approximation of π ≈ 3.14

/-- The unit interval [0, 1] -/
def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The interval [-1, 1] -/
def symInterval : IntervalRat := ⟨-1, 1, by norm_num⟩

end LeanCert
