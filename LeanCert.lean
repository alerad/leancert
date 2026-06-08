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
import LeanCert.Cert.Interval
import LeanCert.Analysis.ContourShift
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
-- v1.1: Computable polynomial Taylor models (high-order integration)
import LeanCert.Engine.CompPoly
-- v1.2: Reflective sum evaluator (O(1) proof size for finite sums)
import LeanCert.Engine.ReflectiveSum
-- v1.3: General finite sum evaluator (O(1) proof size for any Core.Expr body)
import LeanCert.Engine.FinSumDyadic
-- v1.3: Witness-based finite sum evaluator (user-provided per-term evaluator)
import LeanCert.Engine.WitnessSum
-- v1.4: Generic finite table certificates (row-wise native_decide loops)
import LeanCert.Engine.Table
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta

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

-- Q-product product-integral certificates
import LeanCert.QProduct
import LeanCert.ConstantFactory
import LeanCert.ConstantFactory.IntervalBank

-- Analytic number theory certificate machinery
import LeanCert.ANT

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
-- Note: TestAuto and TestDiscovery moved to `examples` build target.
-- Vector simplification with explicit Fin constructors
import LeanCert.Tactic.VecSimp
-- Finset sum expansion (intervals, explicit sets, and Fin sums)
import LeanCert.Tactic.FinSumExpand
-- O(1) proof-size finite sum bounds via native_decide
import LeanCert.Tactic.FinSumBound
-- Witness-based finite sum bounds (user-provided evaluator + correctness proof)
import LeanCert.Tactic.FinSumWitness

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

-- Note: Examples moved to separate `examples` build target.
-- Build with: lake build examples

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

-- Re-export small certificate combinators
export LeanCert.Cert (
  checkRatInterval
  checkRatUpper
  checkRatLower
  verify_rat_interval
  verify_rat_upper
  verify_rat_lower
)

-- Re-export contour-shift certificate API
export LeanCert.Analysis.ContourShift (
  bottomIntegral
  topIntegral
  rightIntegral
  leftIntegral
  rectBoundary
  rectBoundary_eq_zero_of_continuousOn_of_differentiableOn
  VerticalShiftCert
  verticalIntegral
  topHorizontalIntegral
  bottomHorizontalIntegral
  StripPoleCert
  stripResidueSum
  RectangleShiftCert
  HorizontalVanishCert
  HorizontalBoundCert
  ContourShiftCert
)

export LeanCert.Analysis.ContourShift.VerticalShiftCert (
  vertical_shift
  ofHolomorphicRectangle
)

export LeanCert.Analysis.ContourShift.HorizontalBoundCert (
  toVanishCert
)

export LeanCert.Analysis.ContourShift.ContourShiftCert (
  leftValue
  rightValue
  residueSum
  shift_identity
  shift_identity'
)

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

-- Re-export reflective sum evaluator (O(1) proof size for finite sums)
export LeanCert.Engine (
  TableCert
  AdjacentAll
  checkAdjacent
  checkAdjacentList
  checkLinkedRows
  checkStrictlyIncreasingBy
  adjacentAll_of_checkAdjacent
  adjacentAll_of_checkAdjacentList
  linkedRows_of_checkLinkedRows
  adjacentIncreasing_of_checkStrictlyIncreasingBy
  BKLNWSumConfig
  bklnwF
  bklnwSumDyadic
  bklnwSumExpDyadic
  checkBKLNWSumUpperBound
  checkBKLNWSumLowerBound
  checkBKLNWExpUpperBound
  checkBKLNWExpLowerBound
  checkBKLNWSumUpperBound_correct
  checkBKLNWSumLowerBound_correct
  rpowIntervalDyadic
  mem_rpowIntervalDyadic
)

export LeanCert.Engine.TableCert (
  checkAll
  failingIndices
  failingIndicesFrom
  row_checked_of_list_all
  verify
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

export LeanCert.Engine.TaylorModel (
  integrateShiftedPoly
  integralBoundPolyExact
  integralBoundCoarse
  integral_mem_bound_polyExact_of_poly_integral
  integral_mem_bound_coarse
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

-- Re-export Chebyshev certificate APIs
export LeanCert.Engine.ChebyshevPsi (
  vonMangoldtUB
  psiUB
  checkPsiLeMulWith
  checkAllPsiLeMulWith
  checkPsiBound
  allPsiBoundsHold
  psi_le_psiUB
  psi_le_of_checkPsiLeMulWith
  psi_le_mul_real_of_checkPsiLeMulWith
  checkAllPsiLeMulWith_implies_checkPsiLeMulWith
  allPsiBoundsHold_implies_checkPsiBound
  verify_psi_le_mul
  verify_psi_le_mul_real
  verify_all_psi_le_mul
  verify_all_psi_le_mul_real
  verify_psi_bound
  verify_all_psi_bound
)

export LeanCert.Engine.ChebyshevTheta (
  logPrimeUB
  logPrimeLB
  thetaUB
  thetaLB
  checkThetaLeMulWith
  checkAllThetaLeMulWith
  checkThetaAbsError
  checkAllThetaAbsError
  checkThetaRelError
  checkAllThetaRelError
  checkThetaRelErrorReal
  checkAllThetaRelErrorReal
  theta_le_thetaUB
  thetaLB_le_theta
  theta_le_of_checkThetaLeMulWith
  abs_theta_sub_le_of_checkThetaAbsError
  abs_theta_sub_le_mul_of_checkThetaRelError
  abs_theta_sub_le_mul_of_checkThetaRelErrorReal
  checkAllThetaLeMulWith_implies_checkThetaLeMulWith
  checkAllThetaAbsError_implies_checkThetaAbsError
  checkAllThetaRelError_implies_checkThetaRelError
  checkAllThetaRelErrorReal_implies
  verify_theta_le_mul
  verify_theta_abs_error
  verify_theta_rel_error
  verify_theta_rel_error_real
  verify_all_theta_le_mul
  verify_all_theta_abs_error
  verify_all_theta_rel_error
)

-- Re-export QProduct API
export LeanCert.QProduct (
  qProd
  F
  subsetSign
  subsetWeight
  finiteIntegralRat
  momentRat
  moment
  finiteIntegralRat_correct
  momentRat_correct
  qProd_powerset_expand
  qProd_nonneg
  qProd_le_one
  pow_mem_unit_interval
  F_nonneg
  F_le_one
  F_antitone
  one_sub_prod_one_sub_le_sum
  qProd_sub_le_commonPrefix_sum
  odd_tail_telescope_bound
  odd_tail_sum_le_geom
  checkFiniteIntegralInterval
  verify_finiteIntegral_interval
  checkFiniteIntegralUpper
  checkFiniteIntegralLower
  verify_finiteIntegral_upper
  verify_finiteIntegral_lower
  primesLE
  primeFRat
  primeSandwichErrorRat
  primeSandwichLowerRat
  primeSandwichLowerFun
  primeLambda
  primeFRat_antitone
  primeLambda_le_trunc
  primeLambda_lower_of_forall
  checkPrimeLambdaUpper
  verify_primeLambda_upper
  verify_primeLambda_interval_of_forall
  prime_odd_of_gt_two
  odd_ge_form
  telescope_odd_sum_bound_from
  primeSandwichLowerFun_pointwise_of_tail_ge
  primeSandwichLowerFun_le_prime_truncation_of_tail_ge
  integral_primeSandwichLowerFun_eq_rat
  primeSandwichLowerRat_le_truncation_of_tail_ge
  primeSandwichLowerRat_le_lambda_of_tail_ge
  primeLambda_rational_sandwich
  primeLambda_sandwich
  primeSandwichErrorRat_three_five
  primeSandwichLowerRat_three_five
  primeSandwichLowerRat_three_five_le_lambda
  primeFRat_lower_nineteen_thirtysix
  primeLambda_lower_nineteen_thirtysix
  primeLambda_gt_half
)

-- Re-export ConstantFactory API
export LeanCert.ConstantFactory (
  observerIntegralRat
  observerIntegral
  observerIntegralRat_correct
  F_union_eq_observerIntegral
  observerIntegralRat_eq_F_union
  checkConstantFactoryInterval
  verify_constantFactory_interval
  checkConstantFactoryUpper
  checkConstantFactoryLower
  verify_constantFactory_upper
  verify_constantFactory_lower
  KernelIntervalBank
  observerTerm
  observerIntervalTerm
  observerIntegralList
  observerIntervalList
  observerInterval
  observerTerm_mem_interval
  observerIntegralList_mem_observerIntervalList
  observerIntegralList_powerset_eq
  F_union_mem_observerInterval
  exactKernelIntervalBank
)

-- Re-export ANT certificate API
export LeanCert.ANT (
  StepFn
  stepLowerRat
  stepUpperRat
  stepSum
  stepLowerRat_le_stepSum
  stepSum_le_stepUpperRat
  checkStepSumInterval
  checkStepSumLower
  checkStepSumUpper
  verify_stepSum_interval
  verify_stepSum_lower
  verify_stepSum_upper
  prefixSum
  prefixSumRat
  abelTransformRat
  weightedSumRat
  weightedSum
  abelTransformOfPrefix
  weightedSumReal
  abelTransformReal
  weightedSumReal_eq_abelTransformReal
  weightedSumRat_eq_abelTransformRat
  weightedSum_eq_abelTransformOfPrefix
  checkAbelInterval
  checkAbelUpper
  checkAbelLower
  verify_abel_interval
  verify_abel_upper
  verify_abel_lower
  coeffLowerRat
  coeffUpperRat
  abelBoundLowerRat
  abelBoundUpperRat
  abelBoundLowerRat_le_transform
  transform_le_abelBoundUpperRat
  abelTransformOfPrefix_le_abelBoundUpperRat
  abelTransformOfPrefix_ge_abelBoundLowerRat
  checkAbelBoundInterval
  verify_abelBound_interval
  productLowerRat
  productUpperRat
  finiteProduct
  productLowerRat_le_finiteProduct
  finiteProduct_le_productUpperRat
  checkEulerProductInterval
  verify_eulerProduct_interval
  finiteLogProduct
  logProductLowerRat
  logProductUpperRat
  logProductLowerRat_le_finiteLogProduct
  finiteLogProduct_le_logProductUpperRat
  checkLogProductInterval
  verify_logProduct_interval
  finiteProduct_eq_exp_finiteLogProduct
  verify_product_interval_of_log_interval
  verify_product_lower_of_log_lower
  verify_product_upper_of_log_upper
  oneMinusInvRat
  onePlusInvRat
  primeEulerOneMinusInv
  primeEulerOneMinusInvRat
  primeEulerOnePlusInv
  primeEulerOnePlusInvRat
  checkPrimeEulerOneMinusInvInterval
  checkPrimeEulerOnePlusInvInterval
  verify_primeEulerOneMinusInv_interval
  verify_primeEulerOnePlusInv_interval
  finiteDirichletSum
  intervalMulLowerRat
  intervalMulUpperRat
  finiteDirichletSumLowerRat
  finiteDirichletSumUpperRat
  finiteDirichletSumLowerRat_le
  finiteDirichletSum_le_upperRat
  checkDirichletSumInterval
  checkDirichletSumLower
  checkDirichletSumUpper
  verify_dirichletSum_interval
  verify_dirichletSum_lower
  verify_dirichletSum_upper
  naturalsIcc
  harmonicSum
  harmonicSumRat
  primeHarmonicSum
  primeHarmonicSumRat
  logPrimeOverPrimeSum
  logPrimeOverPrimeLowerRat
  logPrimeOverPrimeUpperRat
  harmonicSum_eq_rat
  primeHarmonicSum_eq_rat
  checkHarmonicSumInterval
  checkPrimeHarmonicSumInterval
  checkLogPrimeOverPrimeSumInterval
  logPrimeOverPrimeLowerRat_le
  logPrimeOverPrime_le_upperRat
  verify_harmonicSum_interval
  verify_primeHarmonicSum_interval
  verify_logPrimeOverPrimeSum_interval
  mertensLogSum
  thetaIncrement
  invNatRat
  thetaPrefixLowerRat
  thetaPrefixUpperRat
  mertensAbelSum
  thetaPrefixLowerRat_le_prefix
  prefix_le_thetaPrefixUpperRat
  thetaPrefix_envelope
  checkMertensAbelInterval
  verify_mertensAbel_interval
  mertensLogSumLowerRat
  mertensLogSumUpperRat
  mertensLogSumLowerRat_le
  mertensLogSum_le_mertensLogSumUpperRat
  checkMertensLogSumInterval
  verify_mertensLogSum_interval
)

-- Re-export asymptotic envelope API
export LeanCert.ANT.Asymp (
  AsympEnv
  evalAtNat
  ErrorDomination
  PointwiseEnvelope
  SlabInequalityCert
  InequalityTableRow
  checkInequalityTableRow
  InequalityTableCert
)

export LeanCert.ANT.Asymp.AsympEnv (
  summatory
  summatoryReal
  lower
  upper
  lowerReal
  upperReal
  lower_le_summatory
  summatory_le_upper
  lowerReal_le_summatoryReal
  summatoryReal_le_upperReal
  certReal
  weakenError
  shiftCutoff
  add
  neg
  sub
  constMul
  toPointwiseFloorEnvelope
)

export LeanCert.ANT.Asymp.PointwiseEnvelope (
  lower
  upper
  lower_le_value
  value_le_upper
  weakenError
)

export LeanCert.ANT.Asymp.SlabInequalityCert (
  verify
)

export LeanCert.ANT.Asymp.InequalityTableCert (
  verify
  failingIndices
)

export LeanCert.ANT.PrimePowerExt (
  ext_prime_powers
  eq_iff_eq_on_prime_powers
  LocalPrimePowerCert
)

export LeanCert.ANT.PrimePowerExt.LocalPrimePowerCert (
  sound
)

export LeanCert.ANT.PNTCompilers (
  psi_to_theta_bound
  theta_to_pi_bound_of_decomposition
  theta_to_pi_bound
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
  | .namedConst c => c.toRatApprox

/-- The unit interval [0, 1] -/
def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The interval [-1, 1] -/
def symInterval : IntervalRat := ⟨-1, 1, by norm_num⟩

end LeanCert
