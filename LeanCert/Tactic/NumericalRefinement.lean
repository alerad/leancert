/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

/-!
# Coordinated numerical refinement

This module contains the untrusted scheduling policy shared by tactic-side
candidate search. A stage coordinates three independent sources of enclosure
error: Dyadic rounding, Taylor approximation, and spatial subdivision.

The schedule never proves a theorem. A selected stage must still close the
ordinary Boolean checker and apply its existing Golden Theorem.
-/

namespace LeanCert.Tactic

/-- One finite numerical-refinement attempt. `index` is zero-based. -/
structure NumericalRefinementStage where
  index : Nat
  dyadicPrecision : Int
  taylorDepth : Nat
  subdivisionDepth : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Deterministic policy for coordinated candidate refinement. -/
structure NumericalRefinementPolicy where
  initialDyadicPrecision : Int := -53
  dyadicPrecisionStep : Nat := 32
  initialTaylorDepth : Nat := 10
  taylorDepthStep : Nat := 10
  maxSubdivisionDepth : Nat := 4
  stageCount : Nat := 3
  deriving DecidableEq, Repr, Inhabited

namespace NumericalRefinementPolicy

/-- Spatial depth at a stage, linearly ramped from zero to the configured
maximum. A singleton schedule receives the full configured depth. -/
def subdivisionDepthAt (policy : NumericalRefinementPolicy) (index : Nat) : Nat :=
  if policy.stageCount ≤ 1 then
    policy.maxSubdivisionDepth
  else
    policy.maxSubdivisionDepth * index / (policy.stageCount - 1)

/-- Materialize one stage of the policy. -/
def stageAt (policy : NumericalRefinementPolicy) (index : Nat) :
    NumericalRefinementStage := {
  index
  dyadicPrecision := policy.initialDyadicPrecision -
    Int.ofNat (index * policy.dyadicPrecisionStep)
  taylorDepth := policy.initialTaylorDepth + index * policy.taylorDepthStep
  subdivisionDepth := policy.subdivisionDepthAt index
}

/-- All configured stages in increasing refinement order. -/
def stages (policy : NumericalRefinementPolicy) : List NumericalRefinementStage :=
  (List.range policy.stageCount).map policy.stageAt

/-- Default three-stage policy used by the semantic tactic router. -/
def adaptive (initialTaylorDepth maxSubdivisionDepth : Nat) :
    NumericalRefinementPolicy := {
  initialTaylorDepth
  maxSubdivisionDepth
}

/-- Refine Dyadic rounding and spatial depth while holding a user-specified
Taylor depth fixed. -/
def fixedTaylor (taylorDepth maxSubdivisionDepth : Nat) :
    NumericalRefinementPolicy := {
  initialTaylorDepth := taylorDepth
  taylorDepthStep := 0
  maxSubdivisionDepth
}

end NumericalRefinementPolicy

end LeanCert.Tactic
