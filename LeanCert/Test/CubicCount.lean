/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Algebra

/-!
# Discriminant root-count certificate regressions

The shifted family is `(x-t)(x-t-1)(x-t-2)`. Its discriminant is identically
`4`, but direct interval evaluation cannot see the cancellations on the whole
parameter box. Adaptive subdivision succeeds.
-/

namespace LeanCert.Test.CubicCount

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization
open LeanCert.Validity.Algebra

def exactThreeRoots : Cubic ℝ := ⟨1, 0, -1, 0⟩
def exactOneRoot : Cubic ℝ := ⟨1, 0, 1, 0⟩

example : (Engine.Algebra.cubicZeroSet exactThreeRoots).ncard = 3 := by
  apply Engine.Algebra.cubicZeroSet_ncard_eq_three_of_discr_pos
  · norm_num [exactThreeRoots]
  · norm_num [exactThreeRoots, Cubic.discr]

example : (Engine.Algebra.cubicZeroSet exactOneRoot).ncard = 1 := by
  apply Engine.Algebra.cubicZeroSet_ncard_eq_one_of_discr_neg
  · norm_num [exactOneRoot]
  · norm_num [exactOneRoot, Cubic.discr]

example : (Engine.Algebra.quadraticZeroSet 1 0 1).ncard = 0 := by
  apply Engine.Algebra.quadraticZeroSet_ncard_eq_zero_of_discrim_neg
  norm_num [discrim]

def t : Expr := .var 0

def shiftedThreeRootFamily : CubicFamily where
  a := .const 1
  b := .neg (.add (.mul (.const 3) t) (.const 3))
  c := .add (.add (.mul (.const 3) (.pow t 2)) (.mul (.const 6) t)) (.const 2)
  d := .neg (.add (.add (.pow t 3) (.mul (.const 3) (.pow t 2))) (.mul (.const 2) t))

def oneRootFamily : CubicFamily where
  a := .const 1
  b := .const 0
  c := .const 1
  d := t

def smallParameterBox : Box := [⟨-1 / 10, 1 / 10, by norm_num⟩]
def unitParameterBox : Box := [⟨-1, 1, by norm_num⟩]

-- Dependency makes the unsplit discriminant enclosure inconclusive.
example : cubicCountCheckBox shiftedThreeRootFamily smallParameterBox .three {} = false := by
  native_decide

-- Six widest-dimension bisections recover the uniform positive sign.
example : cubicCountCheckSubdiv shiftedThreeRootFamily smallParameterBox .three 6 {} = true := by
  native_decide

example : ∀ rho : Nat → ℝ, smallParameterBox.envMem rho →
    (∀ i, i ≥ smallParameterBox.length → rho i = 0) →
    (Engine.Algebra.cubicZeroSet (shiftedThreeRootFamily.at rho)).ncard = 3 := by
  exact verify_cubic_root_count_subdiv shiftedThreeRootFamily smallParameterBox .three 6 {}
    (by native_decide)

-- `x³ + x + t` has negative discriminant for every real `t`; subdivision
-- resolves the dependency introduced by interval evaluation of `t²`.
example : cubicCountCheckSubdiv oneRootFamily unitParameterBox .one 4 {} = true := by
  native_decide

example : ∀ rho : Nat → ℝ, unitParameterBox.envMem rho →
    (∀ i, i ≥ unitParameterBox.length → rho i = 0) →
    (Engine.Algebra.cubicZeroSet (oneRootFamily.at rho)).ncard = 1 := by
  exact verify_cubic_root_count_subdiv oneRootFamily unitParameterBox .one 4 {}
    (by native_decide)

-- Degenerate cubics are rejected even when the discriminant interval itself
-- happens to have the requested sign.
def degenerate : CubicFamily where
  a := .const 0
  b := .const 1
  c := .const 0
  d := .const (-1)

example : cubicCountCheckBox degenerate [] .three {} = false := by native_decide

end LeanCert.Test.CubicCount
