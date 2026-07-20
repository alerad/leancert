/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.Gradient

/-!
# Domain-aware automatic differentiation regressions

The checked API accepts reciprocal and logarithm nodes precisely when their
interval arguments certify the analytic domain conditions.  These tests cover
successful computation, structured rejection, nesting, multivariable use, and
the public soundness theorem.
-/

namespace LeanCert.Test.DomainAwareAD

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

def positive : IntervalRat := ⟨1, 2, by norm_num⟩
def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
def nonpositive : IntervalRat := ⟨-2, 0, by norm_num⟩

def positiveEnv : IntervalEnv := fun _ => positive
def crossesZeroEnv : IntervalEnv := fun _ => crossesZero
def nonpositiveEnv : IntervalEnv := fun _ => nonpositive

def reciprocal : Expr := .inv (.var 0)
def logarithm : Expr := .log (.var 0)
def nested : Expr := .log (.inv (.var 0))
def twoVariableLog : Expr := .log (.add (.var 0) (.var 1))

def succeeds {T : Type} (result : EvalResult T) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

def invalidPrecision {T : Type} (result : EvalResult T) : Bool :=
  match result with
  | .error (.invalidConfiguration _) => true
  | _ => false

#guard succeeds (derivIntervalChecked reciprocal positiveEnv 0)
#guard succeeds (derivIntervalChecked logarithm positiveEnv 0)
#guard succeeds (derivIntervalChecked nested positiveEnv 0)
#guard succeeds (gradientIntervalChecked twoVariableLog [positive, positive])

#guard derivIntervalChecked reciprocal crossesZeroEnv 0 =
  .error (.reciprocalContainsZero crossesZero)
#guard derivIntervalChecked logarithm nonpositiveEnv 0 =
  .error (.logNonpositive nonpositive)
#guard derivIntervalChecked (.log reciprocal) crossesZeroEnv 0 =
  .error (.nestedFailure "logarithm operand" (.reciprocalContainsZero crossesZero))
#guard derivIntervalChecked (.sqrt (.var 0)) positiveEnv 0 =
  .error (.unsupportedFeature "domain-aware automatic differentiation")

example (D : DualInterval) (x : ℝ) (hx : x ∈ positive)
    (hok : evalWithDerivChecked nested positiveEnv 0 {} = .ok D) :
    DifferentiableAt ℝ (Expr.evalAlong nested (fun _ => x) 0) x := by
  apply evalWithDerivChecked_differentiableAt nested (fun _ => x)
    positiveEnv 0 {} D x hx
  · intro i
    exact hx
  · exact hok

example (dI : IntervalRat) (x : ℝ) (hx : x ∈ positive)
    (hok : derivIntervalChecked nested positiveEnv 0 {} = .ok dI) :
    deriv (Expr.evalAlong nested (fun _ => x) 0) x ∈ dI := by
  apply derivIntervalChecked_correct nested (fun _ => x)
    positiveEnv 0 {} dI x hx
  · intro i
    exact hx
  · exact hok

#check gradientIntervalChecked_correct

/-! The same API shape is available with bounded-denominator Dyadic arithmetic. -/

def positiveDyadic : IntervalDyadic := IntervalDyadic.ofIntervalRat positive (-40)
def negativeDyadic : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨-2, -1, by norm_num⟩ (-40)
def crossesZeroDyadic : IntervalDyadic := IntervalDyadic.ofIntervalRat crossesZero (-40)
def positiveDyadicEnv : IntervalDyadicEnv := fun _ => positiveDyadic
def negativeDyadicEnv : IntervalDyadicEnv := fun _ => negativeDyadic
def crossesZeroDyadicEnv : IntervalDyadicEnv := fun _ => crossesZeroDyadic

#guard succeeds (derivIntervalDyadicChecked reciprocal positiveDyadicEnv 0)
#guard succeeds (derivIntervalDyadicChecked logarithm positiveDyadicEnv 0)
#guard succeeds (derivIntervalDyadicChecked nested positiveDyadicEnv 0)
#guard succeeds (derivIntervalDyadicChecked reciprocal negativeDyadicEnv 0)
#guard succeeds (gradientIntervalDyadicChecked twoVariableLog positiveDyadicEnv 2)
#guard succeeds (derivIntervalDyadicCheckedOfRat nested positiveEnv 0)
#guard succeeds (gradientIntervalDyadicCheckedOfRat twoVariableLog positiveEnv 2)
#guard succeeds (derivIntervalDyadicChecked (.log (.exp (.var 0))) negativeDyadicEnv 0
  { precision := -100, taylorDepth := 40 })

#guard !succeeds (derivIntervalDyadicChecked reciprocal crossesZeroDyadicEnv 0)
#guard !succeeds (derivIntervalDyadicChecked logarithm crossesZeroDyadicEnv 0)
#guard !succeeds (derivIntervalDyadicChecked logarithm negativeDyadicEnv 0)
#guard invalidPrecision
  (derivIntervalDyadicChecked reciprocal positiveDyadicEnv 0 { precision := 1 })
#guard !succeeds (derivIntervalDyadicChecked (.sqrt (.var 0)) positiveDyadicEnv 0)

example (D : DualIntervalDyadic) (x : ℝ) (hx : x ∈ positiveDyadic)
    (hok : evalWithDerivDyadicChecked nested positiveDyadicEnv 0 {} = .ok D) :
    DifferentiableAt ℝ (Expr.evalAlong nested (fun _ => x) 0) x := by
  apply evalWithDerivDyadicChecked_differentiableAt nested (fun _ => x)
    positiveDyadicEnv 0 {} D x hx
  · intro i
    exact hx
  · exact hok

example (dI : IntervalDyadic) (x : ℝ) (hx : x ∈ positiveDyadic)
    (hok : derivIntervalDyadicChecked nested positiveDyadicEnv 0 {} = .ok dI) :
    deriv (Expr.evalAlong nested (fun _ => x) 0) x ∈ dI := by
  apply derivIntervalDyadicChecked_correct nested (fun _ => x)
    positiveDyadicEnv 0 {} dI x hx
  · intro i
    exact hx
  · exact hok

#check gradientIntervalDyadicChecked_correct
#check derivIntervalDyadicCheckedOfRat_correct
#check gradientIntervalDyadicCheckedOfRat_correct

end LeanCert.Test.DomainAwareAD
