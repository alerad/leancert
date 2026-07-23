/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Executable exact rational polynomials

`Polynomial ℚ` is the semantic representation used by Mathlib, but its sparse
implementation is not a suitable native certificate payload. `QPoly` stores
ascending coefficients in an `Array ℚ` and supplies a small exact executable
kernel. The `toPoly` lemmas connect successful computations to Mathlib.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-- An exact executable rational polynomial.

`coeffs[i]` is the coefficient of `x^i`. Trailing zero coefficients are
allowed; use `trim` when a canonical certificate representation is useful. -/
structure QPoly where
  coeffs : Array ℚ
  deriving DecidableEq, Repr, Inhabited

namespace QPoly

private def addCoeffs : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addCoeffs xs ys

private def scaleCoeffs (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | x :: xs => (c * x) :: scaleCoeffs c xs

private def mulCoeffs : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: xs, ys => addCoeffs (scaleCoeffs x ys) (0 :: mulCoeffs xs ys)

/-- Remove trailing zero coefficients. -/
private def trimCoeffs : List ℚ → List ℚ
  | [] => []
  | x :: xs =>
      match trimCoeffs xs with
      | [] => if x = 0 then [] else [x]
      | y :: ys => x :: y :: ys

private def weightedDerivativeCoeffs (n : Nat) : List ℚ → List ℚ
  | [] => []
  | x :: xs => ((n : ℚ) * x) :: weightedDerivativeCoeffs (n + 1) xs

/-- Formal derivative on ascending coefficients. -/
private def derivativeCoeffs : List ℚ → List ℚ
  | [] => []
  | _ :: xs => weightedDerivativeCoeffs 1 xs

private def antiderivativeCoeffs (n : Nat) : List ℚ → List ℚ
  | [] => []
  | x :: xs => (x / (n : ℚ)) :: antiderivativeCoeffs (n + 1) xs

private def evalCoeffs (x : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: cs => c + x * evalCoeffs x cs

private noncomputable def listToPoly : List ℚ → Polynomial ℚ
  | [] => 0
  | x :: xs => Polynomial.C x + Polynomial.X * listToPoly xs

/-- The semantic Mathlib polynomial represented by an executable `QPoly`. -/
noncomputable def toPoly (p : QPoly) : Polynomial ℚ :=
  listToPoly p.coeffs.toList

def zero : QPoly := ⟨#[]⟩

def constant (c : ℚ) : QPoly := ⟨#[c]⟩

/-- The polynomial variable. -/
def X : QPoly := ⟨#[0, 1]⟩

def add (p q : QPoly) : QPoly :=
  ⟨(addCoeffs p.coeffs.toList q.coeffs.toList).toArray⟩

def mul (p q : QPoly) : QPoly :=
  ⟨(mulCoeffs p.coeffs.toList q.coeffs.toList).toArray⟩

def derivative (p : QPoly) : QPoly :=
  ⟨(trimCoeffs (derivativeCoeffs p.coeffs.toList)).toArray⟩

/-- The exact rational antiderivative with constant coefficient zero. -/
def antiderivative (p : QPoly) : QPoly :=
  ⟨(0 :: antiderivativeCoeffs 1 p.coeffs.toList).toArray⟩

/-- Exact Horner evaluation over the rationals. -/
def evalRat (p : QPoly) (x : ℚ) : ℚ :=
  evalCoeffs x p.coeffs.toList

/-- Exact definite integral between rational endpoints. -/
def integralRat (p : QPoly) (a b : ℚ) : ℚ :=
  p.antiderivative.evalRat b - p.antiderivative.evalRat a

def trim (p : QPoly) : QPoly :=
  ⟨(trimCoeffs p.coeffs.toList).toArray⟩

private theorem listToPoly_addCoeffs (xs ys : List ℚ) :
    listToPoly (addCoeffs xs ys) = listToPoly xs + listToPoly ys := by
  induction xs generalizing ys with
  | nil => simp [addCoeffs, listToPoly]
  | cons x xs ih =>
      cases ys with
      | nil => simp [addCoeffs, listToPoly]
      | cons y ys =>
          simp only [addCoeffs, listToPoly, ih, map_add]
          ring

private theorem listToPoly_scaleCoeffs (c : ℚ) (xs : List ℚ) :
    listToPoly (scaleCoeffs c xs) = Polynomial.C c * listToPoly xs := by
  induction xs with
  | nil => simp [scaleCoeffs, listToPoly]
  | cons x xs ih =>
      simp only [scaleCoeffs, listToPoly, ih, map_mul]
      ring

private theorem listToPoly_mulCoeffs (xs ys : List ℚ) :
    listToPoly (mulCoeffs xs ys) = listToPoly xs * listToPoly ys := by
  induction xs with
  | nil => simp [mulCoeffs, listToPoly]
  | cons x xs ih =>
      rw [mulCoeffs, listToPoly_addCoeffs, listToPoly_scaleCoeffs]
      simp only [listToPoly, ih, map_zero]
      ring

private theorem listToPoly_trimCoeffs (xs : List ℚ) :
    listToPoly (trimCoeffs xs) = listToPoly xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [trimCoeffs]
      split
      next htrim =>
        by_cases hx : x = 0
        · simp [hx, listToPoly, ← ih, htrim]
        · simp [hx, listToPoly, ← ih, htrim]
      next y ys htrim =>
        simp [listToPoly, ← ih, htrim]

private theorem listToPoly_weightedDerivativeCoeffs (n : Nat) (xs : List ℚ) :
    listToPoly (weightedDerivativeCoeffs n xs) =
      Polynomial.C (n : ℚ) * listToPoly xs +
        Polynomial.X * (listToPoly xs).derivative := by
  induction xs generalizing n with
  | nil => simp [weightedDerivativeCoeffs, listToPoly]
  | cons x xs ih =>
      simp only [weightedDerivativeCoeffs, listToPoly, ih,
        Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, map_mul]
      push_cast
      simp only [map_add, map_one]
      ring

private theorem listToPoly_derivativeCoeffs (xs : List ℚ) :
    listToPoly (derivativeCoeffs xs) = (listToPoly xs).derivative := by
  cases xs with
  | nil => simp [derivativeCoeffs, listToPoly]
  | cons x xs =>
      rw [derivativeCoeffs, listToPoly_weightedDerivativeCoeffs]
      simp only [listToPoly, Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X]
      norm_num [Polynomial.C_1]

private theorem weightedDerivativeCoeffs_antiderivativeCoeffs
    (xs : List ℚ) (n : Nat) (hn : 0 < n) :
    weightedDerivativeCoeffs n (antiderivativeCoeffs n xs) = xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
      simp only [antiderivativeCoeffs, weightedDerivativeCoeffs, List.cons.injEq]
      constructor
      · field_simp
      · exact ih (n + 1) (by omega)

@[simp] theorem toPoly_zero : zero.toPoly = 0 := by
  rfl

@[simp] theorem toPoly_constant (c : ℚ) : (constant c).toPoly = Polynomial.C c := by
  simp [constant, toPoly, listToPoly]

@[simp] theorem toPoly_X : X.toPoly = Polynomial.X := by
  simp [X, toPoly, listToPoly]

theorem toPoly_add (p q : QPoly) : (p.add q).toPoly = p.toPoly + q.toPoly := by
  simpa [add, toPoly] using listToPoly_addCoeffs p.coeffs.toList q.coeffs.toList

theorem toPoly_mul (p q : QPoly) : (p.mul q).toPoly = p.toPoly * q.toPoly := by
  simpa [mul, toPoly] using listToPoly_mulCoeffs p.coeffs.toList q.coeffs.toList

theorem toPoly_derivative (p : QPoly) : p.derivative.toPoly = p.toPoly.derivative := by
  simpa [derivative, toPoly, listToPoly_trimCoeffs] using
    listToPoly_derivativeCoeffs p.coeffs.toList

theorem toPoly_antiderivative_derivative (p : QPoly) :
    p.antiderivative.toPoly.derivative = p.toPoly := by
  rw [← toPoly_derivative]
  simp only [derivative, antiderivative, derivativeCoeffs,
    weightedDerivativeCoeffs_antiderivativeCoeffs _ 1 (by omega), toPoly,
    listToPoly_trimCoeffs]

theorem toPoly_trim (p : QPoly) : p.trim.toPoly = p.toPoly := by
  simpa [trim, toPoly] using listToPoly_trimCoeffs p.coeffs.toList

private def listToExpr : List ℚ → Expr
  | [] => .const 0
  | x :: xs => .add (.const x) (.mul (.var 0) (listToExpr xs))

/-- Convert to a single-variable Horner expression in variable `0`. -/
def toExpr (p : QPoly) : Expr :=
  listToExpr p.coeffs.toList

private theorem eval_listToExpr (xs : List ℚ) (x : ℝ) :
    Expr.eval (fun _ => x) (listToExpr xs) = Polynomial.aeval x (listToPoly xs) := by
  induction xs with
  | nil => simp [listToExpr, listToPoly]
  | cons q qs ih =>
      simp only [listToExpr, listToPoly, Expr.eval, ih, map_add, map_mul,
        Polynomial.aeval_C, Polynomial.aeval_X]
      rfl

/-- The Horner `Expr` and Mathlib polynomial have identical real semantics. -/
theorem eval_toExpr (p : QPoly) (x : ℝ) :
    Expr.eval (fun _ => x) p.toExpr = Polynomial.aeval x p.toPoly := by
  exact eval_listToExpr p.coeffs.toList x

private theorem cast_evalCoeffs (xs : List ℚ) (x : ℚ) :
    ((evalCoeffs x xs : ℚ) : ℝ) = Expr.eval (fun _ => (x : ℝ)) (listToExpr xs) := by
  induction xs with
  | nil => simp [evalCoeffs, listToExpr]
  | cons c cs ih => simp [evalCoeffs, listToExpr, Expr.eval, ih]

theorem cast_evalRat (p : QPoly) (x : ℚ) :
    ((p.evalRat x : ℚ) : ℝ) = Expr.eval (fun _ => (x : ℝ)) p.toExpr := by
  exact cast_evalCoeffs p.coeffs.toList x

/-- The executable exact integral agrees with the interval integral of the
represented polynomial. -/
theorem integral_eval_toExpr (p : QPoly) (a b : ℚ) :
    (∫ x in (a : ℝ)..(b : ℝ), Expr.eval (fun _ => x) p.toExpr) =
      (p.integralRat a b : ℝ) := by
  let q := p.antiderivative
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t => Expr.eval (fun _ => t) q.toExpr)
        (Expr.eval (fun _ => x) p.toExpr) x := by
    intro x
    have hq : q.toPoly.derivative = p.toPoly :=
      toPoly_antiderivative_derivative p
    have h := q.toPoly.hasDerivAt_aeval x
    rw [hq] at h
    simpa only [eval_toExpr] using h
  have hInt : IntervalIntegrable
      (fun x => Expr.eval (fun _ => x) p.toExpr) MeasureTheory.volume (a : ℝ) (b : ℝ) := by
    rw [show (fun x : ℝ => Expr.eval (fun _ => x) p.toExpr) =
        (fun x : ℝ => Polynomial.aeval x p.toPoly) by
      funext x
      exact eval_toExpr p x]
    exact p.toPoly.differentiable_aeval.continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    hInt]
  simp only [q, integralRat]
  rw [← cast_evalRat p.antiderivative b, ← cast_evalRat p.antiderivative a]
  norm_num

/-- The analytic derivative of the Horner expression agrees with the formal
polynomial derivative. -/
theorem deriv_eval_toExpr (p : QPoly) (x : ℝ) :
    deriv (fun t : ℝ => Expr.eval (fun _ => t) p.toExpr) x =
      Polynomial.aeval x p.toPoly.derivative := by
  rw [show (fun t : ℝ => Expr.eval (fun _ => t) p.toExpr) =
      (fun t : ℝ => Polynomial.aeval t p.toPoly) by
    funext t
    exact eval_toExpr p t]
  exact (p.toPoly.hasDerivAt_aeval x).deriv

end QPoly
end LeanCert.Engine
