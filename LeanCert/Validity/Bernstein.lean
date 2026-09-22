/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.QPolyBernstein
import LeanCert.Engine.Algebra.QPolyIntegral

/-!
# Golden theorems for Bernstein polynomial certificates

`checkPolyLowerBound e I c depth` recognises `e` as a univariate rational
polynomial (`QPoly.ofExpr`) and runs the recursive Bernstein certificate
`QPoly.bernsteinCheck`. Recognition doubles as the support proof, so the golden
theorems need no `ExprSupportedCore` premise. All theorems here are kernel-clean;
the checker itself may be closed by kernel or native evaluation.
-/

namespace LeanCert.Validity.Bernstein

open LeanCert.Core LeanCert.Engine

/-- Generic Bernstein checker over reified expressions. -/
def checkPolyBound (cmp : QPoly.Cmp) (e : Expr) (I : IntervalRat) (c : ℚ)
    (depth : Nat) : Bool :=
  match QPoly.ofExpr e with
  | some p => QPoly.bernsteinCheck cmp p c I depth
  | none => false

/-- `∀ x ∈ I, c ≤ e x` by Bernstein coefficients. -/
def checkPolyLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .lower e I c depth

/-- `∀ x ∈ I, e x ≤ c` by Bernstein coefficients. -/
def checkPolyUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .upper e I c depth

/-- `∀ x ∈ I, c < e x` by Bernstein coefficients. -/
def checkPolyStrictLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .strictLower e I c depth

/-- `∀ x ∈ I, e x < c` by Bernstein coefficients. -/
def checkPolyStrictUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .strictUpper e I c depth

/-- Does `QPoly.ofExpr` recognise `e`? Used by tactics to decide applicability
without spending budget. -/
def isPolynomial (e : Expr) : Bool :=
  (QPoly.ofExpr e).isSome

theorem verify_poly_bound (cmp : QPoly.Cmp) (e : Expr) (I : IntervalRat) (c : ℚ)
    (depth : Nat) (h : checkPolyBound cmp e I c depth = true) :
    ∀ x ∈ I, cmp.holds c (Expr.eval (fun _ => x) e) := by
  unfold checkPolyBound at h
  cases hpoly : QPoly.ofExpr e with
  | none => simp [hpoly] at h
  | some p =>
      rw [hpoly] at h
      intro x hx
      rw [QPoly.ofExpr_correct hpoly, QPoly.eval_toExpr]
      exact QPoly.bernsteinCheck_sound h x hx

/-- **Golden theorem (lower bound).** -/
theorem verify_poly_lower_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyLowerBound e I c depth = true) :
    ∀ x ∈ I, (c : ℝ) ≤ Expr.eval (fun _ => x) e :=
  verify_poly_bound .lower e I c depth h

/-- **Golden theorem (upper bound).** -/
theorem verify_poly_upper_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyUpperBound e I c depth = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ (c : ℝ) :=
  verify_poly_bound .upper e I c depth h

/-- **Golden theorem (strict lower bound).** -/
theorem verify_poly_strict_lower_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyStrictLowerBound e I c depth = true) :
    ∀ x ∈ I, (c : ℝ) < Expr.eval (fun _ => x) e :=
  verify_poly_bound .strictLower e I c depth h

/-- **Golden theorem (strict upper bound).** -/
theorem verify_poly_strict_upper_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyStrictUpperBound e I c depth = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < (c : ℝ) :=
  verify_poly_bound .strictUpper e I c depth h

/-! ### `Set.Icc` bridges -/

theorem verify_poly_lower_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyLowerBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, (c : ℝ) ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  exact verify_poly_lower_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

theorem verify_poly_upper_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyUpperBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  intro x hx
  exact verify_poly_upper_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

theorem verify_poly_strict_lower_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyStrictLowerBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, (c : ℝ) < Expr.eval (fun _ => x) e := by
  intro x hx
  exact verify_poly_strict_lower_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

theorem verify_poly_strict_upper_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyStrictUpperBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e < (c : ℝ) := by
  intro x hx
  exact verify_poly_strict_upper_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

end LeanCert.Validity.Bernstein
