/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.QProduct

/-!
# ConstantFactory

Finite observer certificates for q-product constants.

The first layer reuses the exact `QProduct` moment checker.  A base exponent set
`R` supplies the kernel bank

`moment R m = ∫ u in 0..1, qProd R u * u^m`,

and a finite perturbation set `Q` supplies signed subset-sum coefficients.  The
main theorem says that, when `R` and `Q` are disjoint, the product integral for
`R ∪ Q` is exactly the finite observer sum over moments of `R`.
-/

namespace LeanCert.ConstantFactory

open scoped BigOperators
open LeanCert.QProduct

/-- Exact rational observer sum for the perturbation `Q` around a base `R`. -/
def observerIntegralRat (R Q : Finset Nat) : ℚ :=
  ∑ A ∈ Q.powerset, subsetSign A * momentRat R (subsetWeight A)

/-- Real observer sum, useful as the semantic bridge before using exact rationals. -/
noncomputable def observerIntegral (R Q : Finset Nat) : ℝ :=
  ∑ A ∈ Q.powerset, (subsetSign A : ℝ) * moment R (subsetWeight A)

/-- Exact observer sum computes the semantic observer sum. -/
theorem observerIntegralRat_correct (R Q : Finset Nat) :
    (observerIntegralRat R Q : ℝ) = observerIntegral R Q := by
  classical
  unfold observerIntegralRat observerIntegral
  simp_rw [Rat.cast_sum, Rat.cast_mul, momentRat_correct]

private theorem continuous_qProd (S : Finset Nat) :
    Continuous fun u : ℝ => qProd S u := by
  classical
  refine Finset.induction_on S ?empty ?insert
  · simpa [qProd] using (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
  · intro n S hn hS
    have hfactor : Continuous fun u : ℝ => 1 - u ^ n :=
      continuous_const.sub (continuous_id.pow n)
    simpa [qProd, Finset.prod_insert hn] using! hfactor.mul hS

/-- Observer algebra identity at the integrand level. -/
theorem qProd_union_eq_observer_sum (R Q : Finset Nat) (hdisj : Disjoint R Q)
    (u : ℝ) :
    qProd (R ∪ Q) u =
      ∑ A ∈ Q.powerset,
        (subsetSign A : ℝ) * (qProd R u * u ^ subsetWeight A) := by
  classical
  rw [qProd, Finset.prod_union hdisj]
  change qProd R u * qProd Q u =
    ∑ A ∈ Q.powerset,
      (subsetSign A : ℝ) * (qProd R u * u ^ subsetWeight A)
  rw [qProd_powerset_expand Q u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  ring

/--
Semantic ConstantFactory identity.

After the base kernel `R` is known, every disjoint finite perturbation `Q`
reduces to a finite signed sum of moments of `R`.
-/
theorem F_union_eq_observerIntegral (R Q : Finset Nat) (hdisj : Disjoint R Q) :
    F (R ∪ Q) = observerIntegral R Q := by
  classical
  unfold F observerIntegral moment
  simp_rw [qProd_union_eq_observer_sum R Q hdisj]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [intervalIntegral.integral_const_mul]
  · intro A hA
    have hcont :
        Continuous fun u : ℝ =>
          (subsetSign A : ℝ) * (qProd R u * u ^ subsetWeight A) :=
      continuous_const.mul
        ((continuous_qProd R).mul (continuous_id.pow (subsetWeight A)))
    exact hcont.intervalIntegrable 0 1

/-- Exact rational ConstantFactory identity. -/
theorem observerIntegralRat_eq_F_union (R Q : Finset Nat) (hdisj : Disjoint R Q) :
    (observerIntegralRat R Q : ℝ) = F (R ∪ Q) := by
  rw [observerIntegralRat_correct, ← F_union_eq_observerIntegral R Q hdisj]

/-- Exact interval checker for a ConstantFactory observer certificate. -/
def checkConstantFactoryInterval (R Q : Finset Nat) (lo hi : ℚ) : Bool :=
  decide (Disjoint R Q ∧
    lo ≤ observerIntegralRat R Q ∧
      observerIntegralRat R Q ≤ hi)

/-- Golden theorem for exact ConstantFactory interval certificates. -/
theorem verify_constantFactory_interval (R Q : Finset Nat) (lo hi : ℚ)
    (hcheck : checkConstantFactoryInterval R Q lo hi = true) :
    (lo : ℝ) ≤ F (R ∪ Q) ∧ F (R ∪ Q) ≤ (hi : ℝ) := by
  simp only [checkConstantFactoryInterval, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hdisj, hlo, hhi⟩
  rw [← observerIntegralRat_eq_F_union R Q hdisj]
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- Exact upper-bound checker for a ConstantFactory observer certificate. -/
def checkConstantFactoryUpper (R Q : Finset Nat) (hi : ℚ) : Bool :=
  decide (Disjoint R Q ∧ observerIntegralRat R Q ≤ hi)

/-- Exact lower-bound checker for a ConstantFactory observer certificate. -/
def checkConstantFactoryLower (R Q : Finset Nat) (lo : ℚ) : Bool :=
  decide (Disjoint R Q ∧ lo ≤ observerIntegralRat R Q)

/-- Golden theorem for exact ConstantFactory upper-bound certificates. -/
theorem verify_constantFactory_upper (R Q : Finset Nat) (hi : ℚ)
    (hcheck : checkConstantFactoryUpper R Q hi = true) :
    F (R ∪ Q) ≤ (hi : ℝ) := by
  simp only [checkConstantFactoryUpper, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hdisj, hhi⟩
  rw [← observerIntegralRat_eq_F_union R Q hdisj]
  exact_mod_cast hhi

/-- Golden theorem for exact ConstantFactory lower-bound certificates. -/
theorem verify_constantFactory_lower (R Q : Finset Nat) (lo : ℚ)
    (hcheck : checkConstantFactoryLower R Q lo = true) :
    (lo : ℝ) ≤ F (R ∪ Q) := by
  simp only [checkConstantFactoryLower, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hdisj, hlo⟩
  rw [← observerIntegralRat_eq_F_union R Q hdisj]
  exact_mod_cast hlo

end LeanCert.ConstantFactory
