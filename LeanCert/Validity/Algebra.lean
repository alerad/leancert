/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.Bezout
import LeanCert.Validity.Algebra.CubicIsolation

/-!
# Golden theorems for algebraic root certificates

Stable wrappers turn a successful executable Bézout check into the common
semantic goal shapes: separability, squarefreeness, coprimality with the formal
derivative, and simplicity of every real root. They also expose uniform
real-root counts for parametric cubic families whose leading coefficient and
discriminant signs are certified by interval arithmetic.
-/

namespace LeanCert.Validity.Algebra

open LeanCert.Core
open LeanCert.Engine

/-- A checked Bézout identity certifies separability. -/
theorem verify_separable (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) : P.toPoly.Separable :=
  bezoutCheck_sound P cert h

/-- A checked Bézout identity certifies squarefreeness. -/
theorem verify_squarefree (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) : Squarefree P.toPoly :=
  (verify_separable P cert h).squarefree

/-- A checked Bézout identity certifies that `P` and `P'` are coprime. -/
theorem verify_coprime_deriv (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    IsCoprime P.toPoly P.toPoly.derivative :=
  (Polynomial.separable_def P.toPoly).mp (verify_separable P cert h)

/-- Every real root of a polynomial with a checked Bézout certificate is
simple, stated using Mathlib polynomial evaluation. -/
theorem verify_real_roots_simple (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    ∀ x : ℝ, Polynomial.aeval x P.toPoly = 0 →
      Polynomial.aeval x P.toPoly.derivative ≠ 0 := by
  intro x hx
  exact (verify_separable P cert h).aeval_derivative_ne_zero hx

/-- Simplicity in the form consumed by LeanCert's analytic `Expr` layer. -/
theorem verify_toExpr_roots_simple (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    ∀ x : ℝ, Expr.eval (fun _ => x) P.toExpr = 0 →
      deriv (fun t : ℝ => Expr.eval (fun _ => t) P.toExpr) x ≠ 0 := by
  intro x hx
  rw [QPoly.eval_toExpr] at hx
  rw [QPoly.deriv_eval_toExpr]
  exact verify_real_roots_simple P cert h x hx

/-- A successful one-box discriminant check proves the requested number of
real roots for every parameter environment in the box. -/
theorem verify_cubic_root_count (P : CubicFamily) (B : Optimization.Box)
    (count : CubicRootCount) (cfg : EvalConfig)
    (h : cubicCountCheckBox P B count cfg = true) :
    ∀ rho : Nat → ℝ, B.envMem rho →
      (∀ i, i ≥ B.length → rho i = 0) →
      (Engine.Algebra.cubicZeroSet (P.at rho)).ncard = count.toNat :=
  cubicCountCheckBox_sound P B count cfg h

/-- A successful adaptive discriminant check proves the requested uniform
real-root count, including when subdivision is needed to resolve dependency. -/
theorem verify_cubic_root_count_subdiv (P : CubicFamily) (B : Optimization.Box)
    (count : CubicRootCount) (maxDepth : Nat) (cfg : EvalConfig)
    (h : cubicCountCheckSubdiv P B count maxDepth cfg = true) :
    ∀ rho : Nat → ℝ, B.envMem rho →
      (∀ i, i ≥ B.length → rho i = 0) →
      (Engine.Algebra.cubicZeroSet (P.at rho)).ncard = count.toNat :=
  cubicCountCheckSubdiv_sound P B count maxDepth cfg h

/-- Every real root of an exact rational cubic lies in its executable Cauchy
radius. -/
theorem verify_cubic_root_radius (P : QCubic) (ha : P.a ≠ 0) {x : ℝ}
    (hx : x ∈ Engine.Algebra.cubicZeroSet P.toReal) : |x| ≤ P.cauchyRadius :=
  P.root_abs_le_cauchyRadius ha hx

/-- A successful mesh check gives a strict lower bound on all three pairwise
root gaps. -/
theorem verify_cubic_separation_mesh (P : QCubic) {eps : ℚ} {x y z : ℝ}
    (hcheck : P.separationMeshCheck eps = true)
    (hroots : P.toReal.roots = {x, y, z}) :
    (eps : ℝ) < |x - y| ∧ (eps : ℝ) < |x - z| ∧ (eps : ℝ) < |y - z| :=
  P.separationMeshCheck_sound hcheck hroots

/-- Ergonomic separation theorem for any two distinct real roots, avoiding an
explicit root-multiset enumeration. -/
theorem verify_cubic_distinct_roots_separated (P : QCubic) {eps : ℚ}
    (hcount : P.threeRootCountCheck = true)
    (hmesh : P.separationMeshCheck eps = true) {x y : ℝ}
    (hx : x ∈ Engine.Algebra.cubicZeroSet P.toReal)
    (hy : y ∈ Engine.Algebra.cubicZeroSet P.toReal) (hxy : x ≠ y) :
    (eps : ℝ) < |x - y| :=
  P.separationMeshCheck_sound_of_distinct_roots hcount hmesh hx hy hxy

end LeanCert.Validity.Algebra
