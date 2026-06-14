/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.AffineBounds

/-!
# Affine cover certificates for interval lower bounds

`interval_bound_subdiv` uses the plain interval backend and only handles bounds
against a rational constant.  For dependency-heavy transcendental comparisons
(e.g. `error term ≤ admissible curve`, where the curve is `polynomial · exp`),
the plain interval product is too loose even under subdivision, but the affine
backend — which tracks linear correlations between subterms — is tight on each
small piece.

This module packages "subdivide, check each piece with the affine backend" as a
single boolean cover checker plus a golden theorem, in the same checker +
soundness style as the rest of LeanCert.  The intended consumer is a comparison
`∀ x ∈ [a,b], f x ≤ g x`, reduced to `0 ≤ (g - f) x` and covered.
-/

namespace LeanCert.Validity

open LeanCert.Core LeanCert.Engine

/-- Check that `c ≤ e` on every consecutive piece `[lo, b₀], [b₀, b₁], …` of a
partition, using the strict affine single-interval backend.  Pieces with a
non-ordered endpoint are rejected. -/
def checkLowerAffineCover (e : Expr) (c : ℚ) (cfg : AffineConfig) :
    ℚ → List ℚ → Bool
  | _, [] => true
  | lo, hi :: rest =>
      (if h : lo ≤ hi then checkLowerBoundAffine1Strict e ⟨lo, hi, h⟩ c cfg
        else false)
      && checkLowerAffineCover e c cfg hi rest

/-- Golden theorem: a successful affine cover proves `c ≤ e` on the whole
interval `[lo, last]`, where `last` is the final breakpoint. -/
theorem verify_lower_affine_cover (e : Expr) (hsupp : ExprSupportedCore e)
    (c : ℚ) (cfg : AffineConfig) :
    ∀ (lo : ℚ) (bps : List ℚ) (hbps : bps ≠ []),
      checkLowerAffineCover e c cfg lo bps = true →
      ∀ x ∈ Set.Icc (lo : ℝ) ((bps.getLast hbps : ℚ) : ℝ),
        (c : ℝ) ≤ Expr.eval (fun _ => x) e := by
  intro lo bps
  induction bps generalizing lo with
  | nil => intro hbps; exact absurd rfl hbps
  | cons hi rest ih =>
    intro _ hcheck
    simp only [checkLowerAffineCover, Bool.and_eq_true] at hcheck
    obtain ⟨hpiece, hrest⟩ := hcheck
    -- the piece [lo, hi] must be ordered and pass the affine check
    have hle : lo ≤ hi := by
      by_contra h; simp [h] at hpiece
    rw [dif_pos hle] at hpiece
    have hleft := verify_lower_bound_affine1_strict e hsupp ⟨lo, hi, hle⟩ c cfg hpiece
    cases rest with
    | nil =>
      -- getLast [hi] = hi; goal is exactly [lo, hi]
      intro x hx
      simp only [List.getLast_singleton] at hx
      exact hleft x ((IntervalRat.mem_iff_mem_Icc _ _).mpr hx)
    | cons hd tl =>
      have hrestne : (hd :: tl) ≠ [] := by simp
      have hih := ih hi hrestne hrest
      intro x hx
      rw [List.getLast_cons hrestne] at hx
      obtain ⟨hxlo, hxhi⟩ := hx
      by_cases hxm : x ≤ (hi : ℝ)
      · exact hleft x ((IntervalRat.mem_iff_mem_Icc _ _).mpr ⟨hxlo, hxm⟩)
      · exact hih x ⟨le_of_lt (not_le.mp hxm), hxhi⟩

/-- Cover checker for a comparison `f ≤ g`: covers `g - f` against `0`. -/
def checkLeAffineCover (f g : Expr) (cfg : AffineConfig) (lo : ℚ) (bps : List ℚ) :
    Bool :=
  checkLowerAffineCover (Expr.sub g f) 0 cfg lo bps

/-- Golden theorem for affine comparison covers: a successful cover of `g - f`
proves `f ≤ g` on the whole interval `[lo, last]`.  This closes
dependency-heavy transcendental comparisons (e.g. `error ≤ admissible curve`)
that the plain interval backend is too loose for even under subdivision. -/
theorem verify_le_affine_cover (f g : Expr)
    (hsupp : ExprSupportedCore (Expr.sub g f)) (cfg : AffineConfig)
    (lo : ℚ) (bps : List ℚ) (hbps : bps ≠ [])
    (hcheck : checkLeAffineCover f g cfg lo bps = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) ((bps.getLast hbps : ℚ) : ℝ),
      Expr.eval (fun _ => x) f ≤ Expr.eval (fun _ => x) g := by
  intro x hx
  have h := verify_lower_affine_cover (Expr.sub g f) hsupp 0 cfg lo bps hbps hcheck x hx
  simp only [Expr.sub, Expr.eval_add, Expr.eval_neg, Rat.cast_zero] at h
  linarith

end LeanCert.Validity
