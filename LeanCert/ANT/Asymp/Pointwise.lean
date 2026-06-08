/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.ANT.Asymp.Env

/-!
# Pointwise error envelopes

`AsympEnv` is the canonical envelope type for summatory arithmetic functions.
This module adds the sibling type for ordinary real-variable estimates:

`|f x - main x| ≤ error x` on a domain.

The conversion from `AsympEnv` uses the existing floored real-endpoint
semantics, so later explicit-PNT transfer functors can consume either discrete
summatory envelopes or genuine real-variable envelopes without duplicating the
core absolute-error algebra.
-/

namespace LeanCert.ANT.Asymp

/-- A pointwise real-variable error envelope. -/
structure PointwiseEnvelope where
  /-- Function being bounded. -/
  f : ℝ → ℝ
  /-- Main approximation term. -/
  main : ℝ → ℝ
  /-- Nonnegative error radius. -/
  error : ℝ → ℝ
  /-- Domain on which the envelope is valid. -/
  domain : Set ℝ
  /-- Absolute-error certificate. -/
  cert : ∀ x ∈ domain, |f x - main x| ≤ error x
  /-- Error radius is nonnegative on the domain. -/
  error_nonneg : ∀ x ∈ domain, 0 ≤ error x

namespace PointwiseEnvelope

/-- Lower endpoint induced by a pointwise envelope. -/
noncomputable def lower (E : PointwiseEnvelope) (x : ℝ) : ℝ :=
  E.main x - E.error x

/-- Upper endpoint induced by a pointwise envelope. -/
noncomputable def upper (E : PointwiseEnvelope) (x : ℝ) : ℝ :=
  E.main x + E.error x

/-- A pointwise envelope as a lower bound. -/
theorem lower_le_value (E : PointwiseEnvelope) {x : ℝ} (hx : x ∈ E.domain) :
    E.lower x ≤ E.f x := by
  unfold lower
  have h := E.cert x hx
  have hneg : -E.error x ≤ E.f x - E.main x := neg_le_of_abs_le h
  linarith

/-- A pointwise envelope as an upper bound. -/
theorem value_le_upper (E : PointwiseEnvelope) {x : ℝ} (hx : x ∈ E.domain) :
    E.f x ≤ E.upper x := by
  unfold upper
  have h := E.cert x hx
  have hpos : E.f x - E.main x ≤ E.error x := le_of_abs_le h
  linarith

/-- Weaken a pointwise envelope to a larger error term. -/
noncomputable def weakenError (E : PointwiseEnvelope) (newError : ℝ → ℝ)
    (hnew : ∀ x ∈ E.domain, E.error x ≤ newError x) :
    PointwiseEnvelope where
  f := E.f
  main := E.main
  error := newError
  domain := E.domain
  cert := by
    intro x hx
    exact (E.cert x hx).trans (hnew x hx)
  error_nonneg := by
    intro x hx
    exact (E.error_nonneg x hx).trans (hnew x hx)

/-- Sum of two pointwise envelopes on their common domain. -/
noncomputable def add (E G : PointwiseEnvelope) : PointwiseEnvelope where
  f := fun x => E.f x + G.f x
  main := fun x => E.main x + G.main x
  error := fun x => E.error x + G.error x
  domain := E.domain ∩ G.domain
  cert := by
    intro x hx
    rcases hx with ⟨hE, hG⟩
    have hEcert := E.cert x hE
    have hGcert := G.cert x hG
    calc
      |(E.f x + G.f x) - (E.main x + G.main x)|
          = |(E.f x - E.main x) + (G.f x - G.main x)| := by ring_nf
      _ ≤ |E.f x - E.main x| + |G.f x - G.main x| := abs_add_le _ _
      _ ≤ E.error x + G.error x := add_le_add hEcert hGcert
  error_nonneg := by
    intro x hx
    exact add_nonneg (E.error_nonneg x hx.1) (G.error_nonneg x hx.2)

/-- Negation of a pointwise envelope. -/
noncomputable def neg (E : PointwiseEnvelope) : PointwiseEnvelope where
  f := fun x => -E.f x
  main := fun x => -E.main x
  error := E.error
  domain := E.domain
  cert := by
    intro x hx
    calc
      |-E.f x - -E.main x| = |E.f x - E.main x| := by
        have h : -E.f x - -E.main x = -(E.f x - E.main x) := by ring
        rw [h, abs_neg]
      _ ≤ E.error x := E.cert x hx
  error_nonneg := E.error_nonneg

/-- Difference of two pointwise envelopes on their common domain. -/
noncomputable def sub (E G : PointwiseEnvelope) : PointwiseEnvelope :=
  add E (neg G)

/-- Rational scalar multiplication of a pointwise envelope. -/
noncomputable def constMul (q : ℚ) (E : PointwiseEnvelope) : PointwiseEnvelope where
  f := fun x => (q : ℝ) * E.f x
  main := fun x => (q : ℝ) * E.main x
  error := fun x => ((|q| : ℚ) : ℝ) * E.error x
  domain := E.domain
  cert := by
    intro x hx
    have hE := E.cert x hx
    calc
      |(q : ℝ) * E.f x - (q : ℝ) * E.main x|
          = |(q : ℝ) * (E.f x - E.main x)| := by ring_nf
      _ = |(q : ℝ)| * |E.f x - E.main x| := abs_mul _ _
      _ = ((|q| : ℚ) : ℝ) * |E.f x - E.main x| := by rw [Rat.cast_abs]
      _ ≤ ((|q| : ℚ) : ℝ) * E.error x := by
        exact mul_le_mul_of_nonneg_left hE (by exact_mod_cast abs_nonneg q)
  error_nonneg := by
    intro x hx
    exact mul_nonneg (by exact_mod_cast abs_nonneg q) (E.error_nonneg x hx)

end PointwiseEnvelope

namespace AsympEnv

/--
Convert a discrete summatory envelope to a pointwise envelope using the existing
floored real-endpoint semantics.
-/
noncomputable def toPointwiseFloorEnvelope (A : AsympEnv) : PointwiseEnvelope where
  f := A.summatoryReal
  main := fun x => evalAtNat A.mainTerm ⌊x⌋₊
  error := fun x => evalAtNat A.errorTerm ⌊x⌋₊
  domain := {x | A.cutoff ≤ ⌊x⌋₊}
  cert := by
    intro x hx
    exact A.certReal x hx
  error_nonneg := by
    intro x hx
    exact A.error_nonneg ⌊x⌋₊ hx

theorem toPointwiseFloorEnvelope_cert (A : AsympEnv) :
    ∀ x ∈ (A.toPointwiseFloorEnvelope).domain,
      |(A.toPointwiseFloorEnvelope).f x -
          (A.toPointwiseFloorEnvelope).main x| ≤
        (A.toPointwiseFloorEnvelope).error x :=
  A.toPointwiseFloorEnvelope.cert

end AsympEnv

end LeanCert.ANT.Asymp
