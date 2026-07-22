/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.Discriminant
import LeanCert.Engine.Eval.Extended
import LeanCert.Engine.Optimization.Box
import LeanCert.Engine.RootFinding.Basic

/-!
# Executable root-count certificates for parametric cubics

The coefficients of a cubic may be arbitrary `Expr`s in a parameter
environment.  A successful interval check proves that the leading coefficient
never vanishes and that the discriminant has a fixed strict sign throughout a
parameter box.  When direct interval evaluation is inconclusive, the recursive
checker bisects the widest parameter interval and checks both children.
-/

namespace LeanCert.Engine

open LeanCert.Core
open LeanCert.Engine.Algebra
open LeanCert.Engine.Optimization

/-- A cubic whose coefficients are expressions in a parameter environment. -/
structure CubicFamily where
  a : Expr
  b : Expr
  c : Expr
  d : Expr
  deriving Repr, DecidableEq, Inhabited

/-- The discriminant expression
`b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd`. -/
def CubicFamily.discrExpr (P : CubicFamily) : Expr :=
  .add
    (.add
      (.add
        (.mul (.pow P.b 2) (.pow P.c 2))
        (.neg (.mul (.const 4) (.mul P.a (.pow P.c 3)))))
      (.neg (.mul (.const 4) (.mul (.pow P.b 3) P.d))))
    (.add
      (.neg (.mul (.const 27) (.mul (.pow P.a 2) (.pow P.d 2))))
      (.mul (.const 18) (.mul P.a (.mul P.b (.mul P.c P.d)))))

/-- Specialize a coefficient family at a real parameter environment. -/
noncomputable def CubicFamily.at (P : CubicFamily) (rho : Nat → ℝ) : Cubic ℝ where
  a := Expr.eval rho P.a
  b := Expr.eval rho P.b
  c := Expr.eval rho P.c
  d := Expr.eval rho P.d

@[simp] theorem CubicFamily.discrExpr_eval (P : CubicFamily) (rho : Nat → ℝ) :
    Expr.eval rho P.discrExpr = (P.at rho).discr := by
  simp [CubicFamily.discrExpr, CubicFamily.at, Cubic.discr]
  ring

/-- The two nonsingular real-root counts available for cubics. -/
inductive CubicRootCount where
  | one
  | three
  deriving Repr, DecidableEq, Inhabited

def CubicRootCount.toNat : CubicRootCount → Nat
  | .one => 1
  | .three => 3

/-- Does an interval prove the strict discriminant sign for this count? -/
def intervalCertifiesCubicCount (count : CubicRootCount) (I : IntervalRat) : Bool :=
  match count with
  | .one => decide (I.hi < 0)
  | .three => decide (0 < I.lo)

/-- Check one parameter box. Evaluation failures and inconclusive intervals
return `false`; they never manufacture a finite enclosure. -/
def cubicCountCheckBox (P : CubicFamily) (B : Box) (count : CubicRootCount)
    (cfg : EvalConfig := {}) : Bool :=
  match evalIntervalTightChecked P.a B.toEnv cfg,
      evalIntervalTightChecked P.discrExpr B.toEnv cfg with
  | .ok Ia, .ok IΔ => excludesZero Ia && intervalCertifiesCubicCount count IΔ
  | _, _ => false

/-- Adaptive certificate checker. At positive depth it first tries the current
box, then bisects its widest dimension only when that direct check fails. -/
def cubicCountCheckSubdiv (P : CubicFamily) (B : Box) (count : CubicRootCount)
    (maxDepth : Nat) (cfg : EvalConfig := {}) : Bool :=
  match maxDepth with
  | 0 => cubicCountCheckBox P B count cfg
  | depth + 1 =>
      cubicCountCheckBox P B count cfg ||
        (cubicCountCheckSubdiv P (B.splitWidest).1 count depth cfg &&
          cubicCountCheckSubdiv P (B.splitWidest).2 count depth cfg)

private theorem Box.envMem_splitWidest_cases' (B : Box) (rho : Nat → ℝ)
    (hrho : B.envMem rho) :
    (B.splitWidest).1.envMem rho ∨ (B.splitWidest).2.envMem rho := by
  unfold Box.splitWidest
  by_cases hdim : B.widestDim < B.length
  · exact Box.envMem_split_cases B B.widestDim hdim rho hrho
  · simp [Box.split, hdim, hrho]

private theorem Box.splitWidest_fst_length' (B : Box) :
    (B.splitWidest).1.length = B.length := by
  unfold Box.splitWidest Box.split
  split <;> simp

private theorem Box.splitWidest_snd_length' (B : Box) :
    (B.splitWidest).2.length = B.length := by
  unfold Box.splitWidest Box.split
  split <;> simp

/-- Soundness of the one-box checker. -/
theorem cubicCountCheckBox_sound (P : CubicFamily) (B : Box)
    (count : CubicRootCount) (cfg : EvalConfig)
    (hcheck : cubicCountCheckBox P B count cfg = true) :
    ∀ rho : Nat → ℝ, B.envMem rho →
      (∀ i, i ≥ B.length → rho i = 0) →
      (cubicZeroSet (P.at rho)).ncard = count.toNat := by
  intro rho hrho hzero
  unfold cubicCountCheckBox at hcheck
  cases haeval : evalIntervalTightChecked P.a B.toEnv cfg with
  | error e => simp [haeval] at hcheck
  | ok Ia =>
      cases hΔeval : evalIntervalTightChecked P.discrExpr B.toEnv cfg with
      | error e => simp [haeval, hΔeval] at hcheck
      | ok IΔ =>
          simp only [haeval, hΔeval, Bool.and_eq_true] at hcheck
          have henv := Box.envMem_toEnv rho B hrho hzero
          have haMem := evalIntervalTightChecked_correct P.a B.toEnv cfg Ia haeval rho henv
          have hΔMem := evalIntervalTightChecked_correct P.discrExpr B.toEnv cfg IΔ hΔeval rho henv
          have ha : (P.at rho).a ≠ 0 := by
            simp only [CubicFamily.at]
            have hbounds := (IntervalRat.mem_def _ _).mp haMem
            have hexcl : excludesZero Ia = true := hcheck.1
            simp only [excludesZero, decide_eq_true_eq] at hexcl
            rcases hexcl with hneg | hpos
            · have hneg' : (Ia.hi : ℝ) < 0 := by exact_mod_cast hneg
              linarith
            · have hpos' : (0 : ℝ) < Ia.lo := by exact_mod_cast hpos
              linarith
          cases count with
          | one =>
              apply cubicZeroSet_ncard_eq_one_of_discr_neg (P.at rho) ha
              have hbounds := (IntervalRat.mem_def _ _).mp hΔMem
              simp only [intervalCertifiesCubicCount, decide_eq_true_eq] at hcheck
              have hhi : (IΔ.hi : ℝ) < 0 := by exact_mod_cast hcheck.2
              rw [← P.discrExpr_eval rho]
              linarith
          | three =>
              apply cubicZeroSet_ncard_eq_three_of_discr_pos (P.at rho) ha
              have hbounds := (IntervalRat.mem_def _ _).mp hΔMem
              simp only [intervalCertifiesCubicCount, decide_eq_true_eq] at hcheck
              have hlo : (0 : ℝ) < IΔ.lo := by exact_mod_cast hcheck.2
              rw [← P.discrExpr_eval rho]
              linarith

/-- Golden engine theorem: successful adaptive subdivision proves a uniform
fiberwise real-root count over the original parameter box. -/
theorem cubicCountCheckSubdiv_sound (P : CubicFamily) (B : Box)
    (count : CubicRootCount) (maxDepth : Nat) (cfg : EvalConfig)
    (hcheck : cubicCountCheckSubdiv P B count maxDepth cfg = true) :
    ∀ rho : Nat → ℝ, B.envMem rho →
      (∀ i, i ≥ B.length → rho i = 0) →
      (cubicZeroSet (P.at rho)).ncard = count.toNat := by
  induction maxDepth generalizing B with
  | zero =>
      exact cubicCountCheckBox_sound P B count cfg hcheck
  | succ depth ih =>
      intro rho hrho hzero
      simp only [cubicCountCheckSubdiv, Bool.or_eq_true, Bool.and_eq_true] at hcheck
      rcases hcheck with hleaf | ⟨hleft, hright⟩
      · exact cubicCountCheckBox_sound P B count cfg hleaf rho hrho hzero
      · rcases Box.envMem_splitWidest_cases' B rho hrho with hrhoLeft | hrhoRight
        · apply ih (B.splitWidest).1 hleft rho hrhoLeft
          intro i hi
          apply hzero i
          rw [Box.splitWidest_fst_length'] at hi
          exact hi
        · apply ih (B.splitWidest).2 hright rho hrhoRight
          intro i hi
          apply hzero i
          rw [Box.splitWidest_snd_length'] at hi
          exact hi

end LeanCert.Engine
