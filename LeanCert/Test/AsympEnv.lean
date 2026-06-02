/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp

/-!
# Tests for certified asymptotic envelopes
-/

namespace LeanCert.Test.AsympEnv

open LeanCert.ANT
open LeanCert.ANT.Asymp
open LeanCert.ANT.Asymp.AsympEnv
open LeanCert.Core

/-- Exact envelope for the zero sequence. -/
noncomputable def zeroEnv : AsympEnv where
  seq := fun _ => 0
  cutoff := 0
  mainTerm := Expr.const 0
  errorTerm := Expr.const 0
  cert := by
    intro N _hN
    simp [prefixSum, evalAtNat]

/-- Exact envelope for the sequence concentrated at zero. -/
noncomputable def deltaZeroEnv : AsympEnv where
  seq := fun n => if n = 0 then (1 : ℝ) else 0
  cutoff := 0
  mainTerm := Expr.const 1
  errorTerm := Expr.const 0
  cert := by
    intro N _hN
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum :
        prefixSum (fun n => if n = 0 then (1 : ℝ) else 0) (N + 1) = 1 := by
      unfold prefixSum
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b hb hb0
        simp [hb0]
      · intro hnot
        exact False.elim (hnot hmem)
    simp [hsum, evalAtNat]

example (N : Nat) :
    (AsympEnv.add zeroEnv deltaZeroEnv).summatory N = 1 := by
  simp [AsympEnv.add, summatory, zeroEnv, deltaZeroEnv]
  have hsum :
      prefixSum (fun n => if n = 0 then (1 : ℝ) else 0) (N + 1) = 1 := by
    unfold prefixSum
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hb0
      simp [hb0]
    · intro hnot
      exact False.elim (hnot (by simp))
  exact hsum

example (N : Nat) :
    |(AsympEnv.add zeroEnv deltaZeroEnv).summatory N
      - evalAtNat (AsympEnv.add zeroEnv deltaZeroEnv).mainTerm N|
      ≤ evalAtNat (AsympEnv.add zeroEnv deltaZeroEnv).errorTerm N := by
  exact (AsympEnv.add zeroEnv deltaZeroEnv).cert N (Nat.zero_le N)

example (N : Nat) :
    |(AsympEnv.constMul (-3) deltaZeroEnv).summatory N
      - evalAtNat (AsympEnv.constMul (-3) deltaZeroEnv).mainTerm N|
      ≤ evalAtNat (AsympEnv.constMul (-3) deltaZeroEnv).errorTerm N := by
  exact (AsympEnv.constMul (-3) deltaZeroEnv).cert N (Nat.zero_le N)

/-- A deliberately weaker zero-sequence envelope with error one. -/
noncomputable def zeroEnvErrorOne : AsympEnv :=
  zeroEnv.weakenError (Expr.const 1) (by
    intro N _hN
    simp [zeroEnv, evalAtNat])

example (N : Nat) :
    zeroEnvErrorOne.lower N ≤ zeroEnvErrorOne.summatory N ∧
      zeroEnvErrorOne.summatory N ≤ zeroEnvErrorOne.upper N := by
  exact ⟨zeroEnvErrorOne.lower_le_summatory N (Nat.zero_le N),
    zeroEnvErrorOne.summatory_le_upper N (Nat.zero_le N)⟩

end LeanCert.Test.AsympEnv
