/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Taylor
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev

/-!
# Certified Chebyshev ψ(N) Upper Bounds

This module provides a fully computable upper bound `psiUB(N)` on the
Chebyshev function `ψ(N) = ∑_{n ∈ Ioc 0 N} Λ(n)`, together with a
correctness theorem `ψ(N) ≤ psiUB(N)`.

## Strategy

1. `vonMangoldtUB n depth` returns `(logPointComputable (minFac n) depth).hi`
   when `IsPrimePow n`, and `0` otherwise.  This is a computable `ℚ` value.

2. `psiUB N depth = ∑ n ∈ Ioc 0 N, vonMangoldtUB n depth` is a computable
   rational sum.

3. The correctness proof chains:
   - `Λ(n) ≤ vonMangoldtUB(n)` via `mem_logPointComputable`
   - `ψ(N) ≤ psiUB(N)` via `Finset.sum_le_sum`

Since `IsPrimePow n` is `Decidable` for `ℕ`, `Nat.minFac` is computable,
and `logPointComputable` is computable, the entire bound is computable
and can be checked by `native_decide`.

## References

* Chebyshev's function: Mathlib `Chebyshev.psi`
* Von Mangoldt function: Mathlib `ArithmeticFunction.vonMangoldt`
-/

namespace LeanCert.Engine.ChebyshevPsi

open Finset Real ArithmeticFunction
open Chebyshev (psi)
open LeanCert.Core (IntervalRat)
open LeanCert.Core.IntervalRat (logPointComputable mem_logPointComputable mem_def)

/-! ### Computable upper bound on Λ(n) -/

/-- Computable upper bound on the von Mangoldt function Λ(n).
    Returns `(logPointComputable (minFac n) depth).hi` when `IsPrimePow n`,
    and `0` otherwise. -/
def vonMangoldtUB (n : ℕ) (depth : ℕ := 20) : ℚ :=
  if IsPrimePow n then (logPointComputable (n.minFac : ℚ) depth).hi else 0

/-- Computable upper bound on ψ(N).
    `psiUB N depth = ∑ n ∈ Ioc 0 N, vonMangoldtUB n depth` -/
def psiUB (N : ℕ) (depth : ℕ := 20) : ℚ :=
  (Ioc 0 N).sum (fun n => vonMangoldtUB n depth)

/-! ### Correctness theorems -/

/-- The von Mangoldt function is bounded above by our computable bound. -/
theorem vonMangoldt_le_vonMangoldtUB (n : ℕ) (depth : ℕ) :
    (Λ n : ℝ) ≤ (vonMangoldtUB n depth : ℝ) := by
  unfold vonMangoldtUB
  rw [vonMangoldt_apply]
  split_ifs with h
  · -- Case: IsPrimePow n, need log(minFac n) ≤ hi
    have hpos : (0 : ℚ) < (n.minFac : ℚ) := by
      exact_mod_cast Nat.minFac_pos n
    have hmem := mem_logPointComputable hpos depth
    simp only [IntervalRat.mem_def] at hmem
    exact hmem.2
  · -- Case: ¬IsPrimePow n, both sides are 0
    simp

/-- The Chebyshev function ψ(N) is bounded above by psiUB(N). -/
theorem psi_le_psiUB (N : ℕ) (depth : ℕ) :
    psi (N : ℝ) ≤ (psiUB N depth : ℝ) := by
  unfold psi psiUB
  rw [Nat.floor_natCast]
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun n _ => vonMangoldt_le_vonMangoldtUB n depth

/-! ### Decidable comparison infrastructure -/

/-- Master theorem: if `psiUB(N, depth) ≤ c` is verified computationally,
    then `ψ(N) ≤ c`. -/
theorem psi_le_of_psiUB_le (N : ℕ) (depth : ℕ) (c : ℚ)
    (h : decide (psiUB N depth ≤ c) = true) :
    psi (N : ℝ) ≤ (c : ℝ) := by
  have hub := psi_le_psiUB N depth
  have hle : psiUB N depth ≤ c := by rwa [decide_eq_true_eq] at h
  exact le_trans hub (by exact_mod_cast hle)

/-! ### Bulk verification: ψ(N) ≤ 1.11 * N for all N ≤ bound -/

/-- Computable check: does psiUB(N) ≤ 111 * N / 100 hold? -/
def checkPsiBound (N : ℕ) (depth : ℕ := 20) : Bool :=
  decide (psiUB N depth ≤ 111 * (N : ℚ) / 100)

/-- If checkPsiBound N depth holds, then ψ(N) ≤ 1.11 * N.
    This is the key theorem: it's sorry-free and connects the decidable check
    to the analytic bound. Downstream code provides the decidable check via native_decide. -/
theorem psi_le_of_checkPsiBound (N depth : ℕ)
    (h : checkPsiBound N depth = true) :
    psi (N : ℝ) ≤ 111 / 100 * N := by
  unfold checkPsiBound at h
  rw [decide_eq_true_eq] at h
  have hub := psi_le_psiUB N depth
  calc psi (N : ℝ) ≤ (psiUB N depth : ℝ) := hub
    _ ≤ (111 * (N : ℚ) / 100 : ℚ) := by exact_mod_cast h
    _ = 111 / 100 * N := by push_cast; ring

/-- ψ(x) ≤ ψ(⌊x⌋₊) ≤ 1.11 * ⌊x⌋₊ ≤ 1.11 * x, given checkPsiBound at ⌊x⌋₊. -/
theorem psi_le_mul_real (x : ℝ) (depth : ℕ) (hx : 0 < x)
    (h : checkPsiBound ⌊x⌋₊ depth = true) :
    psi x ≤ 111 / 100 * x := by
  have hnn : (0 : ℝ) ≤ x := le_of_lt hx
  have := psi_le_of_checkPsiBound ⌊x⌋₊ depth h
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  calc psi (⌊x⌋₊ : ℝ) ≤ 111 / 100 * ⌊x⌋₊ := this
    _ ≤ 111 / 100 * x := by gcongr; exact Nat.floor_le hnn

/-! ### Efficient incremental checker (for `#eval` / `native_decide` testing) -/

/-- Helper: accumulate vonMangoldtUB from 1 to n-1. -/
def psiUBAcc (n : ℕ) (depth : ℕ) : ℚ :=
  (Ioc 0 (n - 1)).sum (fun i => vonMangoldtUB i depth)

/-- Efficient O(N) check that psiUB(N) ≤ 1.11 * N for all N = 1, ..., bound.
    Uses incremental accumulation instead of recomputing psiUB from scratch. -/
def allPsiBoundsHold (bound : ℕ) (depth : ℕ := 20) : Bool :=
  go bound depth 1 0
where
  go (bound depth n : ℕ) (acc : ℚ) : Bool :=
    if n > bound then true
    else
      let acc' := acc + vonMangoldtUB n depth
      if decide (acc' ≤ 111 * (n : ℚ) / 100) then go bound depth (n + 1) acc'
      else false
  termination_by bound + 1 - n

/-! ### Bridge: allPsiBoundsHold.go → checkPsiBound -/

private theorem psiUB_succ (n depth : ℕ) :
    psiUB (n + 1) depth = psiUB n depth + vonMangoldtUB (n + 1) depth := by
  unfold psiUB
  have hdisj : Disjoint (Ioc 0 n) {n + 1} := by
    simp [Finset.disjoint_singleton_right, Finset.mem_Ioc]
  rw [show Ioc 0 (n + 1) = (Ioc 0 n) ∪ {n + 1} from by
    ext x; simp [Finset.mem_Ioc]; omega]
  rw [Finset.sum_union hdisj, Finset.sum_singleton]

private theorem psiUB_eq_acc (n : ℕ) (hn : 0 < n) (depth : ℕ) :
    psiUB n depth = psiUB (n - 1) depth + vonMangoldtUB n depth := by
  have h1 : n = (n - 1) + 1 := by omega
  conv_lhs => rw [h1]
  rw [psiUB_succ]
  simp [show n - 1 + 1 = n from by omega]

/-- Core bridge: if the incremental loop `go` returns true starting at step `n` with
    accumulator `acc = psiUB(n-1)`, then `checkPsiBound m` holds for all m in [n, bound]. -/
private def go_true_implies
    (bound depth n : ℕ) (hn_pos : 0 < n) (acc : ℚ)
    (hacc : acc = psiUB (n - 1) depth)
    (hgo : allPsiBoundsHold.go bound depth n acc = true)
    (m : ℕ) (hm : n ≤ m) (hmb : m ≤ bound) :
    checkPsiBound m depth = true := by
  unfold allPsiBoundsHold.go at hgo
  split at hgo
  · omega  -- n > bound contradicts n ≤ m ≤ bound
  · rename_i hn_le
    -- Extract the let binding
    change (if decide (acc + vonMangoldtUB n depth ≤ 111 * (n : ℚ) / 100) then
      allPsiBoundsHold.go bound depth (n + 1) (acc + vonMangoldtUB n depth) else false) = true
      at hgo
    split at hgo
    · rename_i hcheck
      -- Check passed for n
      have hpsiUB_n : psiUB n depth ≤ 111 * (n : ℚ) / 100 := by
        rw [psiUB_eq_acc n hn_pos depth, ← hacc]
        rwa [decide_eq_true_eq] at hcheck
      by_cases hmn : m = n
      · subst hmn
        exact decide_eq_true_eq.mpr hpsiUB_n
      · exact go_true_implies bound depth (n + 1) (by omega)
          (acc + vonMangoldtUB n depth)
          (by rw [show n + 1 - 1 = n from by omega, psiUB_eq_acc n hn_pos, hacc])
          hgo m (by omega) hmb
    · exact absurd hgo Bool.false_ne_true
  termination_by bound + 1 - n

/-- If `allPsiBoundsHold bound depth` returns true, then `checkPsiBound N depth` is true
    for all N in {1, ..., bound}. -/
theorem allPsiBoundsHold_implies_checkPsiBound
    (bound depth : ℕ) (h : allPsiBoundsHold bound depth = true)
    (N : ℕ) (hN : 0 < N) (hNb : N ≤ bound) :
    checkPsiBound N depth = true :=
  go_true_implies bound depth 1 (by omega) 0 (by simp [psiUB]) h N hN hNb

end LeanCert.Engine.ChebyshevPsi
