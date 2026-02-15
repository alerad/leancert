/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Taylor
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev

/-!
# Certified Chebyshev psi(N) Upper Bounds

This module provides computable upper bounds on the Chebyshev function
`psi(N) = sum_{n in Ioc 0 N} vonMangoldt(n)`.

The core checker is generalized by a rational slope `slope`:
- `checkPsiLeMulWith N slope depth` checks `psiUB(N) <= slope * N`
- `checkAllPsiLeMulWith bound slope depth` checks all `N = 1..bound`

The original `1.11`-specific API is kept as thin wrappers:
- `checkPsiBound`, `allPsiBoundsHold`, and their bridge theorems.
-/

namespace LeanCert.Engine.ChebyshevPsi

open Finset Real ArithmeticFunction
open Chebyshev (psi)
open LeanCert.Core (IntervalRat)
open LeanCert.Core.IntervalRat (logPointComputable mem_logPointComputable mem_def)

/-! ### Computable upper bound on vonMangoldt(n) -/

/-- Computable upper bound on the von Mangoldt function `vonMangoldt(n)`.
Returns `(logPointComputable (minFac n) depth).hi` when `IsPrimePow n`,
and `0` otherwise. -/
def vonMangoldtUB (n : Nat) (depth : Nat := 20) : Rat :=
  if IsPrimePow n then (logPointComputable (n.minFac : Rat) depth).hi else 0

/-- Computable upper bound on `psi(N)`:
`psiUB N depth = sum n in Ioc 0 N, vonMangoldtUB n depth`. -/
def psiUB (N : Nat) (depth : Nat := 20) : Rat :=
  (Ioc 0 N).sum (fun n => vonMangoldtUB n depth)

/-! ### Correctness theorems -/

/-- The von Mangoldt function is bounded above by our computable bound. -/
theorem vonMangoldt_le_vonMangoldtUB (n : Nat) (depth : Nat) :
    (vonMangoldt n : Real) <= (vonMangoldtUB n depth : Real) := by
  rw [vonMangoldt_apply]
  by_cases hp : IsPrimePow n
  case pos =>
    have hpos : (0 : Rat) < (n.minFac : Rat) := by
      exact_mod_cast Nat.minFac_pos n
    have hmem := mem_logPointComputable hpos depth
    simp [IntervalRat.mem_def] at hmem
    simpa [vonMangoldtUB, hp] using hmem.2
  case neg =>
    simp [vonMangoldtUB, hp]

/-- The Chebyshev function `psi(N)` is bounded above by `psiUB(N)`. -/
theorem psi_le_psiUB (N : Nat) (depth : Nat) :
    psi (N : Real) <= (psiUB N depth : Real) := by
  unfold psi psiUB
  rw [Nat.floor_natCast]
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun n _ => vonMangoldt_le_vonMangoldtUB n depth

/-! ### Decidable comparison infrastructure -/

/-- Master theorem: if `psiUB(N, depth) <= slope` is verified computationally,
then `psi(N) <= slope`. -/
theorem psi_le_of_psiUB_le (N : Nat) (depth : Nat) (slope : Rat)
    (h : decide (psiUB N depth <= slope) = true) :
    psi (N : Real) <= (slope : Real) := by
  have hub := psi_le_psiUB N depth
  have hle : psiUB N depth <= slope := by rwa [decide_eq_true_eq] at h
  exact le_trans hub (by exact_mod_cast hle)

/-! ### Generic slope checker: psi(N) <= slope * N -/

/-- Computable check: does `psiUB(N) <= slope * N` hold? -/
def checkPsiLeMulWith (N : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  decide (psiUB N depth <= slope * (N : Rat))

/-- If `checkPsiLeMulWith N slope depth` holds, then `psi(N) <= slope * N`. -/
theorem psi_le_of_checkPsiLeMulWith (N depth : Nat) (slope : Rat)
    (h : checkPsiLeMulWith N slope depth = true) :
    psi (N : Real) <= (slope : Real) * N := by
  unfold checkPsiLeMulWith at h
  rw [decide_eq_true_eq] at h
  have hub := psi_le_psiUB N depth
  calc
    psi (N : Real) <= (psiUB N depth : Real) := hub
    _ <= (slope * (N : Rat) : Rat) := by exact_mod_cast h
    _ = (slope : Real) * N := by norm_cast

/-- Real-variable form:
if `checkPsiLeMulWith floor(x) slope depth` holds and `slope >= 0`,
then `psi(x) <= slope*x`. -/
theorem psi_le_mul_real_of_checkPsiLeMulWith
    (x : Real) (slope : Rat) (depth : Nat)
    (hslope : 0 <= slope) (hx : 0 < x)
    (h : checkPsiLeMulWith (Nat.floor x) slope depth = true) :
    psi x <= (slope : Real) * x := by
  have hnn : (0 : Real) <= x := le_of_lt hx
  have hNat := psi_le_of_checkPsiLeMulWith (Nat.floor x) depth slope h
  have hfloor : (Nat.floor x : Real) <= x := Nat.floor_le hnn
  have hslopeReal : (0 : Real) <= (slope : Real) := by exact_mod_cast hslope
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  calc
    psi (Nat.floor x : Real) <= (slope : Real) * Nat.floor x := hNat
    _ <= (slope : Real) * x := mul_le_mul_of_nonneg_left hfloor hslopeReal

/-! ### Backwards-compatible wrappers for slope = 111/100 -/

/-- Legacy check used by downstream code: `psiUB(N) <= 1.11 * N`. -/
def checkPsiBound (N : Nat) (depth : Nat := 20) : Bool :=
  checkPsiLeMulWith N (111 / 100) depth

/-- Legacy theorem used by downstream code: `psi(N) <= 1.11 * N`. -/
theorem psi_le_of_checkPsiBound (N depth : Nat)
    (h : checkPsiBound N depth = true) :
    psi (N : Real) <= 111 / 100 * N := by
  simpa [checkPsiBound] using
    (psi_le_of_checkPsiLeMulWith N depth (111 / 100) h)

/-- Real-variable legacy theorem:
`psi(x) <= 1.11 * x`, given `checkPsiBound floor(x) depth`. -/
theorem psi_le_mul_real (x : Real) (depth : Nat) (hx : 0 < x)
    (h : checkPsiBound (Nat.floor x) depth = true) :
    psi x <= 111 / 100 * x := by
  have hslope : (0 : Rat) <= (111 / 100 : Rat) := by norm_num
  simpa [checkPsiBound] using
    (psi_le_mul_real_of_checkPsiLeMulWith x (111 / 100) depth hslope hx h)

/-! ### Efficient incremental checker (for #eval / native_decide testing) -/

/-- Helper: accumulate `vonMangoldtUB` from `1` to `n-1`. -/
def psiUBPrefix (n : Nat) (depth : Nat) : Rat :=
  (Ioc 0 (n - 1)).sum (fun i => vonMangoldtUB i depth)

/-- Efficient O(N) check that `psiUB(N) <= slope * N` for all `N = 1..bound`.
Uses incremental accumulation instead of recomputing `psiUB` from scratch. -/
def checkAllPsiLeMulWith (bound : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  go bound slope depth 1 0
where
  go (bound : Nat) (slope : Rat) (depth n : Nat) (acc : Rat) : Bool :=
    if n > bound then true
    else
      let acc' := acc + vonMangoldtUB n depth
      if decide (acc' <= slope * (n : Rat)) then go bound slope depth (n + 1) acc'
      else false
  termination_by bound + 1 - n

/-- Legacy O(N) checker for `slope = 111/100`. -/
def allPsiBoundsHold (bound : Nat) (depth : Nat := 20) : Bool :=
  checkAllPsiLeMulWith bound (111 / 100) depth

/-! ### Bridge: checkAllPsiLeMulWith.go -> checkPsiLeMulWith -/

private theorem psiUB_succ (n depth : Nat) :
    psiUB (n + 1) depth = psiUB n depth + vonMangoldtUB (n + 1) depth := by
  unfold psiUB
  rw [show Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) from by
    ext x
    simp [Finset.mem_Ioc]
    omega]
  rw [Finset.sum_insert (by simp [Finset.mem_Ioc])]
  ring

private theorem psiUB_eq_acc (n : Nat) (hn : 0 < n) (depth : Nat) :
    psiUB n depth = psiUB (n - 1) depth + vonMangoldtUB n depth := by
  have h1 : n = (n - 1) + 1 := by omega
  conv_lhs => rw [h1]
  rw [psiUB_succ]
  simp [show n - 1 + 1 = n from by omega]

/-- Core bridge: if the incremental loop `go` returns true starting at step `n`
with accumulator `acc = psiUB(n-1)`, then `checkPsiLeMulWith m slope depth` holds
for all `m in [n, bound]`. -/
private def go_true_implies_checkPsiLeMulWith
    (bound : Nat) (slope : Rat) (depth n : Nat) (hn_pos : 0 < n) (acc : Rat)
    (hacc : acc = psiUB (n - 1) depth)
    (hgo : checkAllPsiLeMulWith.go bound slope depth n acc = true)
    (m : Nat) (hm : n <= m) (hmb : m <= bound) :
    checkPsiLeMulWith m slope depth = true := by
  unfold checkAllPsiLeMulWith.go at hgo
  split at hgo
  case isTrue hn_gt =>
    omega
  case isFalse hn_le =>
    change (if decide (acc + vonMangoldtUB n depth <= slope * (n : Rat)) then
      checkAllPsiLeMulWith.go bound slope depth (n + 1) (acc + vonMangoldtUB n depth)
      else false) = true at hgo
    split at hgo
    case isTrue hcheck =>
      have hpsiUB_n : psiUB n depth <= slope * (n : Rat) := by
        rw [psiUB_eq_acc n hn_pos depth, <- hacc]
        rwa [decide_eq_true_eq] at hcheck
      by_cases hmn : m = n
      case pos =>
        subst hmn
        exact decide_eq_true_eq.mpr hpsiUB_n
      case neg =>
        exact go_true_implies_checkPsiLeMulWith bound slope depth (n + 1) (by omega)
          (acc + vonMangoldtUB n depth)
          (by
            rw [show n + 1 - 1 = n from by omega]
            rw [psiUB_eq_acc n hn_pos depth, hacc])
          hgo m (by omega) hmb
    case isFalse =>
      exact absurd hgo Bool.false_ne_true
  termination_by bound + 1 - n

/-- If `checkAllPsiLeMulWith bound slope depth` returns true, then
`checkPsiLeMulWith N slope depth` is true for all `N in {1, ..., bound}`. -/
theorem checkAllPsiLeMulWith_implies_checkPsiLeMulWith
    (bound : Nat) (slope : Rat) (depth : Nat)
    (h : checkAllPsiLeMulWith bound slope depth = true)
    (N : Nat) (hN : 0 < N) (hNb : N <= bound) :
    checkPsiLeMulWith N slope depth = true :=
  go_true_implies_checkPsiLeMulWith bound slope depth 1 (by omega) 0 (by simp [psiUB]) h N hN hNb

/-- Legacy bridge theorem for `slope = 111/100`. -/
theorem allPsiBoundsHold_implies_checkPsiBound
    (bound depth : Nat) (h : allPsiBoundsHold bound depth = true)
    (N : Nat) (hN : 0 < N) (hNb : N <= bound) :
    checkPsiBound N depth = true := by
  simpa [allPsiBoundsHold, checkPsiBound] using
    (checkAllPsiLeMulWith_implies_checkPsiLeMulWith bound (111 / 100) depth h N hN hNb)

end LeanCert.Engine.ChebyshevPsi
