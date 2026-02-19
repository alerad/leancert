/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Taylor
import Mathlib.NumberTheory.Chebyshev

/-!
# Certified Chebyshev theta(N) Bounds

This module provides computable upper **and** lower bounds on the first Chebyshev
function `theta(N) = sum_{p prime, p in Ioc 0 N} log p`.

## Main definitions

* `logPrimeUB n depth` / `logPrimeLB n depth` — upper/lower bounds on the
  `n`-th summand of theta.
* `thetaUB N depth` / `thetaLB N depth` — upper/lower bounds on theta(N).
* `checkThetaLeMulWith` / `checkAllThetaLeMulWith` — decide `thetaUB(N) ≤ slope * N`.
* `checkThetaAbsError` / `checkAllThetaAbsError` — decide `|theta(N) - N| ≤ bound`
  (both directions).

## Design notes

The structure mirrors `ChebyshevPsi` almost exactly.  The difference is that
summands are `log p` (only primes) instead of `vonMangoldt n` (prime powers).
For the absolute-error checker we need *both* an upper and a lower bound on theta;
the lower bound uses `logPrimeLB` (the `.lo` endpoint of the interval enclosure).
-/

namespace LeanCert.Engine.ChebyshevTheta

open Finset Real
open Chebyshev (theta)
open LeanCert.Core (IntervalRat)
open LeanCert.Core.IntervalRat (logPointComputable mem_logPointComputable mem_def)

/-! ### Computable upper and lower bounds on the theta summand -/

/-- Computable upper bound on the theta summand at `n`.
Returns `(logPointComputable n depth).hi` when `n` is prime, `0` otherwise. -/
def logPrimeUB (n : Nat) (depth : Nat := 20) : Rat :=
  if n.Prime then (logPointComputable (n : Rat) depth).hi else 0

/-- Computable lower bound on the theta summand at `n`.
Returns `(logPointComputable n depth).lo` when `n` is prime, `0` otherwise. -/
def logPrimeLB (n : Nat) (depth : Nat := 20) : Rat :=
  if n.Prime then (logPointComputable (n : Rat) depth).lo else 0

/-- Computable upper bound on `theta(N)`:
`thetaUB N depth = sum n in Ioc 0 N, logPrimeUB n depth`. -/
def thetaUB (N : Nat) (depth : Nat := 20) : Rat :=
  (Ioc 0 N).sum (fun n => logPrimeUB n depth)

/-- Computable lower bound on `theta(N)`:
`thetaLB N depth = sum n in Ioc 0 N, logPrimeLB n depth`. -/
def thetaLB (N : Nat) (depth : Nat := 20) : Rat :=
  (Ioc 0 N).sum (fun n => logPrimeLB n depth)

/-! ### Correctness theorems -/

/-- The theta summand `log p` is bounded above by our computable bound for primes,
and is zero (hence bounded) for non-primes. -/
theorem log_prime_le_logPrimeUB (n : Nat) (depth : Nat) :
    (if n.Prime then Real.log n else 0 : Real) ≤ (logPrimeUB n depth : Real) := by
  by_cases hp : n.Prime
  case pos =>
    have hpos : (0 : Rat) < (n : Rat) := by exact_mod_cast hp.pos
    have hmem := mem_logPointComputable hpos depth
    simp [IntervalRat.mem_def] at hmem
    simp [logPrimeUB, hp]
    exact hmem.2
  case neg =>
    simp [logPrimeUB, hp]

/-- The theta summand is bounded below by our computable bound. -/
theorem logPrimeLB_le_log_prime (n : Nat) (depth : Nat) :
    (logPrimeLB n depth : Real) ≤ (if n.Prime then Real.log n else 0 : Real) := by
  by_cases hp : n.Prime
  case pos =>
    have hpos : (0 : Rat) < (n : Rat) := by exact_mod_cast hp.pos
    have hmem := mem_logPointComputable hpos depth
    simp [IntervalRat.mem_def] at hmem
    simp [logPrimeLB, hp]
    exact hmem.1
  case neg =>
    simp [logPrimeLB, hp]

/-- Rewrite `theta(N)` as a sum with an if-then-else over `Prime`. -/
private theorem theta_eq_ite_sum (N : Nat) :
    theta (N : Real) = ∑ n ∈ Ioc 0 N, if n.Prime then Real.log n else 0 := by
  unfold theta
  rw [Nat.floor_natCast, sum_filter]

/-- `theta(N)` is bounded above by `thetaUB(N)`. -/
theorem theta_le_thetaUB (N : Nat) (depth : Nat) :
    theta (N : Real) ≤ (thetaUB N depth : Real) := by
  rw [theta_eq_ite_sum]
  unfold thetaUB
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun n _ => log_prime_le_logPrimeUB n depth

/-- `theta(N)` is bounded below by `thetaLB(N)`. -/
theorem thetaLB_le_theta (N : Nat) (depth : Nat) :
    (thetaLB N depth : Real) ≤ theta (N : Real) := by
  rw [theta_eq_ite_sum]
  unfold thetaLB
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun n _ => logPrimeLB_le_log_prime n depth

/-! ### Decidable comparison infrastructure -/

/-- If `thetaUB(N, depth) <= slope` computationally, then `theta(N) <= slope`. -/
theorem theta_le_of_thetaUB_le (N : Nat) (depth : Nat) (slope : Rat)
    (h : decide (thetaUB N depth <= slope) = true) :
    theta (N : Real) <= (slope : Real) := by
  have hub := theta_le_thetaUB N depth
  have hle : thetaUB N depth <= slope := by rwa [decide_eq_true_eq] at h
  exact le_trans hub (by exact_mod_cast hle)

/-! ### Generic slope checker: theta(N) <= slope * N -/

/-- Computable check: does `thetaUB(N) <= slope * N` hold? -/
def checkThetaLeMulWith (N : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  decide (thetaUB N depth <= slope * (N : Rat))

/-- If `checkThetaLeMulWith N slope depth` holds, then `theta(N) <= slope * N`. -/
theorem theta_le_of_checkThetaLeMulWith (N depth : Nat) (slope : Rat)
    (h : checkThetaLeMulWith N slope depth = true) :
    theta (N : Real) <= (slope : Real) * N := by
  unfold checkThetaLeMulWith at h
  rw [decide_eq_true_eq] at h
  have hub := theta_le_thetaUB N depth
  calc
    theta (N : Real) <= (thetaUB N depth : Real) := hub
    _ <= (slope * (N : Rat) : Rat) := by exact_mod_cast h
    _ = (slope : Real) * N := by norm_cast

/-! ### Absolute error checker: |theta(N) - N| <= bound -/

/-- Computable check for `|theta(N) - N| <= bound`.
Checks both `thetaUB(N) - N <= bound` and `N - thetaLB(N) <= bound`. -/
def checkThetaAbsError (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  decide (thetaUB N depth - (N : Rat) <= bound) &&
  decide ((N : Rat) - thetaLB N depth <= bound)

/-- If `checkThetaAbsError N bound depth` holds, then `|theta(N) - N| <= bound`. -/
theorem abs_theta_sub_le_of_checkThetaAbsError (N depth : Nat) (bound : Rat)
    (h : checkThetaAbsError N bound depth = true) :
    |theta (N : Real) - N| <= (bound : Real) := by
  unfold checkThetaAbsError at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [decide_eq_true_eq] at h1 h2
  have hub := theta_le_thetaUB N depth
  have hlb := thetaLB_le_theta N depth
  rw [abs_le]
  constructor
  · -- -(bound : ℝ) ≤ theta(N) - N
    have hcast : (thetaLB N depth : Real) ≥ (N : Real) - (bound : Real) := by
      have : ((N : Rat) - thetaLB N depth : Rat) ≤ bound := h2
      exact_mod_cast (show (N : Rat) - bound ≤ thetaLB N depth by linarith)
    linarith
  · -- theta(N) - N ≤ bound
    have hcast : (thetaUB N depth : Real) ≤ (N : Real) + (bound : Real) := by
      have : (thetaUB N depth - (N : Rat) : Rat) ≤ bound := h1
      exact_mod_cast (show thetaUB N depth ≤ (N : Rat) + bound by linarith)
    linarith

/-! ### Efficient incremental checkers (O(N) for native_decide) -/

/-- Helper: `thetaUB` for the prefix `1..n-1`. -/
def thetaUBPrefix (n : Nat) (depth : Nat) : Rat :=
  (Ioc 0 (n - 1)).sum (fun i => logPrimeUB i depth)

private theorem thetaUB_succ (n depth : Nat) :
    thetaUB (n + 1) depth = thetaUB n depth + logPrimeUB (n + 1) depth := by
  unfold thetaUB
  rw [show Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) from by
    ext x
    simp [Finset.mem_Ioc]
    omega]
  rw [Finset.sum_insert (by simp [Finset.mem_Ioc])]
  ring

private theorem thetaUB_eq_acc (n : Nat) (hn : 0 < n) (depth : Nat) :
    thetaUB n depth = thetaUB (n - 1) depth + logPrimeUB n depth := by
  have h1 : n = (n - 1) + 1 := by omega
  conv_lhs => rw [h1]
  rw [thetaUB_succ]
  simp [show n - 1 + 1 = n from by omega]

/-- Efficient O(N) incremental checker for `thetaUB(N) <= slope * N`
for all `N = 1..bound`. -/
def checkAllThetaLeMulWith (bound : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  go bound slope depth 1 0
where
  go (bound : Nat) (slope : Rat) (depth n : Nat) (acc : Rat) : Bool :=
    if n > bound then true
    else
      let acc' := acc + logPrimeUB n depth
      if decide (acc' <= slope * (n : Rat)) then go bound slope depth (n + 1) acc'
      else false
  termination_by bound + 1 - n

/-! ### Bridge: checkAllThetaLeMulWith.go → checkThetaLeMulWith -/

private def go_true_implies_checkThetaLeMulWith
    (bound : Nat) (slope : Rat) (depth n : Nat) (hn_pos : 0 < n) (acc : Rat)
    (hacc : acc = thetaUB (n - 1) depth)
    (hgo : checkAllThetaLeMulWith.go bound slope depth n acc = true)
    (m : Nat) (hm : n <= m) (hmb : m <= bound) :
    checkThetaLeMulWith m slope depth = true := by
  unfold checkAllThetaLeMulWith.go at hgo
  split at hgo
  case isTrue hn_gt =>
    omega
  case isFalse hn_le =>
    change (if decide (acc + logPrimeUB n depth <= slope * (n : Rat)) then
      checkAllThetaLeMulWith.go bound slope depth (n + 1) (acc + logPrimeUB n depth)
      else false) = true at hgo
    split at hgo
    case isTrue hcheck =>
      have hthetaUB_n : thetaUB n depth <= slope * (n : Rat) := by
        rw [thetaUB_eq_acc n hn_pos depth, ← hacc]
        rwa [decide_eq_true_eq] at hcheck
      by_cases hmn : m = n
      case pos =>
        subst hmn
        exact decide_eq_true_eq.mpr hthetaUB_n
      case neg =>
        exact go_true_implies_checkThetaLeMulWith bound slope depth (n + 1) (by omega)
          (acc + logPrimeUB n depth)
          (by
            rw [show n + 1 - 1 = n from by omega]
            rw [thetaUB_eq_acc n hn_pos depth, hacc])
          hgo m (by omega) hmb
    case isFalse =>
      exact absurd hgo Bool.false_ne_true
  termination_by bound + 1 - n

/-- If `checkAllThetaLeMulWith bound slope depth` returns true, then
`checkThetaLeMulWith N slope depth` is true for all `N in {1, ..., bound}`. -/
theorem checkAllThetaLeMulWith_implies_checkThetaLeMulWith
    (bound : Nat) (slope : Rat) (depth : Nat)
    (h : checkAllThetaLeMulWith bound slope depth = true)
    (N : Nat) (hN : 0 < N) (hNb : N <= bound) :
    checkThetaLeMulWith N slope depth = true :=
  go_true_implies_checkThetaLeMulWith bound slope depth 1 (by omega) 0
    (by simp [thetaUB]) h N hN hNb

/-! ### Efficient incremental absolute-error checker -/

private theorem thetaLB_succ (n depth : Nat) :
    thetaLB (n + 1) depth = thetaLB n depth + logPrimeLB (n + 1) depth := by
  unfold thetaLB
  rw [show Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) from by
    ext x
    simp [Finset.mem_Ioc]
    omega]
  rw [Finset.sum_insert (by simp [Finset.mem_Ioc])]
  ring

private theorem thetaLB_eq_acc (n : Nat) (hn : 0 < n) (depth : Nat) :
    thetaLB n depth = thetaLB (n - 1) depth + logPrimeLB n depth := by
  have h1 : n = (n - 1) + 1 := by omega
  conv_lhs => rw [h1]
  rw [thetaLB_succ]
  simp [show n - 1 + 1 = n from by omega]

/-- Efficient O(N) incremental checker for `|theta(N) - N| <= bound`
for all `N = 1..limit`.  Maintains both an upper-bound and a lower-bound
accumulator. -/
def checkAllThetaAbsError (limit : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  go limit bound depth 1 0 0
where
  go (limit : Nat) (bound : Rat) (depth n : Nat) (accUB accLB : Rat) : Bool :=
    if n > limit then true
    else
      let accUB' := accUB + logPrimeUB n depth
      let accLB' := accLB + logPrimeLB n depth
      if decide (accUB' - (n : Rat) <= bound) &&
         decide ((n : Rat) - accLB' <= bound) then
        go limit bound depth (n + 1) accUB' accLB'
      else false
  termination_by limit + 1 - n

/-! ### Bridge: checkAllThetaAbsError.go → checkThetaAbsError -/

private def go_true_implies_checkThetaAbsError
    (limit : Nat) (bound : Rat) (depth n : Nat) (hn_pos : 0 < n)
    (accUB accLB : Rat)
    (haccUB : accUB = thetaUB (n - 1) depth)
    (haccLB : accLB = thetaLB (n - 1) depth)
    (hgo : checkAllThetaAbsError.go limit bound depth n accUB accLB = true)
    (m : Nat) (hm : n <= m) (hmb : m <= limit) :
    checkThetaAbsError m bound depth = true := by
  unfold checkAllThetaAbsError.go at hgo
  split at hgo
  case isTrue hn_gt =>
    omega
  case isFalse hn_le =>
    change (if decide (accUB + logPrimeUB n depth - (n : Rat) <= bound) &&
               decide ((n : Rat) - (accLB + logPrimeLB n depth) <= bound) then
      checkAllThetaAbsError.go limit bound depth (n + 1)
        (accUB + logPrimeUB n depth) (accLB + logPrimeLB n depth)
      else false) = true at hgo
    split at hgo
    case isTrue hcheck =>
      rw [Bool.and_eq_true] at hcheck
      obtain ⟨hcheckUB, hcheckLB⟩ := hcheck
      rw [decide_eq_true_eq] at hcheckUB hcheckLB
      have hthetaUB_n : thetaUB n depth - (n : Rat) <= bound := by
        rw [thetaUB_eq_acc n hn_pos depth, ← haccUB]; exact hcheckUB
      have hthetaLB_n : (n : Rat) - thetaLB n depth <= bound := by
        rw [thetaLB_eq_acc n hn_pos depth, ← haccLB]; exact hcheckLB
      by_cases hmn : m = n
      case pos =>
        subst hmn
        unfold checkThetaAbsError
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true_eq.mpr hthetaUB_n, decide_eq_true_eq.mpr hthetaLB_n⟩
      case neg =>
        exact go_true_implies_checkThetaAbsError limit bound depth (n + 1) (by omega)
          (accUB + logPrimeUB n depth) (accLB + logPrimeLB n depth)
          (by rw [show n + 1 - 1 = n from by omega]
              rw [thetaUB_eq_acc n hn_pos depth, haccUB])
          (by rw [show n + 1 - 1 = n from by omega]
              rw [thetaLB_eq_acc n hn_pos depth, haccLB])
          hgo m (by omega) hmb
    case isFalse =>
      exact absurd hgo Bool.false_ne_true
  termination_by limit + 1 - n

/-- If `checkAllThetaAbsError limit bound depth` returns true, then
`checkThetaAbsError N bound depth` is true for all `N in {1, ..., limit}`. -/
theorem checkAllThetaAbsError_implies_checkThetaAbsError
    (limit : Nat) (bound : Rat) (depth : Nat)
    (h : checkAllThetaAbsError limit bound depth = true)
    (N : Nat) (hN : 0 < N) (hNb : N <= limit) :
    checkThetaAbsError N bound depth = true :=
  go_true_implies_checkThetaAbsError limit bound depth 1 (by omega) 0 0
    (by simp [thetaUB]) (by simp [thetaLB]) h N hN hNb

/-! ### Relative error checker: |theta(N) - N| / N <= bound, i.e. |theta(N) - N| <= bound * N

This is what `Eθ(x) ≤ bound` means in the PNT+ blueprint (Definition 2.0.7). -/

/-- Computable check for `|theta(N) - N| <= bound * N`.
Checks `thetaUB(N) <= (1 + bound) * N` and `thetaLB(N) >= (1 - bound) * N`. -/
def checkThetaRelError (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  decide (thetaUB N depth <= (1 + bound) * (N : Rat)) &&
  decide ((1 - bound) * (N : Rat) <= thetaLB N depth)

/-- If `checkThetaRelError N bound depth` holds, then `|theta(N) - N| <= bound * N`. -/
theorem abs_theta_sub_le_mul_of_checkThetaRelError (N depth : Nat) (bound : Rat)
    (h : checkThetaRelError N bound depth = true) :
    |theta (N : Real) - N| <= (bound : Real) * N := by
  unfold checkThetaRelError at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [decide_eq_true_eq] at h1 h2
  have hub := theta_le_thetaUB N depth
  have hlb := thetaLB_le_theta N depth
  rw [abs_le]
  constructor
  · -- -(bound * N) ≤ theta(N) - N, i.e. (1-bound)*N ≤ theta(N)
    have : ((1 - bound) * (N : Rat) : Rat) ≤ (thetaLB N depth : Rat) := h2
    have hcast : ((1 - bound) * (N : Rat) : Real) ≤ (thetaLB N depth : Real) := by
      exact_mod_cast this
    push_cast at hcast ⊢
    linarith
  · -- theta(N) - N ≤ bound * N, i.e. theta(N) ≤ (1+bound)*N
    have : (thetaUB N depth : Rat) ≤ (1 + bound) * (N : Rat) := h1
    have hcast : (thetaUB N depth : Real) ≤ ((1 + bound) * (N : Rat) : Real) := by
      exact_mod_cast this
    push_cast at hcast ⊢
    linarith

/-- Efficient O(N) incremental checker for `|theta(N) - N| <= bound * N`
for all `N = start..limit`.  The `start` parameter allows skipping small N
(e.g. start=3 for the range 2 < x ≤ 599). -/
def checkAllThetaRelError (start limit : Nat) (bound : Rat)
    (depth : Nat := 20) : Bool :=
  go start limit bound depth 1 0 0
where
  go (start limit : Nat) (bound : Rat) (depth n : Nat) (accUB accLB : Rat) : Bool :=
    if n > limit then true
    else
      let accUB' := accUB + logPrimeUB n depth
      let accLB' := accLB + logPrimeLB n depth
      if n < start then
        go start limit bound depth (n + 1) accUB' accLB'
      else if decide (accUB' <= (1 + bound) * (n : Rat)) &&
              decide ((1 - bound) * (n : Rat) <= accLB') then
        go start limit bound depth (n + 1) accUB' accLB'
      else false
  termination_by limit + 1 - n

/-! ### Bridge: checkAllThetaRelError.go → checkThetaRelError -/

private def go_true_implies_checkThetaRelError
    (start limit : Nat) (bound : Rat) (depth n : Nat) (hn_pos : 0 < n)
    (accUB accLB : Rat)
    (haccUB : accUB = thetaUB (n - 1) depth)
    (haccLB : accLB = thetaLB (n - 1) depth)
    (hgo : checkAllThetaRelError.go start limit bound depth n accUB accLB = true)
    (m : Nat) (hm : n <= m) (hm_start : start <= m) (hmb : m <= limit) :
    checkThetaRelError m bound depth = true := by
  unfold checkAllThetaRelError.go at hgo
  split at hgo
  case isTrue hn_gt =>
    omega
  case isFalse hn_le =>
    -- The go function first updates accumulators, then branches on n < start
    change (let accUB' := accUB + logPrimeUB n depth
            let accLB' := accLB + logPrimeLB n depth
            if n < start then
              checkAllThetaRelError.go start limit bound depth (n + 1) accUB' accLB'
            else if decide (accUB' <= (1 + bound) * (n : Rat)) &&
                    decide ((1 - bound) * (n : Rat) <= accLB') then
              checkAllThetaRelError.go start limit bound depth (n + 1) accUB' accLB'
            else false) = true at hgo
    simp only at hgo
    split at hgo
    case isTrue hn_lt_start =>
      -- n < start, skip this step
      exact go_true_implies_checkThetaRelError start limit bound depth (n + 1) (by omega)
        (accUB + logPrimeUB n depth) (accLB + logPrimeLB n depth)
        (by rw [show n + 1 - 1 = n from by omega]
            rw [thetaUB_eq_acc n hn_pos depth, haccUB])
        (by rw [show n + 1 - 1 = n from by omega]
            rw [thetaLB_eq_acc n hn_pos depth, haccLB])
        hgo m (by omega) hm_start hmb
    case isFalse hn_ge_start =>
      split at hgo
      case isTrue hcheck =>
        rw [Bool.and_eq_true] at hcheck
        obtain ⟨hcheckUB, hcheckLB⟩ := hcheck
        rw [decide_eq_true_eq] at hcheckUB hcheckLB
        have hthetaUB_n : thetaUB n depth <= (1 + bound) * (n : Rat) := by
          rw [thetaUB_eq_acc n hn_pos depth, ← haccUB]; exact hcheckUB
        have hthetaLB_n : (1 - bound) * (n : Rat) <= thetaLB n depth := by
          rw [thetaLB_eq_acc n hn_pos depth, ← haccLB]; exact hcheckLB
        by_cases hmn : m = n
        case pos =>
          subst hmn
          unfold checkThetaRelError
          rw [Bool.and_eq_true]
          exact ⟨decide_eq_true_eq.mpr hthetaUB_n, decide_eq_true_eq.mpr hthetaLB_n⟩
        case neg =>
          exact go_true_implies_checkThetaRelError start limit bound depth (n + 1) (by omega)
            (accUB + logPrimeUB n depth) (accLB + logPrimeLB n depth)
            (by rw [show n + 1 - 1 = n from by omega]
                rw [thetaUB_eq_acc n hn_pos depth, haccUB])
            (by rw [show n + 1 - 1 = n from by omega]
                rw [thetaLB_eq_acc n hn_pos depth, haccLB])
            hgo m (by omega) hm_start hmb
      case isFalse =>
        exact absurd hgo Bool.false_ne_true
  termination_by limit + 1 - n

/-- If `checkAllThetaRelError start limit bound depth` returns true, then
`checkThetaRelError N bound depth` holds for all `N in {start, ..., limit}`. -/
theorem checkAllThetaRelError_implies_checkThetaRelError
    (start limit : Nat) (bound : Rat) (depth : Nat)
    (h : checkAllThetaRelError start limit bound depth = true)
    (N : Nat) (hN : 0 < N) (hN_start : start <= N) (hNb : N <= limit) :
    checkThetaRelError N bound depth = true :=
  go_true_implies_checkThetaRelError start limit bound depth 1 (by omega) 0 0
    (by simp [thetaUB]) (by simp [thetaLB]) h N (by omega) hN_start hNb


/-! ### Strengthened checker for real-valued Eθ

For real `x ∈ [N, N+1)`, `θ(x) = θ(N)` but `x` can be as large as `N+1-ε`.
The upper-bound direction still works from the integer check (worst at `x = N`),
but the lower bound requires the strengthened condition `θ(N) ≥ (1-a)·(N+1)`.

At the last integer `N = limit` we only need the regular check (x ≤ limit). -/

/-- Strengthened check for one integer `N`, covering all real `x ∈ [N, N+1)`:
- upper: `thetaUB(N) ≤ (1 + bound) * N`
- lower: `thetaLB(N) ≥ (1 - bound) * (N + 1)` -/
def checkThetaRelErrorReal (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  decide (thetaUB N depth <= (1 + bound) * (N : Rat)) &&
  decide ((1 - bound) * ((N : Rat) + 1) <= thetaLB N depth)

/-- If `checkThetaRelErrorReal N bound depth` holds, then for all real `x ∈ [N, N+1)`,
`|θ(x) - x| ≤ bound * x`. -/
theorem abs_theta_sub_le_mul_of_checkThetaRelErrorReal (N depth : Nat) (bound : Rat)
    (hbound : 0 ≤ bound) (hbound1 : bound ≤ 1)
    (h : checkThetaRelErrorReal N bound depth = true)
    (x : Real) (hxlo : (N : Real) ≤ x) (hxhi : x < (N : Real) + 1) :
    |theta x - x| ≤ (bound : Real) * x := by
  unfold checkThetaRelErrorReal at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [decide_eq_true_eq] at h1 h2
  have hub := theta_le_thetaUB N depth
  have hlb := thetaLB_le_theta N depth
  have hnn : (0 : Real) ≤ x := le_trans (by exact_mod_cast (Nat.zero_le N)) hxlo
  have hfloor : Nat.floor x = N := by
    exact Nat.floor_eq_iff hnn |>.mpr ⟨by exact_mod_cast hxlo, by exact_mod_cast hxhi⟩
  rw [Chebyshev.theta_eq_theta_coe_floor x, hfloor]
  rw [abs_le]
  constructor
  · have hcast : ((1 - bound) * ((N : Rat) + 1) : Real) ≤ (thetaLB N depth : Real) := by
      exact_mod_cast h2
    have h1sub : (0 : Real) ≤ 1 - (bound : Real) := by
      have : (bound : Real) ≤ 1 := by exact_mod_cast hbound1
      linarith
    have : (1 - (bound : Real)) * x ≤ (1 - (bound : Real)) * ((N : Real) + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hxhi) h1sub
    push_cast at hcast ⊢
    linarith
  · have hcast : (thetaUB N depth : Real) ≤ ((1 + bound) * (N : Rat) : Real) := by
      exact_mod_cast h1
    have h1add : (0 : Real) ≤ 1 + (bound : Real) := by
      linarith [show (0 : Real) ≤ bound from by exact_mod_cast hbound]
    have : (1 + (bound : Real)) * (N : Real) ≤ (1 + (bound : Real)) * x :=
      mul_le_mul_of_nonneg_left hxlo h1add
    push_cast at hcast ⊢
    linarith

/-- Efficient O(N) incremental checker for the strengthened real-valued condition.
For `N = start .. limit-1`: checks `checkThetaRelErrorReal N bound depth`
  (covers `x ∈ [N, N+1)`)
For `N = limit`: checks `checkThetaRelError N bound depth`
  (covers only `x = limit`) -/
def checkAllThetaRelErrorReal (start limit : Nat) (bound : Rat)
    (depth : Nat := 20) : Bool :=
  go start limit bound depth 1 0 0
where
  go (start limit : Nat) (bound : Rat) (depth n : Nat) (accUB accLB : Rat) : Bool :=
    if n > limit then true
    else
      let accUB' := accUB + logPrimeUB n depth
      let accLB' := accLB + logPrimeLB n depth
      if n < start then
        go start limit bound depth (n + 1) accUB' accLB'
      else if n = limit then
        decide (accUB' <= (1 + bound) * (n : Rat)) &&
        decide ((1 - bound) * (n : Rat) <= accLB')
      else
        if decide (accUB' <= (1 + bound) * (n : Rat)) &&
           decide ((1 - bound) * ((n : Rat) + 1) <= accLB') then
          go start limit bound depth (n + 1) accUB' accLB'
        else false
  termination_by limit + 1 - n

/-! ### Bridge: checkAllThetaRelErrorReal → pointwise -/

private def go_true_implies_checkAllThetaRelErrorReal
    (start limit : Nat) (bound : Rat) (depth n : Nat) (hn_pos : 0 < n)
    (accUB accLB : Rat)
    (haccUB : accUB = thetaUB (n - 1) depth)
    (haccLB : accLB = thetaLB (n - 1) depth)
    (hgo : checkAllThetaRelErrorReal.go start limit bound depth n accUB accLB = true)
    (m : Nat) (hm : n <= m) (hm_start : start <= m) (hmb : m <= limit) :
    (if m < limit then checkThetaRelErrorReal m bound depth
     else checkThetaRelError m bound depth) = true := by
  unfold checkAllThetaRelErrorReal.go at hgo
  split at hgo
  case isTrue hn_gt => omega
  case isFalse hn_le =>
    change (let accUB' := accUB + logPrimeUB n depth
            let accLB' := accLB + logPrimeLB n depth
            if n < start then _
            else if n = limit then _
            else _) = true at hgo
    simp only at hgo
    split at hgo
    case isTrue hn_lt_start =>
      exact go_true_implies_checkAllThetaRelErrorReal start limit bound depth (n + 1) (by omega)
        (accUB + logPrimeUB n depth) (accLB + logPrimeLB n depth)
        (by rw [show n + 1 - 1 = n from by omega]
            rw [thetaUB_eq_acc n hn_pos depth, haccUB])
        (by rw [show n + 1 - 1 = n from by omega]
            rw [thetaLB_eq_acc n hn_pos depth, haccLB])
        hgo m (by omega) hm_start hmb
    case isFalse hn_ge_start =>
      split at hgo
      case isTrue hn_eq_limit =>
        have hmn : m = n := by omega
        rw [if_neg (show ¬(m < limit) from by omega)]
        subst hmn
        unfold checkThetaRelError
        rw [Bool.and_eq_true] at hgo ⊢
        obtain ⟨hUB, hLB⟩ := hgo
        rw [decide_eq_true_eq] at hUB hLB
        exact ⟨decide_eq_true_eq.mpr (by rw [thetaUB_eq_acc m hn_pos depth, ← haccUB]; exact hUB),
               decide_eq_true_eq.mpr (by rw [thetaLB_eq_acc m hn_pos depth, ← haccLB]; exact hLB)⟩
      case isFalse hn_ne_limit =>
        split at hgo
        case isTrue hcheck =>
          rw [Bool.and_eq_true] at hcheck
          obtain ⟨hcheckUB, hcheckLB⟩ := hcheck
          rw [decide_eq_true_eq] at hcheckUB hcheckLB
          have hthetaUB_n : thetaUB n depth <= (1 + bound) * (n : Rat) := by
            rw [thetaUB_eq_acc n hn_pos depth, ← haccUB]; exact hcheckUB
          have hthetaLB_n : (1 - bound) * ((n : Rat) + 1) <= thetaLB n depth := by
            rw [thetaLB_eq_acc n hn_pos depth, ← haccLB]; exact hcheckLB
          by_cases hmn : m = n
          case pos =>
            rw [if_pos (show m < limit from by omega)]
            subst hmn
            unfold checkThetaRelErrorReal
            rw [Bool.and_eq_true]
            exact ⟨decide_eq_true_eq.mpr hthetaUB_n, decide_eq_true_eq.mpr hthetaLB_n⟩
          case neg =>
            exact go_true_implies_checkAllThetaRelErrorReal start limit bound depth (n + 1) (by omega)
              (accUB + logPrimeUB n depth) (accLB + logPrimeLB n depth)
              (by rw [show n + 1 - 1 = n from by omega]
                  rw [thetaUB_eq_acc n hn_pos depth, haccUB])
              (by rw [show n + 1 - 1 = n from by omega]
                  rw [thetaLB_eq_acc n hn_pos depth, haccLB])
              hgo m (by omega) hm_start hmb
        case isFalse =>
          exact absurd hgo Bool.false_ne_true
  termination_by limit + 1 - n

/-- If `checkAllThetaRelErrorReal start limit bound depth` returns true, then:
- for `N ∈ {start, ..., limit-1}`: `checkThetaRelErrorReal N bound depth` holds
- for `N = limit`: `checkThetaRelError N bound depth` holds -/
theorem checkAllThetaRelErrorReal_implies
    (start limit : Nat) (bound : Rat) (depth : Nat)
    (h : checkAllThetaRelErrorReal start limit bound depth = true)
    (N : Nat) (hN : 0 < N) (hN_start : start <= N) (hNb : N <= limit) :
    (if N < limit then checkThetaRelErrorReal N bound depth
     else checkThetaRelError N bound depth) = true :=
  go_true_implies_checkAllThetaRelErrorReal start limit bound depth 1 (by omega) 0 0
    (by simp [thetaUB]) (by simp [thetaLB]) h N (by omega) hN_start hNb

end LeanCert.Engine.ChebyshevTheta
