/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCert.Engine.Pisano

/-! # Pisano Period Tests

Covers:
- known period tables
- optimized Fibonacci period engine vs brute-force reference
- randomized congruence checks for fast-doubling routines
- rank of apparition checks
- small benchmark output for fast vs brute period search
-/

open LeanCert.Engine.Pisano

/-! ### Known Fibonacci Pisano periods -/

#guard findPisanoPeriod 1 (-1) 2 = 3
#guard findPisanoPeriod 1 (-1) 3 = 8
#guard findPisanoPeriod 1 (-1) 5 = 20
#guard findPisanoPeriod 1 (-1) 7 = 16
#guard findPisanoPeriod 1 (-1) 11 = 10
#guard findPisanoPeriod 1 (-1) 13 = 28

/-! ### Known non-Fibonacci period checks (brute fallback path) -/

#guard findPisanoPeriod 2 (-1) 2 = 2
#guard findPisanoPeriod 2 (-1) 3 = 8
#guard findPisanoPeriod 2 (-1) 5 = 12
#guard findPisanoPeriod 2 (-1) 7 = 6

#guard findPisanoPeriod 3 (-1) 2 = 3
#guard findPisanoPeriod 3 (-1) 3 = 2
#guard findPisanoPeriod 3 (-1) 13 = 52

#guard findPisanoPeriod 3 1 2 = 3
#guard findPisanoPeriod 3 1 3 = 4
#guard findPisanoPeriod 3 1 5 = 10

/-! ### Prime-power + CRT/lcm path checks -/

#guard findFibPisanoPeriodPrimePow 2 5 = 48
#guard findFibPisanoPeriodPrimePow 3 2 = 24
#guard findFibPisanoPeriodPrimePow 5 2 = 100

-- 45 = 9 * 5, coprime factors, so pi(45) = lcm(pi(9), pi(5)).
#guard
  findFibPisanoPeriod 45 =
    Nat.lcm (findFibPisanoPeriodPrimePow 3 2) (findFibPisanoPeriodPrimePow 5 1)

/-! ### Optimized engine agrees with brute reference -/

private def checkFibOptimizedMatchesBruteAux : Nat -> Nat -> Bool
  | 0, _ => true
  | fuel + 1, m =>
    findFibPisanoPeriod m == findPisanoPeriodBrute 1 (-1) m &&
      checkFibOptimizedMatchesBruteAux fuel (m + 1)

/-- Check `findFibPisanoPeriod = findPisanoPeriodBrute 1 (-1)` on `[start, start+count)`. -/
def checkFibOptimizedMatchesBrute (count : Nat) (start : Nat := 2) : Bool :=
  checkFibOptimizedMatchesBruteAux count start

example : checkFibOptimizedMatchesBrute 200 = true := by native_decide

/-! ### Core checker bridge theorem (Golden-Theorem style) -/

example :
    LeanCert.Engine.Pisano.IsLucasPeriod 1 (-1) 13 (findPisanoPeriod 1 (-1) 13) := by
  exact
    LeanCert.Engine.Pisano.checkPeriodCore_sound 1 (-1) 13
      (findPisanoPeriod 1 (-1) 13) (by native_decide)

/-! ### Fast-doubling congruence property checks -/

private def lcgStep (x : Nat) : Nat :=
  (1664525 * x + 1013904223) % 4294967296

private def checkFibFastModAgreementAux : Nat -> Nat -> Bool
  | 0, _ => true
  | fuel + 1, seed =>
    let s1 := lcgStep seed
    let m := s1 % 997 + 2
    let s2 := lcgStep s1
    let n := s2 % 5000
    let fast := fibModFast m n % m
    let slow := lucasUMod 1 (-1) m n % m
    fast == slow && checkFibFastModAgreementAux fuel s2

/-- Deterministic random-like check: fast `F_n mod m` equals linear reference. -/
def checkFibFastModAgreement (samples : Nat) : Bool :=
  checkFibFastModAgreementAux samples 123456789

private def checkLucasFastModAgreementAux : Nat -> Nat -> Bool
  | 0, _ => true
  | fuel + 1, seed =>
    let s1 := lcgStep seed
    let m := s1 % 997 + 2
    let s2 := lcgStep s1
    let n := s2 % 5000
    let fast := lucasFibModFast m n % m
    let slow := lucasVMod 1 (-1) m n % m
    fast == slow && checkLucasFastModAgreementAux fuel s2

/-- Deterministic random-like check: fast `L_n mod m` equals linear reference. -/
def checkLucasFastModAgreement (samples : Nat) : Bool :=
  checkLucasFastModAgreementAux samples 987654321

example : checkFibFastModAgreement 3000 = true := by native_decide
example : checkLucasFastModAgreement 3000 = true := by native_decide

/-! ### Rank of apparition checks -/

#guard findFibRankOfApparition 2 = 3
#guard findFibRankOfApparition 3 = 4
#guard findFibRankOfApparition 5 = 5
#guard findFibRankOfApparition 7 = 8

example : checkFibRankDividesPeriod 1000 = true := by native_decide

/-! ### Pisano fixed points -/

#guard findPisanoFixedPoints 1 (-1) 200 = [24, 120]
#guard findPisanoFixedPoints 2 (-1) 200 = [2]
#guard findPisanoFixedPoints 3 (-1) 200 = [6, 156]
#guard findPisanoFixedPoints 3 1 200 = [12, 60]
#guard findPisanoFixedPoints 4 1 200 = [2, 6]

/-! ### Micro-benchmark: optimized Fibonacci period vs brute -/

def benchmarkFibPisano : IO Unit := do
  let totalStart <- IO.monoMsNow
  for m in [233, 377, 701, 997] do
    let t0 <- IO.monoMsNow
    let fast := findFibPisanoPeriod m
    let t1 <- IO.monoMsNow
    let brute := findPisanoPeriodBrute 1 (-1) m
    let t2 <- IO.monoMsNow
    IO.println s!"m={m}: fast={fast} ({t1 - t0} ms), brute={brute} ({t2 - t1} ms)"
  let totalStop <- IO.monoMsNow
  IO.println s!"benchmark total: {totalStop - totalStart} ms"

#eval benchmarkFibPisano
