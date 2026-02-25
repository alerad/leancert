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

/-! ### Known Fibonacci Pisano periods `π(p)` -/

#eval findPisanoPeriod 1 (-1) 2   -- expect 3
#eval findPisanoPeriod 1 (-1) 3   -- expect 8
#eval findPisanoPeriod 1 (-1) 5   -- expect 20
#eval findPisanoPeriod 1 (-1) 7   -- expect 16
#eval findPisanoPeriod 1 (-1) 11  -- expect 10
#eval findPisanoPeriod 1 (-1) 13  -- expect 28

/-! ### Known non-Fibonacci period checks (brute fallback path) -/

#eval findPisanoPeriod 2 (-1) 2   -- expect 2
#eval findPisanoPeriod 2 (-1) 3   -- expect 8
#eval findPisanoPeriod 2 (-1) 5   -- expect 12
#eval findPisanoPeriod 2 (-1) 7   -- expect 6

#eval findPisanoPeriod 3 (-1) 2   -- expect 3
#eval findPisanoPeriod 3 (-1) 3   -- expect 2
#eval findPisanoPeriod 3 (-1) 13  -- expect 52

#eval findPisanoPeriod 3 1 2      -- expect 3
#eval findPisanoPeriod 3 1 3      -- expect 4
#eval findPisanoPeriod 3 1 5      -- expect 10

/-! ### Prime-power + CRT/lcm path checks -/

#eval findFibPisanoPeriodPrimePow 2 5   -- expect 48 (mod 32)
#eval findFibPisanoPeriodPrimePow 3 2   -- expect 24 (mod 9)
#eval findFibPisanoPeriodPrimePow 5 2   -- expect 100 (mod 25)

-- `45 = 9 * 5`, coprime factors, so `π(45) = lcm(π(9), π(5))`.
#eval
  findFibPisanoPeriod 45 ==
    Nat.lcm (findFibPisanoPeriodPrimePow 3 2) (findFibPisanoPeriodPrimePow 5 1)

/-! ### Optimized engine agrees with brute reference -/

private def checkFibOptimizedMatchesBruteAux : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, m =>
    findFibPisanoPeriod m == findPisanoPeriodBrute 1 (-1) m &&
      checkFibOptimizedMatchesBruteAux fuel (m + 1)

/-- Check `findFibPisanoPeriod = findPisanoPeriodBrute 1 (-1)` on `[start, start+count)`. -/
def checkFibOptimizedMatchesBrute (count : Nat) (start : Nat := 2) : Bool :=
  checkFibOptimizedMatchesBruteAux count start

#eval checkFibOptimizedMatchesBrute 200

/-! ### Fast-doubling congruence property checks -/

private def lcgStep (x : Nat) : Nat :=
  (1664525 * x + 1013904223) % 4294967296

private def checkFibFastModAgreementAux : Nat → Nat → Bool
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

private def checkLucasFastModAgreementAux : Nat → Nat → Bool
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

#eval checkFibFastModAgreement 3000
#eval checkLucasFastModAgreement 3000

/-! ### Rank of apparition (`z(m)`) checks -/

#eval findFibRankOfApparition 2   -- expect 3
#eval findFibRankOfApparition 3   -- expect 4
#eval findFibRankOfApparition 5   -- expect 5
#eval findFibRankOfApparition 7   -- expect 8

#eval checkFibRankDividesPeriod 1000  -- expect true

/-! ### Pisano fixed points -/

#eval findPisanoFixedPoints 1 (-1) 200  -- expect [24, 120]
#eval findPisanoFixedPoints 2 (-1) 200  -- expect [2]
#eval findPisanoFixedPoints 3 (-1) 200  -- expect [6, 156]
#eval findPisanoFixedPoints 3 1 200     -- expect [12, 60]
#eval findPisanoFixedPoints 4 1 200     -- expect [2, 6]

/-! ### Micro-benchmark: optimized Fibonacci period vs brute -/

def benchmarkFibPisano : IO Unit := do
  let totalStart ← IO.monoMsNow
  for m in [233, 377, 701, 997] do
    let t0 ← IO.monoMsNow
    let fast := findFibPisanoPeriod m
    let t1 ← IO.monoMsNow
    let brute := findPisanoPeriodBrute 1 (-1) m
    let t2 ← IO.monoMsNow
    IO.println s!"m={m}: fast={fast} ({t1 - t0} ms), brute={brute} ({t2 - t1} ms)"
  let totalStop ← IO.monoMsNow
  IO.println s!"benchmark total: {totalStop - totalStart} ms"

#eval benchmarkFibPisano
