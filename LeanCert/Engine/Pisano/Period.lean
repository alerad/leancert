/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCert.Engine.Pisano.Defs

/-! # Pisano Period Computation

The **Pisano period** `π_{P,Q}(m)` is the smallest positive integer `k` such that
`U_k(P, Q) ≡ 0 (mod m)` and `U_{k+1}(P, Q) ≡ 1 (mod m)`.

For Fibonacci (`P=1`, `Q=-1`), this is the classical Pisano period `π(m)`.

This module now provides:
- a brute-force fallback engine for general `(P, Q)`
- an optimized Fibonacci engine using prime-power decomposition + CRT/lcm
- rank of apparition (`z(m)`) helpers for Fibonacci
-/

namespace LeanCert.Engine.Pisano

/-! ### General brute-force finder -/

/-- Search for a Lucas period by iterating the state `(U_n, U_{n+1}) mod m`. -/
private def findPeriodAux (P Q : Int) (m : Nat) : Nat → Nat → Int × Int → Nat
  | 0, _, _ => 0
  | fuel + 1, n, (u, u') =>
    let uNext := (P * u' - Q * u) % m
    let n' := n + 1
    if u' % m == 0 && uNext % m == 1 % m then n'
    else findPeriodAux P Q m fuel n' (u' % m, uNext)

/-- Brute-force period finder for general Lucas parameters `(P, Q)`.
Runs up to `m^2 + 1` steps. -/
def findPisanoPeriodBrute (P Q : Int) (m : Nat) : Nat :=
  if m ≤ 1 then 1
  else findPeriodAux P Q m (m * m + 1) 0 (0, 1 % m)

/-! ### Integer utilities for factor/divisor workflows -/

/-- Remove all factors `p` from `n`, returning `(exponent, remaining)`. -/
private def splitOffPrimePow (n p : Nat) : Nat × Nat :=
  go n 0 (n + 1)
where
  go : Nat → Nat → Nat → Nat × Nat
  | n, e, 0 => (e, n)
  | n, e, fuel + 1 =>
    if n % p == 0 then go (n / p) (e + 1) fuel else (e, n)

/-- Prime-power factorization of `n` as `[(p_1, e_1), ..., (p_r, e_r)]`. -/
private def primePowerFactors (n : Nat) : List (Nat × Nat) :=
  go n 2 [] (n + 1)
where
  go : Nat → Nat → List (Nat × Nat) → Nat → List (Nat × Nat)
  | 1, _, acc, _ => acc.reverse
  | _, _, acc, 0 => acc.reverse
  | n, p, acc, fuel + 1 =>
    if p * p > n then
      if n > 1 then ((n, 1) :: acc).reverse else acc.reverse
    else if n % p == 0 then
      let (e, rest) := splitOffPrimePow n p
      go rest (p + 1) ((p, e) :: acc) fuel
    else
      go n (p + 1) acc fuel

/-- Distinct prime factors of `n`. -/
private def primeFactors (n : Nat) : List Nat :=
  (primePowerFactors n).map Prod.fst

/-- Enumerate all divisors from a prime-power factorization. -/
private def divisorsFromPrimePowers : List (Nat × Nat) → List Nat
  | [] => [1]
  | (p, e) :: xs =>
    let tail := divisorsFromPrimePowers xs
    let powers := (List.range (e + 1)).map fun i => p ^ i
    powers.foldl (init := []) fun acc pe =>
      (tail.map fun d => pe * d) ++ acc

/-- Minimum positive element satisfying `pred`, if any. -/
private def minPositiveSatisfying (xs : List Nat) (pred : Nat → Bool) : Option Nat :=
  xs.foldl
    (init := none)
    (fun best x =>
      if x > 0 && pred x then
        match best with
        | none => some x
        | some y => some (Nat.min x y)
      else best)

/-- Compute `lcm` of a list of natural numbers. -/
private def listLcm : List Nat → Nat
  | [] => 1
  | x :: xs => Nat.lcm x (listLcm xs)

/-! ### Optimized Fibonacci period engine -/

/-- Fast period check specialized to Fibonacci (`P=1`, `Q=-1`). -/
def checkFibPeriod (m : Nat) (k : Nat) : Bool :=
  if m ≤ 1 then k == 1
  else
    let (fk, fk1) := fibPairModFast m k
    fk % m == 0 && fk1 % m == 1 % m

/-- Known upper bound for `π(p)` used by divisor filtering on primes `p`. -/
private def fibPrimePeriodUpperBound (p : Nat) : Nat :=
  if p == 2 then 3
  else if p == 5 then 20
  else if p % 10 == 1 || p % 10 == 9 then p - 1
  else 2 * (p + 1)

/-- Find the smallest period divisor of `candidate` modulo `m` (Fibonacci case). -/
private def minFibPeriodFromCandidate (m candidate : Nat) : Nat :=
  let divisors := divisorsFromPrimePowers (primePowerFactors candidate)
  match minPositiveSatisfying divisors (checkFibPeriod m) with
  | some d => d
  | none => findPisanoPeriodBrute 1 (-1) m

/-- Fibonacci Pisano period for a prime modulus `p`, using divisor minimization. -/
def findFibPisanoPeriodPrime (p : Nat) : Nat :=
  if p ≤ 1 then 1
  else minFibPeriodFromCandidate p (fibPrimePeriodUpperBound p)

/-- Fibonacci Pisano period for a prime power modulus `p^e`.
Uses the classical upper bound `π(p^e) | p^(e-1) * π(p)`. -/
def findFibPisanoPeriodPrimePow (p e : Nat) : Nat :=
  if e == 0 then 1
  else
    let m := p ^ e
    let base := findFibPisanoPeriodPrime p
    let candidate := base * p ^ (e - 1)
    minFibPeriodFromCandidate m candidate

/-- Optimized Fibonacci Pisano period using prime-power decomposition and CRT/lcm. -/
def findFibPisanoPeriod (m : Nat) : Nat :=
  if m ≤ 1 then 1
  else
    let periods := (primePowerFactors m).map fun pe =>
      findFibPisanoPeriodPrimePow pe.1 pe.2
    listLcm periods

/-- Public period finder.

For Fibonacci (`P=1`, `Q=-1`) this uses the optimized factor/divisor engine.
For other Lucas parameters it falls back to brute-force iteration. -/
def findPisanoPeriod (P Q : Int) (m : Nat) : Nat :=
  if P == 1 && Q == (-1) then findFibPisanoPeriod m
  else findPisanoPeriodBrute P Q m

/-! ### Period checker -/

/-- Check that `k` is a period of `U_n(P, Q) mod m`. -/
def checkPeriod (P Q : Int) (m : Nat) (k : Nat) : Bool :=
  if P == 1 && Q == (-1) then
    checkFibPeriod m k
  else
    lucasUMod P Q m k == 0 && lucasUMod P Q m (k + 1) % m == 1 % m

/-- Semantic period predicate for Lucas sequences modulo `m`. -/
def IsLucasPeriod (P Q : Int) (m : Nat) (k : Nat) : Prop :=
  lucasUMod P Q m k = 0 /\ lucasUMod P Q m (k + 1) % m = 1 % m

/-- Computable checker aligned exactly with `IsLucasPeriod`.
This is suitable for `native_decide` and bridge-theorem workflows. -/
def checkPeriodCore (P Q : Int) (m : Nat) (k : Nat) : Bool :=
  lucasUMod P Q m k == 0 && lucasUMod P Q m (k + 1) % m == 1 % m

/-- Golden-Theorem style bridge: a successful core check implies the semantic predicate. -/
theorem checkPeriodCore_sound (P Q : Int) (m : Nat) (k : Nat) :
    checkPeriodCore P Q m k = true -> IsLucasPeriod P Q m k := by
  intro h
  unfold checkPeriodCore at h
  unfold IsLucasPeriod
  have h' :
      (lucasUMod P Q m k == 0) = true /\
        (lucasUMod P Q m (k + 1) % m == 1 % m) = true := by
    simpa [Bool.and_eq_true] using h
  have h0 : (lucasUMod P Q m k == 0) = true := h'.1
  have h1 : (lucasUMod P Q m (k + 1) % m == 1 % m) = true := h'.2
  exact And.intro (LawfulBEq.eq_of_beq h0) (LawfulBEq.eq_of_beq h1)

/-- Completeness direction for the core checker. -/
theorem IsLucasPeriod_checkPeriodCore_true (P Q : Int) (m : Nat) (k : Nat) :
    IsLucasPeriod P Q m k -> checkPeriodCore P Q m k = true := by
  intro h
  have h0 : lucasUMod P Q m k = 0 := h.1
  have h1 : lucasUMod P Q m (k + 1) % m = 1 % m := h.2
  simp [checkPeriodCore, h0, h1]

/-- Check that `k` is the *minimal* period modulo `m`. -/
def checkPisanoPeriod (P Q : Int) (m : Nat) (k : Nat) : Bool :=
  k > 0 && checkPeriod P Q m k &&
  (List.range (k - 1)).all fun d =>
    if d + 1 < k && k % (d + 1) == 0 then
      !checkPeriod P Q m (d + 1)
    else true

/-! ### Pisano fixed points -/

/-- Check whether `b` is a Pisano fixed point for Lucas `(P, Q)`:
`b = lcm(π_{P,Q}(p) : p prime, p | b)`. -/
def checkPisanoFixedPoint (P Q : Int) (b : Nat) : Bool :=
  let periods := (primeFactors b).map fun p => findPisanoPeriod P Q p
  listLcm periods == b

/-- Search all Pisano fixed points up to `limit`. -/
def findPisanoFixedPoints (P Q : Int) (limit : Nat) : List Nat :=
  (List.range limit).filterMap fun n =>
    let b := n + 2
    if checkPisanoFixedPoint P Q b then some b else none

/-! ### Rank of apparition (`z(m)`) for Fibonacci -/

/-- Fibonacci rank of apparition `z(m)`: the least `k > 0` with `F_k ≡ 0 (mod m)`. -/
def findFibRankOfApparition (m : Nat) : Nat :=
  if m ≤ 1 then 1
  else
    let pi := findFibPisanoPeriod m
    let divisors := divisorsFromPrimePowers (primePowerFactors pi)
    match minPositiveSatisfying divisors (fun d => fibModFast m d % m == 0) with
    | some d => d
    | none => pi

/-- Runtime checker for the relation `z(m) | π(m)` (Fibonacci case). -/
def checkFibRankDividesPeriod (m : Nat) : Bool :=
  if m ≤ 1 then true
  else
    let z := findFibRankOfApparition m
    let pi := findFibPisanoPeriod m
    z > 0 && pi % z == 0

end LeanCert.Engine.Pisano
