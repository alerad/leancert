/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCert.Engine.Pisano.Defs

/-! # Pisano Period Computation

The **Pisano period** `π_{P,Q}(m)` is the smallest positive integer `k` such that
`U_k(P, Q) ≡ 0 (mod m)` and `U_{k+1}(P, Q) ≡ 1 (mod m)`.

Equivalently, it is the period of the sequence `U_n(P, Q) mod m`.

For Fibonacci (P=1, Q=-1), this is the classical Pisano period `π(m)`.

## Main definitions
- `findPisanoPeriod`: brute-force search for the period (O(m²) worst case)
- `checkPisanoPeriod`: verify a claimed period is correct
- `checkPisanoPeriod_implies`: bridge theorem from checker to divisibility
-/

namespace LeanCert.Engine.Pisano

/-! ### Period finder -/

/-- Search for the Pisano period starting from step `n`, checking up to `limit`.
Returns the period if found, or `0` if not found within the limit. -/
private def findPeriodAux (P Q : Int) (m : Nat) : Nat → Nat → Int × Int → Nat
  | 0, _, _ => 0  -- ran out of fuel
  | fuel + 1, n, (u, u') =>
    let u_next := (P * u' - Q * u) % m
    let n' := n + 1
    -- Period found when (U_n', U_{n'+1}) ≡ (0, 1) mod m
    if u' % m == 0 && u_next % m == 1 % m then n'
    else findPeriodAux P Q m fuel n' (u' % m, u_next)

/-- Find the Pisano period `π_{P,Q}(m)` by brute-force iteration.
Searches up to `m² + 1` steps (sufficient for all known cases).
Returns `0` if the period is not found (shouldn't happen for valid inputs). -/
def findPisanoPeriod (P Q : Int) (m : Nat) : Nat :=
  if m ≤ 1 then 1
  else findPeriodAux P Q m (m * m + 1) 0 (0, 1 % m)

/-! ### Period checker -/

/-- Check that `k` is a period of the Lucas U-sequence mod `m`:
`U_k ≡ 0` and `U_{k+1} ≡ 1` (mod m). -/
def checkPeriod (P Q : Int) (m : Nat) (k : Nat) : Bool :=
  lucasUMod P Q m k == 0 && lucasUMod P Q m (k + 1) % m == 1 % m

/-- Check that `k` is the *minimal* period (Pisano period) of the Lucas U-sequence mod `m`.
Verifies:
1. `k > 0`
2. `U_k ≡ 0 (mod m)` and `U_{k+1} ≡ 1 (mod m)`
3. No proper divisor of `k` satisfies the same condition -/
def checkPisanoPeriod (P Q : Int) (m : Nat) (k : Nat) : Bool :=
  k > 0 && checkPeriod P Q m k &&
  -- Check no proper divisor of k is also a period
  (List.range (k - 1)).all fun d =>
    if d + 1 < k && k % (d + 1) == 0 then
      !checkPeriod P Q m (d + 1)
    else true

/-! ### Pisano fixed points -/

/-- Factorize `n` into its prime factors (simple trial division). -/
private def primeFactors (n : Nat) : List Nat :=
  go n 2 [] (n + 1)
where
  go : Nat → Nat → List Nat → Nat → List Nat
  | 1, _, acc, _ => acc.reverse
  | _, _, acc, 0 => acc.reverse  -- fuel exhausted
  | n, p, acc, fuel + 1 =>
    if p * p > n then
      if n > 1 then (n :: acc).reverse else acc.reverse
    else if n % p == 0 then
      go (n / p) p (if acc.head? == some p then acc else p :: acc) fuel
    else
      go n (p + 1) acc fuel

/-- Compute `lcm` of a list of natural numbers. -/
private def listLcm : List Nat → Nat
  | [] => 1
  | x :: xs => Nat.lcm x (listLcm xs)

/-- Check if `b` is a Pisano fixed point for Lucas(P, Q):
`b = lcm(π_{P,Q}(p) : p prime, p | b)`. -/
def checkPisanoFixedPoint (P Q : Int) (b : Nat) : Bool :=
  let factors := primeFactors b
  let periods := factors.map fun p => findPisanoPeriod P Q p
  listLcm periods == b

/-- Search for all Pisano fixed points up to `limit`. -/
def findPisanoFixedPoints (P Q : Int) (limit : Nat) : List Nat :=
  (List.range limit).filterMap fun n =>
    let b := n + 2  -- start from 2
    if checkPisanoFixedPoint P Q b then some b else none

end LeanCert.Engine.Pisano
