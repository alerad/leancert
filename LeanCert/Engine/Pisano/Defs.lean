/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic

/-! # Lucas Sequences — Computable Definitions

We define the generalized Lucas sequences `U_n(P, Q)` and `V_n(P, Q)` satisfying:
- `U_0 = 0, U_1 = 1, U_{n+2} = P · U_{n+1} - Q · U_n`
- `V_0 = 2, V_1 = P, V_{n+2} = P · V_{n+1} - Q · V_n`

Special cases:
- Fibonacci: `U_n(1, -1) = F_n`
- Pell: `U_n(2, -1) = P_n`
- Lucas numbers: `V_n(1, -1) = L_n`

All definitions are computable over `ℤ` for use with `native_decide`. -/

namespace LeanCert.Engine.Pisano

/-! ### Lucas sequence computation -/

/-- Compute `(U_n, U_{n+1})` for the Lucas U-sequence with parameters `(P, Q)` over `ℤ`. -/
def lucasUPair (P Q : Int) : Nat → Int × Int
  | 0 => (0, 1)
  | n + 1 =>
    let (u, u') := lucasUPair P Q n
    (u', P * u' - Q * u)

/-- The Lucas U-sequence: `U_n(P, Q)`. -/
def lucasU (P Q : Int) (n : Nat) : Int :=
  (lucasUPair P Q n).1

/-- Compute `(V_n, V_{n+1})` for the Lucas V-sequence with parameters `(P, Q)` over `ℤ`. -/
def lucasVPair (P Q : Int) : Nat → Int × Int
  | 0 => (2, P)
  | n + 1 =>
    let (v, v') := lucasVPair P Q n
    (v', P * v' - Q * v)

/-- The Lucas V-sequence: `V_n(P, Q)`. -/
def lucasV (P Q : Int) (n : Nat) : Int :=
  (lucasVPair P Q n).1

/-! ### Modular versions -/

/-- Compute `(U_n mod m, U_{n+1} mod m)` efficiently, reducing at each step. -/
def lucasUPairMod (P Q : Int) (m : Nat) : Nat → Int × Int
  | 0 => (0, 1 % m)
  | n + 1 =>
    let (u, u') := lucasUPairMod P Q m n
    (u' % m, (P * u' - Q * u) % m)

/-- `U_n(P, Q) mod m`, computed efficiently with modular reduction at each step. -/
def lucasUMod (P Q : Int) (m : Nat) (n : Nat) : Int :=
  (lucasUPairMod P Q m n).1

/-- Compute `(V_n mod m, V_{n+1} mod m)` efficiently, reducing at each step. -/
def lucasVPairMod (P Q : Int) (m : Nat) : Nat → Int × Int
  | 0 => (2 % m, P % m)
  | n + 1 =>
    let (v, v') := lucasVPairMod P Q m n
    (v' % m, (P * v' - Q * v) % m)

/-- `V_n(P, Q) mod m`, computed efficiently with modular reduction at each step. -/
def lucasVMod (P Q : Int) (m : Nat) (n : Nat) : Int :=
  (lucasVPairMod P Q m n).1

/-- Fast-doubling Fibonacci pair `(F_n mod m, F_{n+1} mod m)` in `O(log n)`. -/
private def fibPairModFastAux (m : Nat) : Nat → Int × Int
  | 0 => (0, 1 % m)
  | Nat.succ n =>
    let k : Nat := Nat.succ n
    let (a, b) := fibPairModFastAux m (k / 2)
    let c := (a * ((2 * b - a) % m)) % m
    let d := (a * a + b * b) % m
    if k % 2 == 0 then (c, d) else (d, (c + d) % m)
termination_by n => n
decreasing_by
  have h : (Nat.succ n) / 2 < Nat.succ n := by
    exact Nat.div_lt_self (Nat.succ_pos n) (by decide)
  simpa using h

/-- Fast-doubling Fibonacci pair `(F_n mod m, F_{n+1} mod m)`. -/
def fibPairModFast (m : Nat) (n : Nat) : Int × Int :=
  fibPairModFastAux m n

/-- `F_n mod m` computed via fast-doubling in `O(log n)`. -/
def fibModFast (m : Nat) (n : Nat) : Int :=
  (fibPairModFast m n).1

/-- `L_n mod m` for the classical Lucas numbers (`P=1`, `Q=-1`) in `O(log n)`. -/
def lucasFibModFast (m : Nat) (n : Nat) : Int :=
  let (fn, fn1) := fibPairModFast m n
  (2 * fn1 - fn) % m

/-! ### Basic recurrence lemmas -/

@[simp] theorem lucasUPair_zero (P Q : Int) : lucasUPair P Q 0 = (0, 1) := rfl

theorem lucasUPair_succ (P Q : Int) (n : Nat) :
    lucasUPair P Q (n + 1) =
      let (u, u') := lucasUPair P Q n
      (u', P * u' - Q * u) := rfl

@[simp] theorem lucasU_zero (P Q : Int) : lucasU P Q 0 = 0 := rfl

@[simp] theorem lucasU_one (P Q : Int) : lucasU P Q 1 = 1 := rfl

theorem lucasU_succ_succ (P Q : Int) (n : Nat) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := by
  simp only [lucasU, lucasUPair]

/-! ### Connection to Nat.fib (Fibonacci = Lucas U with P=1, Q=-1) -/

theorem lucasU_fib (n : Nat) : lucasU 1 (-1) n = Nat.fib n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [Nat.fib]
    | n + 2 =>
      rw [lucasU_succ_succ]
      simp only [one_mul]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      rw [Nat.fib_add_two]
      omega

/-! ### Modular congruence -/

private theorem lucasUPairMod_eq_mod (P Q : Int) (m : Nat) (n : Nat) :
    lucasUPairMod P Q m n =
      ((lucasUPair P Q n).1 % m, (lucasUPair P Q n).2 % m) := by
  induction n with
  | zero =>
    simp [lucasUPairMod, lucasUPair]
  | succ n ih =>
    simp only [lucasUPairMod, lucasUPair]
    rw [ih]
    ext
    · -- fst: (snd % m) % m = snd % m
      exact Int.emod_emod_of_dvd _ dvd_rfl
    · -- snd: (P * (snd % m) - Q * (fst % m)) % m = (P * snd - Q * fst) % m
      rw [Int.sub_emod, Int.mul_emod (a := P), Int.mul_emod (a := Q)]
      simp only [Int.emod_emod_of_dvd _ dvd_rfl]
      rw [← Int.mul_emod (a := P), ← Int.mul_emod (a := Q), ← Int.sub_emod]

theorem lucasUMod_eq_mod (P Q : Int) (m : Nat) (_hm : 0 < m) (n : Nat) :
    lucasUMod P Q m n = lucasU P Q n % m := by
  simp only [lucasUMod, lucasU, lucasUPairMod_eq_mod P Q m n]

private theorem lucasVPairMod_eq_mod (P Q : Int) (m : Nat) (n : Nat) :
    lucasVPairMod P Q m n =
      ((lucasVPair P Q n).1 % m, (lucasVPair P Q n).2 % m) := by
  induction n with
  | zero =>
    simp [lucasVPairMod, lucasVPair]
  | succ n ih =>
    simp only [lucasVPairMod, lucasVPair]
    rw [ih]
    ext
    · exact Int.emod_emod_of_dvd _ dvd_rfl
    · rw [Int.sub_emod, Int.mul_emod (a := P), Int.mul_emod (a := Q)]
      simp only [Int.emod_emod_of_dvd _ dvd_rfl]
      rw [← Int.mul_emod (a := P), ← Int.mul_emod (a := Q), ← Int.sub_emod]

theorem lucasVMod_eq_mod (P Q : Int) (m : Nat) (_hm : 0 < m) (n : Nat) :
    lucasVMod P Q m n = lucasV P Q n % m := by
  simp only [lucasVMod, lucasV, lucasVPairMod_eq_mod P Q m n]

end LeanCert.Engine.Pisano
