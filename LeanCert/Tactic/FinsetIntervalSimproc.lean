/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public meta import Mathlib.Util.Qq
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.Int

/-!
# Simprocs computing intervals of numerals

This is a copy of `Mathlib.Tactic.Simproc.FinsetInterval` (`Finset.Icc_ofNat_ofNat` and friends)
whose auxiliary lemmas are public.

The Mathlib simprocs build proofs out of `private` lemmas. Under the module system, private
declarations of imported modules are not available, so any proof produced by those simprocs in a
`module` file is rejected by the kernel with an unknown constant error. Drop this file in favour of
the Mathlib simprocs once their lemmas are public.
-/

open Qq Lean Finset

namespace LeanCert.Tactic.FinsetInterval

/-! ### Auxiliary lemmas -/

public section

namespace Nat
variable {m n : ℕ} {s : Finset ℕ}

theorem Icc_eq_empty_of_lt (hnm : n.blt m) : Icc m n = ∅ := by simpa using hnm

theorem Icc_eq_insert_of_Icc_succ_eq (hmn : m.ble n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

theorem Ico_succ_eq_of_Icc_eq (hs : Icc m n = s) : Ico m (n + 1) = s := by
  rw [← hs, Ico_add_one_right_eq_Icc]

theorem Ico_zero (m : ℕ) : Ico m 0 = ∅ := by simp

theorem Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs, Icc_add_one_left_eq_Ioc]

theorem Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs, ← Icc_add_one_sub_one_eq_Ioo]

theorem Iic_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iic n = s := hs

theorem Iio_succ_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iio (n + 1) = s := by
  rw [Iio_eq_Ico, Ico_add_one_right_eq_Icc, bot_eq_zero, hs]

theorem Iio_zero : Iio 0 = ∅ := by simp

end Nat

namespace Int
variable {m n : ℤ} {s : Finset ℤ}

theorem Icc_eq_empty_of_lt (hnm : n < m) : Icc m n = ∅ := by simpa using hnm

theorem Icc_eq_insert_of_Icc_succ_eq (hmn : m ≤ n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

theorem Ico_eq_of_Icc_pred_eq (hs : Icc m (n - 1) = s) : Ico m n = s := by
  rw [← hs, Icc_sub_one_right_eq_Ico]

theorem Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs, Icc_add_one_left_eq_Ioc]

theorem Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs, ← Icc_add_one_sub_one_eq_Ioo]

end Int

end

/-! ### Interval evaluation -/

public meta section

/-- Given natural numbers `m` and `n` and corresponding natural literals `em` and `en`,
returns `(s, ⊢ Finset.Icc m n = s)`. -/
def evalFinsetIccNat (m n : ℕ) (em en : Q(ℕ)) :
    MetaM ((s : Q(Finset ℕ)) × Q(.Icc $em $en = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
    have : $em =Q $en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc (m + 1) n)`.
  else if m < n then
    let hmn : Q(Nat.ble $em $en = true) := (q(Eq.refl true) :)
    have em' : Q(ℕ) := mkNatLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccNat (m + 1) n em' en
    return ⟨q(insert $em $s), q(Nat.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm : Q(Nat.blt $en $em = true) := (q(Eq.refl true) :)
    return ⟨q(∅), q(Nat.Icc_eq_empty_of_lt $hnm)⟩

/-- Given integers `m` and `n` and corresponding integer literals `em` and `en`,
returns `(s, ⊢ Finset.Icc m n = s)`. -/
partial def evalFinsetIccInt (m n : ℤ) (em en : Q(ℤ)) :
    MetaM ((s : Q(Finset ℤ)) × Q(.Icc $em $en = $s)) := do
  if m = n then
    have : $em =Q $en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  else if m < n then
    let hmn ← mkDecideProofQ q($em ≤ $en)
    have em' : Q(ℤ) := mkIntLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccInt (m + 1) n em' en
    return ⟨q(insert $em $s), q(Int.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  else
    let hnm ← mkDecideProofQ q($en < $em)
    return ⟨q(∅), q(Int.Icc_eq_empty_of_lt $hnm)⟩

/-! ### Simprocs

These are not `simp` simprocs, to avoid `simp` blowing up on goals such as `Iic (2 ^ 1024)`.
With the standard recursion depth limit, they compute intervals of size 250 at most. -/

/-- Simproc to compute `Finset.Icc a b` where `a` and `b` are numerals. -/
simproc_decl Icc_ofNat_ofNat (Icc _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Icc $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat m n em en
    return .done <| .mk es <| .some p
  | 1, ~q(Finset ℤ), ~q(Icc $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccInt m n em en
    return .done <| .mk es <| .some p
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ico a b` where `a` and `b` are numerals. -/
simproc_decl Ico_ofNat_ofNat (Ico _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ico $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    match n with
    | 0 =>
      have : $en =Q 0 := ⟨⟩
      return .done <| .mk q(∅) <| .some q(Nat.Ico_zero $em)
    | n + 1 =>
      have en' := mkNatLitQ n
      have : $en =Q $en' + 1 := ⟨⟩
      let ⟨es, p⟩ ← evalFinsetIccNat m n em en'
      return .done { expr := es, proof? := q(Nat.Ico_succ_eq_of_Icc_eq $p) }
  | 1, ~q(Finset ℤ), ~q(Ico $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have en' := mkIntLitQ (n - 1)
    have : $en' =Q $en - 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt m (n - 1) em en'
    return .done { expr := es, proof? := q(Int.Ico_eq_of_Icc_pred_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioc a b` where `a` and `b` are numerals. -/
simproc_decl Ioc_ofNat_ofNat (Ioc _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ioc $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    have em' := mkNatLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) n em' en
    return .done <| .mk es <| .some q(Nat.Ioc_eq_of_Icc_succ_eq $p)
  | 1, ~q(Finset ℤ), ~q(Ioc $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have em' := mkIntLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt (m + 1) n em' en
    return .done { expr := es, proof? := q(Int.Ioc_eq_of_Icc_succ_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioo a b` where `a` and `b` are numerals. -/
simproc_decl Ioo_ofNat_ofNat (Ioo _ _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Ioo $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) (n - 1) q($em + 1) q($en - 1)
    return .done <| .mk es <| .some q(Nat.Ioo_eq_of_Icc_succ_pred_eq $p)
  | 1, ~q(Finset ℤ), ~q(Ioo $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have em' := mkIntLitQ (m + 1)
    have : $em' =Q $em + 1 := ⟨⟩
    have en' := mkIntLitQ (n - 1)
    have : $en' =Q $en - 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt (m + 1) (n - 1) em' en'
    return .done { expr := es, proof? := q(Int.Ioo_eq_of_Icc_succ_pred_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iic b` where `b` is a numeral. -/
simproc_decl Iic_ofNat (Iic _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Iic $en) =>
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) en
    return .done <| .mk es <| .some q(Nat.Iic_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iio b` where `b` is a numeral. -/
simproc_decl Iio_ofNat (Iio _) := .ofQ fun u α e ↦ do
  match u, α, e with
  | 1, ~q(Finset ℕ), ~q(Iio $en) =>
    let some n := en.nat? | return .continue
    match n with
    | 0 =>
      have : $en =Q 0 := ⟨⟩
      return .done <| .mk q(∅) <| .some q(Nat.Iio_zero)
    | n + 1 =>
      have en' := mkNatLitQ n
      have : $en =Q $en' + 1 := ⟨⟩
      let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) q($en')
      return .done <| .mk es <| some q(Nat.Iio_succ_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

end

end LeanCert.Tactic.FinsetInterval
