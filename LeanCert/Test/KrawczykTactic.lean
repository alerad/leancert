/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.Krawczyk
import LeanCert.Tactic

/-! Generalized I1 regressions for the manual Krawczyk tactic front end. -/

namespace LeanCert.Test.KrawczykTactic

open LeanCert.Core LeanCert.Engine LeanCert.Validity
open LeanCert.Examples.Krawczyk
open LeanCert.Tactic

/- A translated scalar root checks that the front end is not specialized to
centers near zero. -/
def translatedSystem : Fin 1 → Expr :=
  ![Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const (-4))]

def translatedBox : Fin 1 → IntervalRat :=
  ![⟨19 / 10, 21 / 10, by norm_num⟩]

def translatedCert : KrawczykCert 1 where
  center := ![2]
  preconditioner := !![1 / 4]

/- Checked AD and interval Jacobians are exercised by a genuinely coupled
transcendental system with root `(0, 1)`. -/
def mixedSystem : Fin 2 → Expr :=
  let x := Expr.var 0
  let y := Expr.var 1
  ![Expr.add (Expr.add (Expr.exp x) y) (Expr.const (-2)),
    Expr.add (Expr.add x (Expr.mul y y)) (Expr.const (-1))]

def mixedBox : Fin 2 → IntervalRat :=
  ![⟨-1 / 20, 1 / 20, by norm_num⟩,
    ⟨19 / 20, 21 / 20, by norm_num⟩]

def mixedCert : KrawczykCert 2 where
  center := ![0, 1]
  preconditioner := !![2, -1; -1, 1]

/- Cyclic coupling and a rational 3×3 inverse exercise dimension-generic
matrix handling. -/
def cyclicSystem : Fin 3 → Expr :=
  let x := Expr.var 0
  let y := Expr.var 1
  let z := Expr.var 2
  ![Expr.add (Expr.add (Expr.mul x x) y) (Expr.const (-2)),
    Expr.add (Expr.add (Expr.mul y y) z) (Expr.const (-2)),
    Expr.add (Expr.add (Expr.mul z z) x) (Expr.const (-2))]

def cyclicBox : Fin 3 → IntervalRat := fun _ =>
  ⟨19 / 20, 21 / 20, by norm_num⟩

def cyclicCert : KrawczykCert 3 where
  center := ![1, 1, 1]
  preconditioner := !![4 / 9, -2 / 9, 1 / 9;
    1 / 9, 4 / 9, -2 / 9;
    -2 / 9, 1 / 9, 4 / 9]

/- A generated family above the showcase dimensions catches accidental
hard-coding of `n = 1`, `2`, or `3`. -/
def identitySystem : Fin 4 → Expr := fun i => Expr.var i

def identityBox : Fin 4 → IntervalRat := fun _ =>
  ⟨-1 / 10, 1 / 10, by norm_num⟩

def identityCert : KrawczykCert 4 where
  center := fun _ => 0
  preconditioner := 1

example : ∃! p, FinBoxMem p translatedBox ∧ SystemZero translatedSystem p := by
  system_unique_root using translatedCert (trust := kernel)

example : ∃! p, FinBoxMem p mixedBox ∧ SystemZero mixedSystem p := by
  system_unique_root using mixedCert (trust := native)

example : ∃! p, FinBoxMem p cyclicBox ∧ SystemZero cyclicSystem p := by
  system_unique_root using cyclicCert (trust := auto)

example : ∃! p, FinBoxMem p expBox ∧ SystemZero expSystem p := by
  system_unique_root? using expCertificate (trust := kernel)

example : ∃! p, FinBoxMem p identityBox ∧ SystemZero identitySystem p := by
  system_unique_root using identityCert (trust := kernel)

example : ∃! p, FinBoxMem p mixedBox ∧ SystemZero mixedSystem p := by
  let localCert := mixedCert
  system_unique_root using localCert (trust := kernel)

/- Inline candidates and option order are part of the public elaboration
boundary, not an implementation accident of named declarations. -/
example : ∃! p, FinBoxMem p translatedBox ∧ SystemZero translatedSystem p := by
  system_unique_root using
    ({ center := ![2], preconditioner := !![1 / 4] } : KrawczykCert 1)
    (trust := auto) (taylorDepth := 10)

example : True := by
  let localSystem := translatedSystem
  let localBox := translatedBox
  have : ∃! p, FinBoxMem p localBox ∧ SystemZero localSystem p := by
    system_unique_root using translatedCert
  trivial

/- The source conjunction order is presentation, not part of the tactic's
mathematical contract. -/
example : ∃! p, SystemZero system p ∧ FinBoxMem p box := by
  system_unique_root using certificate

def singularCert : KrawczykCert 2 where
  center := ![1, 1]
  preconditioner := 0

def outsideCert : KrawczykCert 2 where
  center := ![3, 3]
  preconditioner := certificate.preconditioner

def wideBox : Fin 2 → IntervalRat := fun _ => ⟨0, 2, by norm_num⟩

def unsupportedSystem : Fin 2 → Expr := ![Expr.log (Expr.var 0), Expr.var 1]

def imageBox : Fin 2 → IntervalRat := fun _ =>
  ⟨9 / 10, 99 / 100, by norm_num⟩

def imageCert : KrawczykCert 2 where
  center := ![19 / 20, 19 / 20]
  preconditioner := certificate.preconditioner

#guard (inspectKrawczyk system box singularCert).stage ==
  .singularPreconditioner
#guard (inspectKrawczyk system box outsideCert).stage == .centerOutside
#guard (inspectKrawczyk system wideBox certificate).stage ==
  .contractionNotStrict
#guard (inspectKrawczyk unsupportedSystem box certificate).stage == .unsupportedAD
#guard (inspectKrawczyk system imageBox imageCert).stage ==
  .imageNotStrictlyInside

/-- error: Krawczyk certificate rejected: the proposed preconditioner is singular.
Checked contraction bound: 1 -/
#guard_msgs in
example : ∃! p, FinBoxMem p box ∧ SystemZero system p := by
  system_unique_root using singularCert

/-- error: Krawczyk certificate dimension mismatch.
Expected: KrawczykCert 4
Found: KrawczykCert 2 -/
#guard_msgs in
example : ∃! p, FinBoxMem p identityBox ∧ SystemZero identitySystem p := by
  system_unique_root using certificate

/- Rejected verification restores the original goal and all assignments. -/
example : ∃! p, FinBoxMem p box ∧ SystemZero system p := by
  first
  | system_unique_root using singularCert
  | exact unique_root

/- Plain semantic routing recognizes the family but does not pretend I1 can
generate a candidate. -/
example : True := by
  fail_if_success
    have : ∃! p, FinBoxMem p identityBox ∧ SystemZero identitySystem p := by
      leancert?
  trivial

end LeanCert.Test.KrawczykTactic
