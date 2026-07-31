/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.Krawczyk
import LeanCert.Tactic

/-! Generalized I1/I2 regressions for manual and automatic Krawczyk front ends. -/

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

/- I2 constructs midpoint-Jacobian candidates and replays them through the
same checked theorem boundary as the manual tactic. -/
example : ∃! p, FinBoxMem p translatedBox ∧ SystemZero translatedSystem p := by
  system_unique_root (trust := kernel)

example : ∃! p, FinBoxMem p mixedBox ∧ SystemZero mixedSystem p := by
  system_unique_root (trust := native)

example : ∃! p, FinBoxMem p cyclicBox ∧ SystemZero cyclicSystem p := by
  system_unique_root (trust := auto)

example : ∃! p, FinBoxMem p identityBox ∧ SystemZero identitySystem p := by
  system_unique_root

example : ∃! p, FinBoxMem p expBox ∧ SystemZero expSystem p := by
  system_unique_root? (trust := kernel)

#guard (generateAutomaticKrawczyk translatedSystem translatedBox).succeeded
#guard (generateAutomaticKrawczyk mixedSystem mixedBox).succeeded
#guard (generateAutomaticKrawczyk cyclicSystem cyclicBox).succeeded
#guard (generateAutomaticKrawczyk identitySystem identityBox).succeeded

/- An asymmetric exponential box makes the midpoint candidate fail while one
bounded interval-Newton refinement produces a valid certificate. -/
def shiftedExpSystem : Fin 1 → Expr :=
  ![Expr.add (Expr.exp (Expr.var 0)) (Expr.const (-1 / 8))]

def shiftedExpBox : Fin 1 → IntervalRat :=
  ![⟨-57 / 20, -33 / 20, by norm_num⟩]

def shiftedExpReport : AutomaticKrawczykReport :=
  generateAutomaticKrawczyk shiftedExpSystem shiftedExpBox

#guard shiftedExpReport.succeeded
#guard shiftedExpReport.attempts == 2
#guard shiftedExpReport.refinements == 1

example : ∃! p, FinBoxMem p shiftedExpBox ∧ SystemZero shiftedExpSystem p := by
  system_unique_root (maxIterations := 4) (trust := kernel)

/- Exact pivoting is independent of the nonlinear search. -/
#guard invertRatMatrix? (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ) ==
  some !![2 / 3, -1 / 3; -1 / 3, 2 / 3]
#guard invertRatMatrix? (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ) == none

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

/- The semantic front door uses the automatic generator and retains its
search statistics for `leancert?`. -/
example : ∃! p, FinBoxMem p box ∧ SystemZero system p := by
  leancert

example : ∃! p, FinBoxMem p identityBox ∧ SystemZero identitySystem p := by
  leancert? (trust := kernel)

def dimensionFiveSystem : Fin 5 → Expr := fun i => Expr.var i
def dimensionFiveBox : Fin 5 → IntervalRat := fun _ => ⟨-1 / 10, 1 / 10, by norm_num⟩

#guard (generateAutomaticKrawczyk dimensionFiveSystem dimensionFiveBox).failure ==
  some (.dimensionLimit 5 4)
#guard (generateAutomaticKrawczyk unsupportedSystem box).failure == some .unsupportedAD
#guard (generateAutomaticKrawczyk system box
  (search := { maxIterations := 0 })).failure == some (.exhausted 0)

def noRootSystem : Fin 1 → Expr :=
  ![Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 1)]

def symmetricUnitBox : Fin 1 → IntervalRat :=
  ![⟨-1, 1, by norm_num⟩]

#guard (generateAutomaticKrawczyk noRootSystem symmetricUnitBox).failure ==
  some (.singularPointJacobian 1)
#guard (generateAutomaticKrawczyk system wideBox).failure.isSome

/-- error: Automatic Krawczyk candidate generation failed: candidate search exhausted its configured budget after 0 attempt(s).
Last center: []
Last checked contraction bound: 0 -/
#guard_msgs in
example : ∃! p, FinBoxMem p box ∧ SystemZero system p := by
  system_unique_root (maxIterations := 0)

/- Automatic failure is transactional too. -/
example : ∃! p, FinBoxMem p box ∧ SystemZero system p := by
  first
  | system_unique_root (maxIterations := 0)
  | exact unique_root

end LeanCert.Test.KrawczykTactic
