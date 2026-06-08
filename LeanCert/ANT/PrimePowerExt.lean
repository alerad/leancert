/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Prime-power extensionality helpers

Mathlib already proves the main theorem: two multiplicative arithmetic functions
are equal iff they agree on all prime powers.  This module gives LeanCert a
small, stable ANT-facing wrapper with names intended for certificate/tactic
workflows.
-/

namespace LeanCert.ANT.PrimePowerExt

open ArithmeticFunction

/--
Two multiplicative arithmetic functions are equal when they agree on every prime
power.

This is a LeanCert-facing wrapper around
`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`.
-/
theorem ext_prime_powers {R : Type*} [CommMonoidWithZero R]
    (f g : ArithmeticFunction R)
    (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative)
    (h : ∀ p i : Nat, Nat.Prime p → f (p ^ i) = g (p ^ i)) :
    f = g :=
  (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg).2 h

/--
Iff form of prime-power extensionality, exposed under LeanCert's ANT namespace.
-/
theorem eq_iff_eq_on_prime_powers {R : Type*} [CommMonoidWithZero R]
    (f g : ArithmeticFunction R)
    (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p i : Nat, Nat.Prime p → f (p ^ i) = g (p ^ i) :=
  ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg

/--
Certificate object for arithmetic-function equality by local prime-power
checks.

This packages the common ANT workflow: prove both sides multiplicative, then
verify equality on every `p^k`.
-/
structure LocalPrimePowerCert {R : Type*} [CommMonoidWithZero R]
    (f g : ArithmeticFunction R) where
  left_multiplicative : f.IsMultiplicative
  right_multiplicative : g.IsMultiplicative
  local_eq : ∀ p k : Nat, Nat.Prime p → f (p ^ k) = g (p ^ k)

namespace LocalPrimePowerCert

/-- Soundness theorem for a local prime-power equality certificate. -/
theorem sound {R : Type*} [CommMonoidWithZero R] {f g : ArithmeticFunction R}
    (cert : LocalPrimePowerCert f g) :
    f = g :=
  ext_prime_powers f g cert.left_multiplicative cert.right_multiplicative cert.local_eq

end LocalPrimePowerCert

end LeanCert.ANT.PrimePowerExt
