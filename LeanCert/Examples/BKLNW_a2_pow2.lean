/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.BKLNW_a2_reflective

/-!
# BKLNW a₂ Definition and 2^N Certificates

This public interface preserves the historical names used by downstream projects,
but the large certificates now re-export the verified reflective proofs instead
of placeholder theorem bodies.
-/

open Real Finset

namespace LeanCert.Examples.BKLNW_a2_pow2

noncomputable abbrev f : ℝ → ℝ := LeanCert.Examples.BKLNW_a2_base.f

theorem floor_log_two_pow (n : ℕ) : ⌊log ((2:ℝ)^n) / log 2⌋₊ = n :=
  LeanCert.Examples.BKLNW_a2_base.floor_log_two_pow n

theorem pow29_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(29:ℕ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow29_upper

theorem pow37_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(37:ℕ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow37_upper

theorem pow44_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(44:ℕ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow44_upper

theorem pow51_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(51:ℕ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow51_upper

theorem pow58_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(58:ℕ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow58_upper

theorem pow63_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(63:ℕ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow63_upper

theorem pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(145:ℕ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow145_upper

theorem pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(217:ℕ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow217_upper

theorem pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(289:ℕ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow289_upper

theorem pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(361:ℕ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow361_upper

theorem pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(433:ℕ)) ≤ (1.00000001938 : ℝ) + (1:ℝ) / 10^9 :=
  LeanCert.Examples.BKLNW_a2_reflective.pow433_upper

end LeanCert.Examples.BKLNW_a2_pow2

namespace LeanCert.CertifiedBounds.BKLNW

/-- The BKLNW auxiliary function exposed through the stable bounds API. -/
noncomputable abbrev f : ℝ → ℝ := LeanCert.Examples.BKLNW_a2_pow2.f

alias floor_log_two_pow := LeanCert.Examples.BKLNW_a2_pow2.floor_log_two_pow
alias pow29_upper := LeanCert.Examples.BKLNW_a2_pow2.pow29_upper
alias pow37_upper := LeanCert.Examples.BKLNW_a2_pow2.pow37_upper
alias pow44_upper := LeanCert.Examples.BKLNW_a2_pow2.pow44_upper
alias pow51_upper := LeanCert.Examples.BKLNW_a2_pow2.pow51_upper
alias pow58_upper := LeanCert.Examples.BKLNW_a2_pow2.pow58_upper
alias pow63_upper := LeanCert.Examples.BKLNW_a2_pow2.pow63_upper
alias pow145_upper := LeanCert.Examples.BKLNW_a2_pow2.pow145_upper
alias pow217_upper := LeanCert.Examples.BKLNW_a2_pow2.pow217_upper
alias pow289_upper := LeanCert.Examples.BKLNW_a2_pow2.pow289_upper
alias pow361_upper := LeanCert.Examples.BKLNW_a2_pow2.pow361_upper
alias pow433_upper := LeanCert.Examples.BKLNW_a2_pow2.pow433_upper

end LeanCert.CertifiedBounds.BKLNW

attribute [deprecated LeanCert.CertifiedBounds.BKLNW.f (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.f
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.floor_log_two_pow (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.floor_log_two_pow
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow29_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow29_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow37_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow37_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow44_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow44_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow51_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow51_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow58_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow58_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow63_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow63_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow145_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow145_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow217_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow217_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow289_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow289_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow361_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow361_upper
attribute [deprecated LeanCert.CertifiedBounds.BKLNW.pow433_upper (since := "2026-07-19")]
  LeanCert.Examples.BKLNW_a2_pow2.pow433_upper
