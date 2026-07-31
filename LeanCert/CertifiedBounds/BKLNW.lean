/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.CertifiedBounds.BKLNWVerified

/-!
# Certified BKLNW bounds

Stable public interface for the BKLNW `a₂` certificate family. The declarations
here directly expose the checked base lemmas and reflective certificates; example
modules are not part of the public API.
-/

namespace LeanCert.CertifiedBounds.BKLNW

noncomputable abbrev f : ℝ → ℝ := LeanCert.Engine.BKLNW.f
noncomputable abbrev bklnwF : ℝ → Nat → ℝ := LeanCert.Engine.BKLNW.bklnwF

alias floor_log_two_pow := LeanCert.Engine.BKLNW.floor_log_two_pow
alias floor_20 := LeanCert.Engine.BKLNW.floor_20
alias floor_25 := LeanCert.Engine.BKLNW.floor_25
alias floor_30 := LeanCert.Engine.BKLNW.floor_30
alias floor_35 := LeanCert.Engine.BKLNW.floor_35
alias floor_40 := LeanCert.Engine.BKLNW.floor_40
alias floor_43 := LeanCert.Engine.BKLNW.floor_43
alias floor_100 := LeanCert.Engine.BKLNW.floor_100
alias floor_150 := LeanCert.Engine.BKLNW.floor_150
alias floor_200 := LeanCert.Engine.BKLNW.floor_200
alias floor_250 := LeanCert.Engine.BKLNW.floor_250
alias floor_300 := LeanCert.Engine.BKLNW.floor_300
alias f_eq_bklnwF_exp := LeanCert.Engine.BKLNW.f_eq_bklnwF_exp

alias pow29_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow29_upper
alias pow37_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow37_upper
alias pow44_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow44_upper
alias pow51_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow51_upper
alias pow58_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow58_upper
alias pow63_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow63_upper
alias pow145_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow145_upper
alias pow217_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow217_upper
alias pow289_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow289_upper
alias pow361_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow361_upper
alias pow433_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow433_upper

alias a2_20_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_20_exp_lower
alias a2_20_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_20_exp_upper
alias a2_25_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_25_exp_lower
alias a2_25_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_25_exp_upper
alias a2_30_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_30_exp_lower
alias a2_30_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_30_exp_upper
alias a2_35_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_35_exp_lower
alias a2_35_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_35_exp_upper
alias a2_40_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_40_exp_lower
alias a2_40_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_40_exp_upper
alias a2_43_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_43_exp_lower
alias a2_43_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_43_exp_upper
alias a2_100_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_100_exp_lower
alias a2_100_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_100_exp_upper
alias a2_150_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_150_exp_lower
alias a2_150_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_150_exp_upper
alias a2_200_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_200_exp_lower
alias a2_200_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_200_exp_upper
alias a2_250_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_250_exp_lower
alias a2_250_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_250_exp_upper
alias a2_300_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_300_exp_lower
alias a2_300_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_300_exp_upper

end LeanCert.CertifiedBounds.BKLNW
