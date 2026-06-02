/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity

/-!
# Validity Forwarding Export Tests

Smoke tests for stable Validity-layer import paths.
-/

namespace LeanCert.Test.ValidityExports

#check LeanCert.Validity.FinSum.verify_finsum_upper_full
#check LeanCert.Validity.FinSum.verify_witness_sum_upper_list_full
#check LeanCert.Validity.Dyadic.verify_upper_bound_dyadic
#check LeanCert.Validity.Dyadic.verify_upper_bound_dyadic_withInv
#check LeanCert.Validity.Chebyshev.verify_psi_le_mul
#check LeanCert.Validity.Chebyshev.verify_theta_rel_error

end LeanCert.Test.ValidityExports
