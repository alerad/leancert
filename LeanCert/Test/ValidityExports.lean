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
#check LeanCert.Validity.FinSum.verify_witness_sum_upper_cached
#check LeanCert.Validity.FinSum.verify_witness_sum_upper_list_full
#check LeanCert.Validity.Dyadic.verify_upper_bound_dyadic
#check LeanCert.Validity.Dyadic.verify_upper_bound_dyadic_checked
#check LeanCert.Validity.Chebyshev.verify_psi_le_mul
#check LeanCert.Validity.Chebyshev.verify_theta_rel_error
#check LeanCert.Validity.Algebra.verify_separable
#check LeanCert.Validity.Algebra.verify_squarefree
#check LeanCert.Validity.Algebra.verify_coprime_deriv
#check LeanCert.Validity.Algebra.verify_real_roots_simple
#check LeanCert.Validity.Algebra.verify_toExpr_roots_simple
#check LeanCert.Validity.Algebra.verify_cubic_root_count
#check LeanCert.Validity.Algebra.verify_cubic_root_count_subdiv
#check LeanCert.Validity.Algebra.verify_complete_cubic_isolation
#check LeanCert.Validity.Algebra.verify_cubic_root_radius
#check LeanCert.Validity.Algebra.verify_cubic_separation_mesh
#check LeanCert.Validity.Algebra.verify_cubic_distinct_roots_separated
#check LeanCert.Engine.Algebra.cubic_root_gap_gt_of_discr_bound
#check LeanCert.Engine.Algebra.cubic_roots_pairwise_gap_gt_of_discr_bound_and_radius

end LeanCert.Test.ValidityExports
