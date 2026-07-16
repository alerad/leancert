/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.FinSumDyadic
import LeanCert.Engine.WitnessSum

/-!
# Finite-Sum Validity Exports

Stable Validity-layer import path for finite-sum and witness-sum bridge theorems.
The theorem definitions remain in the engine modules for compatibility.
-/

namespace LeanCert.Validity.FinSum

export LeanCert.Engine
  ( verify_finsum_upper
    verify_finsum_lower
    verify_finsum_upper_full
    verify_finsum_lower_full
    verify_finsum_upper_checked
    verify_finsum_lower_checked
    verify_finsum_upper_full_checked
    verify_finsum_lower_full_checked
    verify_finsum_upper_list_full
    verify_finsum_lower_list_full
    verify_finsum_upper_list_full_checked
    verify_finsum_lower_list_full_checked
    verify_witness_sum_upper
    verify_witness_sum_lower
    verify_witness_sum_upper_cached
    verify_witness_sum_lower_cached
    verify_witness_sum_upper_list
    verify_witness_sum_lower_list
    verify_witness_sum_upper_list_full
    verify_witness_sum_lower_list_full )

end LeanCert.Validity.FinSum
