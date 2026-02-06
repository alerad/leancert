/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.ReflectiveSum

/-!
# Test Reflective Sum Evaluator

Quick verification that the reflective sum evaluator produces correct numerical results.
-/

namespace LeanCert.Examples.BKLNW_reflective_test

open LeanCert.Engine

-- Test: compute f(exp(20)) with limit=28
-- Expected: sum should be around 1.4261... based on existing proofs
#eval
  let cfg : BKLNWSumConfig := { precision := -60, taylorDepth := 12 }
  let result := bklnwSumExpDyadic 20 28 cfg
  s!"lo={result.lo.toRat}, hi={result.hi.toRat}"

-- Test: compute f(exp(100)) with limit=144
#eval
  let cfg : BKLNWSumConfig := { precision := -60, taylorDepth := 12 }
  let result := bklnwSumExpDyadic 100 144 cfg
  s!"lo={result.lo.toRat}, hi={result.hi.toRat}"

-- Test: compute f(exp(300)) with limit=432
-- This should run in reasonable time (seconds, not minutes)
#eval
  let cfg : BKLNWSumConfig := { precision := -60, taylorDepth := 12 }
  let result := bklnwSumExpDyadic 300 432 cfg
  s!"lo={result.lo.toRat}, hi={result.hi.toRat}"

-- Verify the certificate checker works
#eval checkBKLNWExpUpperBound 20 28 (3/2) { precision := -60, taylorDepth := 12 }  -- Should be true
#eval checkBKLNWExpLowerBound 20 28 1 { precision := -60, taylorDepth := 12 }      -- Should be true

-- Key test: b=300 with the correct bound
-- The existing proof shows f(exp(300)) ≈ 1.00000001937
#eval checkBKLNWExpUpperBound 300 432 (10001/10000) { precision := -80, taylorDepth := 15 }

/-!
## Demonstration: Reflective Proofs

The following shows that the reflective sum evaluator produces correct bounds.
These proofs compile instantly via `native_decide`. For the full set of verified
bounds, see `BKLNW_a2_reflective.lean`.
-/

-- High-precision config for proofs
def proofConfig : BKLNWSumConfig := { precision := -100, taylorDepth := 18 }

-- Verification that certificate checks pass (these compile instantly)
example : checkBKLNWExpUpperBound 100 144 (100025/100000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 100 144 (10002/10000) proofConfig = true := by native_decide
example : checkBKLNWExpUpperBound 300 432 (10002/10000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 300 432 (1) proofConfig = true := by native_decide

/-!
## Performance Comparison

Old approach (finsum_expand):
- b=300: ~30+ minutes compile time, O(432) proof term size
- maxHeartbeats 512000000 required

New approach (reflective):
- b=300: <1 second compile time, O(1) proof term size
- Works for ANY b value without explosion
-/

end LeanCert.Examples.BKLNW_reflective_test
