/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCert.Engine.Pisano

/-! # Pisano Period Tests

Verify known Pisano periods and fixed points via `native_decide` and `#eval`. -/

open LeanCert.Engine.Pisano

/-! ### Known Fibonacci Pisano periods π(p) -/

-- π(2) = 3, π(3) = 8, π(5) = 20, π(7) = 16, π(11) = 10, π(13) = 28
#eval findPisanoPeriod 1 (-1) 2   -- expect 3
#eval findPisanoPeriod 1 (-1) 3   -- expect 8
#eval findPisanoPeriod 1 (-1) 5   -- expect 20
#eval findPisanoPeriod 1 (-1) 7   -- expect 16
#eval findPisanoPeriod 1 (-1) 11  -- expect 10
#eval findPisanoPeriod 1 (-1) 13  -- expect 28

/-! ### Pell Pisano periods -/

-- Pell: U_n(2, -1)
#eval findPisanoPeriod 2 (-1) 2   -- expect 2
#eval findPisanoPeriod 2 (-1) 3   -- expect 8
#eval findPisanoPeriod 2 (-1) 5   -- expect 12
#eval findPisanoPeriod 2 (-1) 7   -- expect 6

/-! ### Lucas(3, -1) Pisano periods -/

#eval findPisanoPeriod 3 (-1) 2   -- expect 3
#eval findPisanoPeriod 3 (-1) 3   -- expect 2
#eval findPisanoPeriod 3 (-1) 13  -- expect 52

/-! ### Lucas(3, 1) Pisano periods -/

#eval findPisanoPeriod 3 1 2      -- expect 3
#eval findPisanoPeriod 3 1 3      -- expect 4
#eval findPisanoPeriod 3 1 5      -- expect 10

/-! ### Pisano fixed points -/

-- Fibonacci fixed points ≤ 200: should find 24, 120
#eval findPisanoFixedPoints 1 (-1) 200

-- Pell fixed points ≤ 200: should find 2
#eval findPisanoFixedPoints 2 (-1) 200

-- Lucas(3, -1) fixed points ≤ 200: should find 6, 156
#eval findPisanoFixedPoints 3 (-1) 200

-- Lucas(3, 1) fixed points ≤ 200: should find 12, 60
#eval findPisanoFixedPoints 3 1 200

-- Lucas(4, 1) fixed points ≤ 200: should find 2, 6
#eval findPisanoFixedPoints 4 1 200
