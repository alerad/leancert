/-
Quick test: Dyadic integration on g_alt_expr (the Li2 integrand).
Compare computation time vs rational backend.
-/
import LeanCert.Validity.IntegrationDyadic
import LeanCert.Validity.Integration

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.Integration

-- g_alt_expr = log(1-t²) / (log(1+t) · log(1-t))
def g_alt_expr : Expr :=
  Expr.mul
    (Expr.log (Expr.add (Expr.const 1)
      (Expr.neg (Expr.mul (Expr.var 0) (Expr.var 0)))))
    (Expr.inv
      (Expr.mul
        (Expr.log (Expr.add (Expr.const 1) (Expr.var 0)))
        (Expr.log (Expr.add (Expr.const 1) (Expr.neg (Expr.var 0))))))

def testInterval : IntervalRat := ⟨1/1000, 999/1000, by norm_num⟩

-- Test: Dyadic integration with small partition count
set_option profiler true in
#eval do
  let result := integratePartitionDyadic g_alt_expr testInterval 100 (by norm_num)
  IO.println s!"Dyadic (100 parts): [{result.lo}, {result.hi}]"
  IO.println s!"  width: {result.hi - result.lo}"

-- Test: Rational integration with small partition count (for comparison)
set_option profiler true in
#eval do
  match integratePartitionWithInv g_alt_expr testInterval 100 with
  | some result => IO.println s!"Rational (100 parts): [{result.lo}, {result.hi}]"
  | none => IO.println "Rational: failed"

-- Test: Dyadic with 3000 partitions (the Li2 count)
set_option profiler true in
#eval do
  let result := integratePartitionDyadic g_alt_expr testInterval 3000 (by norm_num)
  IO.println s!"Dyadic (3000 parts): [{result.lo}, {result.hi}]"
  IO.println s!"  width: {result.hi - result.lo}"

-- Test: The actual checker with default precision (-53)
set_option profiler true in
#eval checkIntegralLowerBoundDyadic g_alt_expr testInterval 3000 (103775/100000)

-- Test: Higher precision configs
def highPrec : DyadicConfig := { precision := -100, taylorDepth := 15 }
def veryHighPrec : DyadicConfig := { precision := -200, taylorDepth := 20 }

set_option profiler true in
#eval checkIntegralLowerBoundDyadic g_alt_expr testInterval 3000 (103775/100000) highPrec

set_option profiler true in
#eval checkIntegralLowerBoundDyadic g_alt_expr testInterval 3000 (103775/100000) veryHighPrec

set_option profiler true in
#eval checkIntegralUpperBoundDyadic g_alt_expr testInterval 3000 (104840/100000) veryHighPrec

-- Find optimal: precision -150, depth 15, 3000 parts
def medPrec : DyadicConfig := { precision := -150, taylorDepth := 15 }

set_option profiler true in
#eval checkIntegralLowerBoundDyadic g_alt_expr testInterval 3000 (103775/100000) medPrec
