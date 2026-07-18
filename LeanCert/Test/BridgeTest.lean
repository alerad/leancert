/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Bridge

/-!
# Lean-Side Unit Tests for Bridge (Tests 32-33)

Goal: Unit test the JSON deserializers in Lean directly.
These tests verify that the Bridge.lean serialization logic works correctly.
-/

namespace LeanCert.Test.BridgeTest

open Lean LeanCert.Bridge LeanCert.Core

/-! ## Test 32: Expression Deserialization

We test that rawExprFromJson correctly parses various JSON structures
into the expected Expr values.
-/

/-- Helper to check if parsing succeeded -/
def parseSucceeds (json : Json) : Bool :=
  match rawExprFromJson json with
  | Except.ok _ => true
  | Except.error _ => false

/-- Helper to check if parsing failed -/
def parseFails (json : Json) : Bool :=
  match rawExprFromJson json with
  | Except.ok _ => false
  | Except.error _ => true

-- Test 32a: Const parsing succeeds
#guard parseSucceeds (Json.mkObj [("kind", "const"), ("val", Json.mkObj [("n", 5), ("d", 1)])])

-- Test 32b: Var parsing succeeds
#guard parseSucceeds (Json.mkObj [("kind", "var"), ("idx", 0)])

-- Test 32c: Add parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "add"),
  ("e1", Json.mkObj [("kind", "var"), ("idx", 0)]),
  ("e2", Json.mkObj [("kind", "const"), ("val", Json.mkObj [("n", 1), ("d", 1)])])
])

-- Test 32d: Mul parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "mul"),
  ("e1", Json.mkObj [("kind", "var"), ("idx", 0)]),
  ("e2", Json.mkObj [("kind", "var"), ("idx", 1)])
])

-- Test 32e: Sin parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "sin"),
  ("e", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32f: Cos parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "cos"),
  ("e", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32g: Exp parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "exp"),
  ("e", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32h: Log parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "log"),
  ("e", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32i: Neg parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "neg"),
  ("e", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32j: Div parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "div"),
  ("e1", Json.mkObj [("kind", "var"), ("idx", 0)]),
  ("e2", Json.mkObj [("kind", "const"), ("val", Json.mkObj [("n", 2), ("d", 1)])])
])

-- Test 32k: Sub parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "sub"),
  ("e1", Json.mkObj [("kind", "var"), ("idx", 0)]),
  ("e2", Json.mkObj [("kind", "const"), ("val", Json.mkObj [("n", 1), ("d", 1)])])
])

-- Test 32l: Pow parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "pow"),
  ("base", Json.mkObj [("kind", "var"), ("idx", 0)]),
  ("exp", 2)
])

-- Test 32m: Sqrt parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "sqrt"),
  ("e", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32n: Nested expression parsing succeeds
#guard parseSucceeds (Json.mkObj [
  ("kind", "mul"),
  ("e1", Json.mkObj [
    ("kind", "add"),
    ("e1", Json.mkObj [("kind", "var"), ("idx", 0)]),
    ("e2", Json.mkObj [("kind", "const"), ("val", Json.mkObj [("n", 1), ("d", 1)])])
  ]),
  ("e2", Json.mkObj [("kind", "var"), ("idx", 0)])
])

-- Test 32o: Unknown kind fails
#guard parseFails (Json.mkObj [("kind", "unknown_kind")])

-- Test 32p: Missing kind fails
#guard parseFails (Json.mkObj [("val", 5)])

/-! ## Test 33: Rational Serialization -/

-- Test 33a: RawRat to Rat conversion for positive numbers
#guard (
  let raw : RawRat := { n := 3, d := 4 }
  let q := raw.toRat
  q.num = 3 ∧ q.den = 4
)

-- Test 33b: RawRat to Rat conversion for negative numbers
#guard (
  let raw : RawRat := { n := -5, d := 7 }
  let q := raw.toRat
  q.num = -5 ∧ q.den = 7
)

-- Test 33c: RawRat to Rat conversion for zero
#guard (
  let raw : RawRat := { n := 0, d := 1 }
  let q := raw.toRat
  q.num = 0 ∧ q.den = 1
)

-- Test 33d: toRawRat for positive rationals
#guard (
  let q : ℚ := 3 / 4
  let raw := toRawRat q
  raw.n = 3 ∧ raw.d = 4
)

-- Test 33e: toRawRat for negative rationals
#guard (
  let q : ℚ := -5 / 7
  let raw := toRawRat q
  raw.n = -5 ∧ raw.d = 7
)

-- Test 33f: RawRat JSON serialization
#guard (
  let raw : RawRat := { n := 7, d := 11 }
  let json := toJson raw
  match json.getObjValAs? Int "n", json.getObjValAs? Nat "d" with
  | Except.ok n, Except.ok d => n = 7 ∧ d = 11
  | _, _ => false
)

-- Test 33g: RawInterval JSON serialization
#guard (
  let interval : RawInterval := {
    lo := { n := 1, d := 3 },
    hi := { n := 2, d := 3 }
  }
  let json := toJson interval
  match json.getObjVal? "lo", json.getObjVal? "hi" with
  | Except.ok lo, Except.ok hi =>
    match lo.getObjValAs? Int "n", hi.getObjValAs? Int "n" with
    | Except.ok loN, Except.ok hiN => loN = 1 ∧ hiN = 2
    | _, _ => false
  | _, _ => false
)

-- Test 33h: Zero denominator handling (returns 0)
#guard (
  let raw : RawRat := { n := 5, d := 0 }
  raw.toRat = 0
)

/-! ## Checked evaluator boundary regressions -/

def zeroOneRaw : RawInterval := {
  lo := { n := 0, d := 1 }, hi := { n := 1, d := 1 }
}

def halfRaw : RawInterval := {
  lo := { n := 1, d := 2 }, hi := { n := 1, d := 2 }
}

def jsonStatusIs (expected : String) (j : Json) : Bool :=
  match j.getObjValAs? String "status" with
  | .ok actual => actual = expected
  | .error _ => false

def jsonBackendIs (expected : String) (j : Json) : Bool :=
  match j.getObjValAs? String "backend" with
  | .ok actual => actual = expected
  | .error _ => false

def jsonNatFieldIs (field : String) (expected : Nat) (j : Json) : Bool :=
  match j.getObjValAs? Nat field with
  | .ok actual => actual = expected
  | .error _ => false

-- A reciprocal singularity is an error, never a finite pseudo-interval.
#guard jsonStatusIs "domain_error" (handleEvalInterval {
  expr := Expr.inv (Expr.var 0), box := #[zeroOneRaw]
})

-- The same trust boundary applies to the optimized backends.
#guard jsonStatusIs "domain_error" (handleEvalInterval {
  expr := Expr.log (Expr.var 0), box := #[zeroOneRaw], backend := .dyadic
})

#guard jsonStatusIs "domain_error" (handleEvalInterval {
  expr := Expr.atanh (Expr.var 0), box := #[zeroOneRaw], backend := .affine
})

-- Implemented inverse hyperbolics produce certified, non-placeholder output.
#guard jsonStatusIs "certified" (handleEvalInterval {
  expr := Expr.arsinh (Expr.var 0), box := #[halfRaw], backend := .affine
})

#guard jsonStatusIs "certified" (handleEvalInterval {
  expr := Expr.atanh (Expr.var 0), box := #[halfRaw]
})

-- The generic endpoint selects Rational for inexpensive polynomial input.
#guard jsonBackendIs "rational" (handleEvalInterval {
  expr := Expr.add (Expr.var 0) (Expr.const 1), box := #[halfRaw]
})

-- Explicit choices are honored and never silently changed.
#guard jsonBackendIs "rational" (handleEvalInterval {
  expr := Expr.add (Expr.var 0) (Expr.const 1), box := #[halfRaw],
  backend := .rational
})

-- Certified Dyadic outward rounding requires a nonpositive precision.
#guard jsonStatusIs "invalid_configuration" (handleEvalInterval {
  expr := Expr.var 0, box := #[halfRaw], backend := .dyadic, precision := 1
})

-- Operations without a certified Dyadic implementation reject an explicit
-- request; auto uses the certified Rational implementation.
#guard jsonStatusIs "unsupported_backend" (handleIntegrate {
  expr := Expr.var 0, interval := zeroOneRaw, backend := .dyadic
})

#guard jsonBackendIs "rational" (handleIntegrate {
  expr := Expr.var 0, interval := zeroOneRaw
})

-- Optimization shares the selector: auto is Dyadic. Checked monotonicity
-- pruning fixes x to its low endpoint, so the one-dimensional queue finishes
-- in one iteration instead of being split.
#guard jsonBackendIs "dyadic" (handleGlobalMin {
  expr := Expr.var 0, box := #[zeroOneRaw], maxIters := 1
})

#guard jsonStatusIs "certified" (handleGlobalMin {
  expr := Expr.var 0, box := #[zeroOneRaw], maxIters := 1,
  useMonotonicity := true
})

#guard jsonNatFieldIs "iterations" 1 (handleGlobalMin {
  expr := Expr.var 0, box := #[zeroOneRaw], maxIters := 1,
  useMonotonicity := true
})

#guard jsonStatusIs "certified" (handleGlobalMin {
  expr := Expr.var 0, box := #[zeroOneRaw], backend := .rational, maxIters := 1,
  useMonotonicity := true
})

#guard jsonStatusIs "certified" (handleGlobalMax {
  expr := Expr.var 0, box := #[zeroOneRaw], backend := .affine, maxIters := 1,
  useMonotonicity := true
})

-- Expressions outside the differentiable AD subset still optimize safely;
-- the optional monotonicity pre-pass is a checked no-op for them.
#guard jsonStatusIs "certified" (handleGlobalMin {
  expr := Expr.sqrt (Expr.var 0), box := #[zeroOneRaw], maxIters := 1,
  useMonotonicity := true
})

-- Rational-only tuning is rejected when the checked implementation has a
-- fixed verified depth, instead of being silently ignored.
#guard jsonStatusIs "invalid_configuration" (handleEvalInterval {
  expr := Expr.var 0, box := #[zeroOneRaw], backend := .rational,
  taylorDepth := 11
})

#guard jsonStatusIs "invalid_configuration" (handleIntegrate {
  expr := Expr.var 0, interval := zeroOneRaw, taylorDepth := 11
})

-- Unique-root responses follow the unified status/backend contract.
#guard jsonBackendIs "rational" (handleFindUniqueRoot {
  expr := Expr.var 0, interval := zeroOneRaw
})

#guard jsonStatusIs "unsupported_feature" (handleFindUniqueRoot {
  expr := Expr.var 1, interval := zeroOneRaw
})

-- Subdivision must improve the global lower bound rather than retaining the
-- historical root enclosure forever. One split changes x-x from [-2,2] to a
-- strictly tighter lower bound for every backend.
open LeanCert.Engine LeanCert.Engine.Optimization

def dependencyExpr : LeanCert.Core.Expr :=
  LeanCert.Core.Expr.add (LeanCert.Core.Expr.var 0)
    (LeanCert.Core.Expr.neg (LeanCert.Core.Expr.var 0))
def dependencyBox : Box := [RawInterval.toInterval {
  lo := { n := -1, d := 1 }, hi := { n := 1, d := 1 } }]

def dependencyTightens (backend : BackendChoice) : Bool :=
  match globalMinimizeWith {
      backend := backend, maxIterations := 1, tolerance := 0 } dependencyExpr dependencyBox with
  | .ok outcome => outcome.result.bound.lo > (-2 : ℚ)
  | .error _ => false

#guard dependencyTightens .rational
#guard dependencyTightens .dyadic
#guard dependencyTightens .affine

-- Domain failures propagate through each concrete optimization backend.
def singularOptimizationFails (backend : BackendChoice) : Bool :=
  match globalMinimizeWith {
      backend := backend, maxIterations := 1 }
      (LeanCert.Core.Expr.inv (LeanCert.Core.Expr.var 0)) dependencyBox with
  | .error _ => true
  | .ok _ => false

#guard singularOptimizationFails .rational
#guard singularOptimizationFails .dyadic
#guard singularOptimizationFails .affine

end LeanCert.Test.BridgeTest
