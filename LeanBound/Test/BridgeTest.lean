/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Bridge

/-!
# Lean-Side Unit Tests for Bridge (Tests 32-33)

Goal: Unit test the JSON deserializers in Lean directly.
These tests verify that the Bridge.lean serialization logic works correctly.
-/

namespace LeanBound.Test.BridgeTest

open Lean LeanBound.Bridge LeanBound.Core

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

end LeanBound.Test.BridgeTest
