/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean.Data.Json
import LeanCert.Core.Expr
import LeanCert.Core.IntervalRat.Basic

/-!
# Benchmark result schema

Small, dependency-free data structures for LeanCert benchmark samples.  Exact
rational endpoints are retained as strings; compact structural and bit-size
metrics make the JSONL output useful without reparsing them.
-/

namespace LeanCert.Benchmark

open Lean
open LeanCert.Core

inductive Layer where
  | internal
  | checkedAPI
  deriving Repr, DecidableEq

def Layer.name : Layer → String
  | .internal => "internal"
  | .checkedAPI => "checked_api"

structure InputMetrics where
  astNodes : Nat
  astDepth : Nat
  variableCount : Nat
  deriving Repr

structure Outcome where
  status : String
  interval : Option IntervalRat := none
  backendUsed : Option String := none
  error : Option String := none
  deriving Repr

structure Sample where
  runId : String
  suite : String
  caseName : String
  family : String
  layer : Layer
  backendRequested : String
  parameters : List (String × String)
  input : InputMetrics
  outcome : Outcome
  timingNs : Nat
  innerIterations : Nat
  sample : Nat
  deriving Repr

private def natBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

private def intBitLength (n : Int) : Nat :=
  natBitLength n.natAbs

private def ratJson (q : ℚ) : Json := Json.mkObj [
  ("exact", toJson s!"{q}"),
  ("numerator_bits", toJson (intBitLength q.num)),
  ("denominator_bits", toJson (natBitLength q.den))
]

private def intervalJson (I : IntervalRat) : Json :=
  let width := I.hi - I.lo
  Json.mkObj [
    ("lo", ratJson I.lo),
    ("hi", ratJson I.hi),
    ("width", ratJson width)
  ]

private def optionJson (f : α → Json) : Option α → Json
  | none => Json.null
  | some value => f value

def Sample.asJson (result : Sample) : Json := Json.mkObj [
  ("schema", toJson (1 : Nat)),
  ("run_id", toJson result.runId),
  ("suite", toJson result.suite),
  ("case", toJson result.caseName),
  ("family", toJson result.family),
  ("layer", toJson result.layer.name),
  ("backend_requested", toJson result.backendRequested),
  ("backend_used", optionJson toJson result.outcome.backendUsed),
  ("parameters", Json.mkObj (result.parameters.map fun (key, value) => (key, toJson value))),
  ("input", Json.mkObj [
    ("ast_nodes", toJson result.input.astNodes),
    ("ast_depth", toJson result.input.astDepth),
    ("variables", toJson result.input.variableCount)
  ]),
  ("outcome", Json.mkObj [
    ("status", toJson result.outcome.status),
    ("interval", optionJson intervalJson result.outcome.interval),
    ("error", optionJson toJson result.outcome.error)
  ]),
  ("timing_ns", toJson result.timingNs),
  ("inner_iterations", toJson result.innerIterations),
  ("sample", toJson result.sample)
]

end LeanCert.Benchmark
