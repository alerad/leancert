/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Schema

/-!
# Minimal benchmark harness

The harness deliberately measures compiled evaluator actions only.  It supports
warmups, repeated raw samples, human summaries, JSONL output, suite selection,
and case-name filtering.  Algorithm counters and proof-pipeline profiling can
be layered on later without changing the sample schema.
-/

namespace LeanCert.Benchmark

structure Case where
  name : String
  family : String
  layer : Layer
  backendRequested : String
  suites : List String
  parameters : List (String × String)
  input : InputMetrics
  innerIterations : Nat := 1
  expectedStatus : String := "success"
  run : IO Outcome

inductive OutputFormat where
  | human
  | jsonl
  deriving DecidableEq

structure Config where
  suite : String := "smoke"
  caseFilter : Option String := none
  samples : Nat := 10
  warmups : Nat := 3
  format : OutputFormat := .human
  listOnly : Bool := false

def usage : String := "LeanCert benchmark harness\n\n\
Usage: lake exe leancert-bench [options]\n\n\
Options:\n\
  --suite smoke|evaluation   Select benchmark suite (default: smoke)\n\
  --case TEXT                Run cases whose names contain TEXT\n\
  --samples N                Timed samples per case (default: 10)\n\
  --warmups N                Untimed warmups per case (default: 3)\n\
  --format human|jsonl       Summary or one JSON object per sample\n\
  --list                     List selected cases without running them\n\
  --help                     Show this help\n"

private def parseNat (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a natural number, got '{value}'"

partial def parseArgs (args : List String) (cfg : Config := {}) : Except String Config :=
  match args with
  | [] => .ok cfg
  | "--suite" :: value :: rest => parseArgs rest { cfg with suite := value }
  | "--case" :: value :: rest => parseArgs rest { cfg with caseFilter := some value }
  | "--samples" :: value :: rest => do
      let n ← parseNat "--samples" value
      parseArgs rest { cfg with samples := n }
  | "--warmups" :: value :: rest => do
      let n ← parseNat "--warmups" value
      parseArgs rest { cfg with warmups := n }
  | "--format" :: "human" :: rest => parseArgs rest { cfg with format := .human }
  | "--format" :: "jsonl" :: rest => parseArgs rest { cfg with format := .jsonl }
  | "--format" :: value :: _ => .error s!"unknown output format '{value}'"
  | "--list" :: rest => parseArgs rest { cfg with listOnly := true }
  | "--help" :: _ => .error usage
  | flag :: _ => .error s!"unknown or incomplete option '{flag}'\n\n{usage}"

private def insertNat (n : Nat) : List Nat → List Nat
  | [] => [n]
  | x :: xs => if n ≤ x then n :: x :: xs else x :: insertNat n xs

private def sortNats (values : List Nat) : List Nat :=
  values.foldl (fun sorted value => insertNat value sorted) []

private def percentile (sorted : List Nat) (percent : Nat) : Nat :=
  match sorted with
  | [] => 0
  | _ => sorted.getD ((((sorted.length - 1) * percent) + 50) / 100) 0

private def median (values : List Nat) : Nat :=
  let sorted := sortNats values
  match sorted.length with
  | 0 => 0
  | n =>
      if n % 2 = 1 then sorted.getD (n / 2) 0
      else (sorted.getD (n / 2 - 1) 0 + sorted.getD (n / 2) 0) / 2

private def medianAbsoluteDeviation (values : List Nat) : Nat :=
  let center := median values
  median (values.map fun value => value.max center - value.min center)

private def pad3 (n : Nat) : String :=
  if n < 10 then s!"00{n}" else if n < 100 then s!"0{n}" else s!"{n}"

private def formatNanos (ns : Nat) : String :=
  if ns ≥ 1000000 then
    s!"{ns / 1000000}.{pad3 ((ns % 1000000) / 1000)} ms"
  else if ns ≥ 1000 then
    s!"{ns / 1000}.{pad3 (ns % 1000)} µs"
  else
    s!"{ns} ns"

private def measure (benchmark : Case) : IO (Nat × Outcome) := do
  let iterations := max 1 benchmark.innerIterations
  let start ← IO.monoNanosNow
  let mut last ← benchmark.run
  for _ in [1:iterations] do
    last ← benchmark.run
  let stop ← IO.monoNanosNow
  return ((stop - start) / iterations, last)

private def selected (cfg : Config) (benchmark : Case) : Bool :=
  benchmark.suites.contains cfg.suite &&
    match cfg.caseFilter with
    | none => true
    | some filter => filter.isEmpty || (benchmark.name.splitOn filter).length > 1

private def runCase (runId : String) (cfg : Config) (benchmark : Case) : IO Bool := do
  for _ in [:cfg.warmups] do
    let _ ← measure benchmark

  let mut samples : List Sample := []
  for sampleIndex in [:cfg.samples] do
    let (timingNs, outcome) ← measure benchmark
    let sample : Sample := {
      runId
      suite := cfg.suite
      caseName := benchmark.name
      family := benchmark.family
      layer := benchmark.layer
      backendRequested := benchmark.backendRequested
      parameters := benchmark.parameters
      input := benchmark.input
      outcome
      timingNs
      innerIterations := max 1 benchmark.innerIterations
      sample := sampleIndex
    }
    samples := sample :: samples
    if cfg.format = .jsonl then
      IO.println sample.asJson.compress

  if cfg.format = .human then
    let ordered := samples.reverse
    let timings := ordered.map (·.timingNs)
    let sorted := sortNats timings
    let lastOutcome := (ordered.getD 0 {
      runId := "", caseName := "", family := "", layer := .internal,
      suite := "",
      backendRequested := "", parameters := [], input := benchmark.input,
      outcome := { status := "not_run" }, timingNs := 0,
      innerIterations := 1, sample := 0 }).outcome
    let width := match lastOutcome.interval with
      | some I => s!", width={I.hi - I.lo}"
      | none => ""
    IO.println s!"{benchmark.name} [{lastOutcome.status}{width}]"
    IO.println s!"  median={formatNanos (median timings)}, \
MAD={formatNanos (medianAbsoluteDeviation timings)}, \
p10={formatNanos (percentile sorted 10)}, p90={formatNanos (percentile sorted 90)}"
  return samples.all fun sample => sample.outcome.status = benchmark.expectedStatus

def runBenchmarks (cfg : Config) (benchmarks : List Case) : IO UInt32 := do
  let chosen := benchmarks.filter (selected cfg)
  if chosen.isEmpty then
    IO.eprintln s!"No benchmark cases matched suite '{cfg.suite}'."
    return 1

  if cfg.listOnly then
    for benchmark in chosen do IO.println benchmark.name
    return 0

  if cfg.samples = 0 then
    IO.eprintln "--samples must be greater than zero"
    return 1

  let runId := s!"run-{← IO.monoNanosNow}"
  if cfg.format = .human then
    IO.println s!"LeanCert benchmarks: suite={cfg.suite}, samples={cfg.samples}, warmups={cfg.warmups}"
    IO.println "Timing is per evaluator call; use JSONL for raw samples."
  let mut allPassed := true
  for benchmark in chosen do
    if !(← runCase runId cfg benchmark) then allPassed := false
  return if allPassed then 0 else 1

end LeanCert.Benchmark
