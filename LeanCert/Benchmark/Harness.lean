/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Schema

/-!
# Benchmark harness

The harness measures compiled evaluator and checked algorithm actions. It
supports warmups, repeated raw samples, human summaries, JSONL output, suite
selection, and case-name filtering. Algorithm counters and proof-pipeline
profiling can be layered on later without changing the sample schema.
-/

namespace LeanCert.Benchmark

structure Case where
  name : String
  family : String
  tier : String := "micro"
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
  | markdown
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
  --suite smoke|evaluation|ad|heavy|scaling|full|end-to-end|all\n\
                              Select benchmark suite (default: smoke)\n\
  --case TEXT                Run cases whose names contain TEXT\n\
  --samples N                Timed samples per case (default: 10)\n\
  --warmups N                Untimed warmups per case (default: 3)\n\
  --format human|jsonl|markdown\n\
                              Console summary, raw samples, or Markdown table\n\
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
  | "--format" :: "markdown" :: rest => parseArgs rest { cfg with format := .markdown }
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

private def markdownCell (value : String) : String :=
  value.replace "|" "\\|" |>.replace "\n" " "

private def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

private def formatWidth (width : ℚ) : String :=
  let exact := s!"{width}"
  if exact.length ≤ 32 then exact
  else
    let numeratorBits := bitLength width.num.natAbs
    let denominatorBits := bitLength width.den
    let scale := (numeratorBits : Int) - (denominatorBits : Int)
    s!"≈2^{scale} ({numeratorBits}-bit/{denominatorBits}-bit)"

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
      tier := benchmark.tier
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
      runId := "", caseName := "", family := "", tier := "", layer := .internal,
      suite := "",
      backendRequested := "", parameters := [], input := benchmark.input,
      outcome := { status := "not_run" }, timingNs := 0,
      innerIterations := 1, sample := 0 }).outcome
    let width := match lastOutcome.interval with
      | some I => s!", width={formatWidth (I.hi - I.lo)}"
      | none => ""
    IO.println s!"{benchmark.name} [{lastOutcome.status}{width}]"
    IO.println s!"  median={formatNanos (median timings)}, \
MAD={formatNanos (medianAbsoluteDeviation timings)}, \
p10={formatNanos (percentile sorted 10)}, p90={formatNanos (percentile sorted 90)}"
  else if cfg.format = .markdown then
    let ordered := samples.reverse
    let timings := ordered.map (·.timingNs)
    let sorted := sortNats timings
    let lastOutcome := (ordered.getD 0 {
      runId := "", caseName := "", family := "", tier := "", layer := .internal,
      suite := "",
      backendRequested := "", parameters := [], input := benchmark.input,
      outcome := { status := "not_run" }, timingNs := 0,
      innerIterations := 1, sample := 0 }).outcome
    let backendUsed := lastOutcome.backendUsed.getD "—"
    let width := match lastOutcome.interval with
      | some I => formatWidth (I.hi - I.lo)
      | none => "—"
    IO.println s!"| {markdownCell benchmark.name} | {markdownCell benchmark.tier} | {benchmark.layer.name} | \
{markdownCell benchmark.backendRequested} | {markdownCell backendUsed} | \
{benchmark.input.astNodes} | {benchmark.input.astDepth} | \
{markdownCell lastOutcome.status} | {markdownCell width} | \
{formatNanos (median timings)} | {formatNanos (medianAbsoluteDeviation timings)} | \
{formatNanos (percentile sorted 10)} | {formatNanos (percentile sorted 90)} |"
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
    IO.println "Timing is per benchmark action; use JSONL for raw samples."
  else if cfg.format = .markdown then
    IO.println "# LeanCert benchmark results"
    IO.println ""
    IO.println s!"- Suite: {markdownCell cfg.suite}"
    IO.println s!"- Timed samples per case: {cfg.samples}"
    IO.println s!"- Untimed warmups per case: {cfg.warmups}"
    IO.println "- Timing unit: per benchmark action"
    IO.println ""
    IO.println "| Case | Tier | Layer | Requested backend | Used backend | Nodes | Depth | Status | Width | Median | MAD | p10 | p90 |"
    IO.println "| --- | --- | --- | --- | --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |"
  let mut allPassed := true
  for benchmark in chosen do
    if !(← runCase runId cfg benchmark) then allPassed := false
  return if allPassed then 0 else 1

end LeanCert.Benchmark
