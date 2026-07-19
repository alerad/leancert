/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Benchmark.Suites.Evaluation
import LeanCert.Benchmark.Suites.Integration

namespace LeanCert.Benchmark

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
      if message = usage then IO.println message else IO.eprintln message
      return if message = usage then 0 else 1
  | .ok cfg => runBenchmarks cfg (Evaluation.cases ++ Integration.cases)

end LeanCert.Benchmark

def main (args : List String) : IO UInt32 :=
  LeanCert.Benchmark.main args
