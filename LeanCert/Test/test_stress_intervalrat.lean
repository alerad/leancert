module

public import LeanCert.Core.IntervalRat.Taylor

public section

open LeanCert.Core

-- Raw interval computations (debug-style).
#eval
  let I := IntervalRat.expPointComputable (1 / 2) 15
  dbg_trace "exp(1/2): [{I.lo}, {I.hi}]"
  pure ()

#eval
  let I := IntervalRat.sinhPointComputable (1 / 2) 15
  dbg_trace "sinh(1/2): [{I.lo}, {I.hi}]"
  pure ()

#eval
  let I := IntervalRat.atanhPointComputable (1 / 3) 15
  dbg_trace "atanh(1/3): [{I.lo}, {I.hi}]"
  pure ()
