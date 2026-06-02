/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.TrigReduced
import LeanCert.Engine.TaylorModel.TrigReduced

/-!
# Trig Reduction Refactor Tests

Smoke tests for the shared range-reduction API and compatibility aliases.
-/

namespace LeanCert.Test.TrigReduction

open LeanCert.Core

#check LeanCert.Core.TrigReduction.reduceToMainPeriod
#check LeanCert.Core.IntervalRat.reduceToMainPeriod
#check LeanCert.Engine.TaylorModel.reduceToMainPeriod
#check LeanCert.Core.IntervalRat.sinComputableReduced
#check LeanCert.Engine.TaylorModel.sinIntervalReduced

example {x : ℝ} (hx : x ∈ (⟨0, 10, by norm_num⟩ : IntervalRat)) :
    Real.sin x ∈ LeanCert.Core.IntervalRat.sinComputableReduced ⟨0, 10, by norm_num⟩ 10 := by
  exact LeanCert.Core.IntervalRat.mem_sinComputableReduced hx 10

example {x : ℝ} (hx : x ∈ (⟨0, 10, by norm_num⟩ : IntervalRat)) :
    Real.sin x ∈ LeanCert.Engine.TaylorModel.sinIntervalReduced ⟨0, 10, by norm_num⟩ 10 := by
  exact LeanCert.Engine.TaylorModel.mem_sinIntervalReduced hx 10

end LeanCert.Test.TrigReduction
