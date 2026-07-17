import LeanCert.Validity.IntegrationDyadic

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic

namespace LeanCert.Test.IntegrationDyadicChecked

private def unit : IntervalRat := ⟨0, 1, by norm_num⟩
private def left : IntervalRat := ⟨0, 1 / 2, by norm_num⟩
private def right : IntervalRat := ⟨1 / 2, 1, by norm_num⟩
private def gapRight : IntervalRat := ⟨3 / 5, 1, by norm_num⟩
private def overlapRight : IntervalRat := ⟨2 / 5, 1, by norm_num⟩
private def positive : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (⟨1 / 2, 3 / 2, by norm_num⟩ : IntervalRat) (-53)
private def crossesZero : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (⟨-1, 1, by norm_num⟩ : IntervalRat) (-53)
private def logExpr : Expr := .log (.var 0)
private def cfg : DyadicConfig := { precision := -53, taylorDepth := 18 }

example : checkListPartitionCovers [left, right] unit = true := by native_decide
example : checkListPartitionCovers [] unit = false := by native_decide
example : checkListPartitionCovers [left, gapRight] unit = false := by native_decide
example : checkListPartitionCovers [left, overlapRight] unit = false := by native_decide

example : checkIntegralBoundsDyadicList (.var 0) [left, right] 0 1 = true := by
  native_decide

example :
    LeanCert.Internal.Dyadic.evalPreparedCached logExpr (fun _ => positive)
        (LeanCert.Internal.Dyadic.prepareContext cfg) =
      LeanCert.Internal.Dyadic.evalCached logExpr (fun _ => positive) cfg := by
  apply Prod.ext
  · rw [evalIntervalDyadicPreparedCached_fst logExpr (fun _ => positive) cfg,
      evalIntervalDyadicCached_fst logExpr (fun _ => positive) cfg]
  · rw [evalIntervalDyadicPreparedCached_snd logExpr (fun _ => positive) cfg,
      evalIntervalDyadicCached_snd logExpr (fun _ => positive) cfg]

example :
    (LeanCert.Internal.Dyadic.evalPreparedCached logExpr (fun _ => crossesZero)
      (LeanCert.Internal.Dyadic.prepareContext cfg)).2 = false := by
  native_decide

end LeanCert.Test.IntegrationDyadicChecked
