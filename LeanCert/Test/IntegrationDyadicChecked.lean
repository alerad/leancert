import LeanCert.Validity.IntegrationDyadic

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic

namespace LeanCert.Test.IntegrationDyadicChecked

private def unit : IntervalRat := ⟨0, 1, by norm_num⟩
private def left : IntervalRat := ⟨0, 1 / 2, by norm_num⟩
private def right : IntervalRat := ⟨1 / 2, 1, by norm_num⟩
private def gapRight : IntervalRat := ⟨3 / 5, 1, by norm_num⟩
private def overlapRight : IntervalRat := ⟨2 / 5, 1, by norm_num⟩

example : checkListPartitionCovers [left, right] unit = true := by native_decide
example : checkListPartitionCovers [] unit = false := by native_decide
example : checkListPartitionCovers [left, gapRight] unit = false := by native_decide
example : checkListPartitionCovers [left, overlapRight] unit = false := by native_decide

example : checkIntegralBoundsDyadicList (.var 0) [left, right] 0 1 = true := by
  native_decide

end LeanCert.Test.IntegrationDyadicChecked
