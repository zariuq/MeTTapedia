import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectAssertionScheduling

/-!
# Scheduler support for the compressed assertion launch

The canonical assertion slice contains one executable directive and six
dynamic or inert data rows.  Its appended scheduler frame contains the four
earlier cursor handlers.  Their support inventories are proved compositionally
so elaboration never normalizes the large embedded assertion rule as data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSupport

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectAssertionScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private theorem pendingRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.pendingRow = none := by
  apply extractSupportedSourceExecFact_eq_none_of_dynamic
  simp [DirectAssertionContext.pendingRow, isDynamicRow, dynamicRowHeads]

private theorem lookupRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.lookupRow = none := by
  apply extractSupportedSourceExecFact_eq_none_of_dynamic
  simp [DirectAssertionContext.lookupRow, isDynamicRow, dynamicRowHeads]

private theorem heapRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.heapRow = none := by
  apply extractSupportedSourceExecFact_eq_none_of_dynamic
  simp [DirectAssertionContext.heapRow, isDynamicRow, dynamicRowHeads]

private theorem machineRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.machineRow = none := by
  apply extractSupportedSourceExecFact_eq_none_of_dynamic
  simp [DirectAssertionContext.machineRow, isDynamicRow, dynamicRowHeads]

private theorem headerRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.headerRow = none := by
  rfl

private theorem rejoinCaptureRow_no_supported
    (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.rejoinCaptureRow = none := by
  rfl

theorem directAssertionMatchSlice_supported
    (context : DirectAssertionContext) :
    cSupportedSourceExecFacts (directAssertionMatchSlice context) =
      [speculativeDirectAssertionDirective] := by
  have directExact :
      extractSupportedSourceExecFact speculativeDirectAssertionDirective.atom =
        some speculativeDirectAssertionDirective := by
    change extractSupportedSourceExecFact compressedDirectAssertionRule = _
    exact extract_speculativeDirectAssertionDirective_exact
  unfold directAssertionMatchSlice cSupportedSourceExecFacts
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [directExact,
    pendingRow_no_supported, lookupRow_no_supported, heapRow_no_supported,
    machineRow_no_supported, headerRow_no_supported,
    rejoinCaptureRow_no_supported]

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSupport
