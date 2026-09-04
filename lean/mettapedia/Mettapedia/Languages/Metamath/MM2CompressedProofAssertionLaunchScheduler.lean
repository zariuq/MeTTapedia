import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSupport
import Mettapedia.Languages.Metamath.MM2CompressedProofDirectAssertionOrder

/-!
# Scheduled compressed assertion launch

This module joins the independently decoded assertion matcher with the four
earlier cursor handlers and proves that the ordinary reflective scheduler
selects the generated direct-assertion transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduler

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSupport
open Mettapedia.Languages.Metamath.MM2CompressedProofDirectAssertionOrder
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectAssertionScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private theorem proofDirective_decodes :
    extractSupportedSourceExecFact compressedProofStepDirective.atom =
      some compressedProofStepDirective := by
  change extractSupportedSourceExecFact compressedProofStepRule = _
  exact extract_compressedProofStepRule_exact

private theorem assertionLaunchDirective_decodes :
    extractSupportedSourceExecFact compressedAssertionLaunchDirective.atom =
      some compressedAssertionLaunchDirective := by
  change extractSupportedSourceExecFact compressedAssertionLaunchRule = _
  exact extract_compressedAssertionLaunchRule_exact

private theorem lookupFaultDirective_decodes :
    extractSupportedSourceExecFact compressedHeapLookupFaultDirective.atom =
      some compressedHeapLookupFaultDirective := by
  change extractSupportedSourceExecFact compressedHeapLookupFaultRule = _
  exact extract_compressedHeapLookupFaultRule_exact

private theorem lookupAdvanceDirective_decodes :
    extractSupportedSourceExecFact compressedHeapLookupAdvanceDirective.atom =
      some compressedHeapLookupAdvanceDirective := by
  change extractSupportedSourceExecFact compressedHeapLookupAdvanceRule = _
  exact extract_compressedHeapLookupAdvanceRule_exact

theorem directAssertionSchedulerFrame_supported :
    cSupportedSourceExecFacts directAssertionSchedulerFrame =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective] := by
  unfold directAssertionSchedulerFrame cSupportedSourceExecFacts
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [proofDirective_decodes, assertionLaunchDirective_decodes,
    lookupFaultDirective_decodes, lookupAdvanceDirective_decodes]

theorem select_direct_assertion_from_canonical_inventory :
    selectNextScheduled
        [speculativeDirectAssertionDirective, compressedProofStepDirective,
         compressedAssertionLaunchDirective, compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective] =
      some speculativeDirectAssertionDirective := by
  have proofDoesNotPreempt := lexLt_asymm _ _
    direct_assertion_preempts_cursor_proof
  have assertionDoesNotPreempt := lexLt_asymm _ _
    direct_assertion_preempts_cursor_assertion
  have faultDoesNotPreempt := lexLt_asymm _ _
    direct_assertion_preempts_cursor_fault
  have advanceDoesNotPreempt := lexLt_asymm _ _
    direct_assertion_preempts_cursor_advance
  unfold selectNextScheduled
  simp only [List.foldl_cons, proofDoesNotPreempt, assertionDoesNotPreempt,
    faultDoesNotPreempt, advanceDoesNotPreempt, Bool.false_eq_true,
    ↓reduceIte, List.foldl_nil]

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduler
