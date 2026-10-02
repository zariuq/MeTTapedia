import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofDirectAssertionOrder
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofScheduling
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAssertionCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertScheduling

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAssertionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

theorem lookup_step_of_selected (space : List Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (directive : SourceExecFact)
    (selected : selectNextScheduled (cSupportedSourceExecFacts space) =
      some directive) :
    cReflectiveSourceWorkQueueStep .leaveInert space =
      some (cFireReflectiveSourceExecFact space directive) := by
  simp only [cReflectiveSourceWorkQueueStep, selected]

private theorem lookup_advance_scheduler_prefix :
    ∃ rest,
      SchedulerKey.key compressedHeapLookupAdvanceDirective =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes "09" ++
          compactSymbolBytes "mm-compressed-heap-lookup-advance" ++ rest := by
  change ∃ rest,
    totalMorkCompactKey compressedHeapLookupAdvanceDirective.atom =
      [4, 196, 101, 120, 101, 99, 2] ++
        compactSymbolBytes "09" ++
        compactSymbolBytes "mm-compressed-heap-lookup-advance" ++ rest
  obtain ⟨input, output, surface⟩ :
      ExecSurfaceAt compressedHeapLookupAdvanceDirective.atom
        compressedHeapLookupAdvanceDirective.loc := by
    exact ⟨_, _, rfl⟩
  exact totalMorkCompactExec_location_prefix
    "09" "mm-compressed-heap-lookup-advance" input output surface (by rfl)
    (by decide) (by decide) (by decide) (by decide)
    (morkCompactRepresentable_of_isSome (by decide +kernel))

theorem lookup_assertion_preempts_advance :
    lexLt (SchedulerKey.key compressedAssertionLaunchDirective)
        (SchedulerKey.key compressedHeapLookupAdvanceDirective) = true := by
  obtain ⟨assertionRest, assertionPrefix⟩ := cursor_assertion_scheduler_prefix
  obtain ⟨advanceRest, advancePrefix⟩ := lookup_advance_scheduler_prefix
  rw [assertionPrefix, advancePrefix]
  rfl

theorem lookup_select_hit_initial_proof :
    selectNextScheduled
        [compressedProofStepDirective, compressedHeapLookupAdvanceDirective,
         compressedAssertionLaunchDirective, compressedHeapLookupFaultDirective] =
      some compressedProofStepDirective := by
  unfold selectNextScheduled
  simp only [List.foldl_cons,
    lexLt_asymm _ _ cursor_proof_preempts_cursor_advance,
    lexLt_asymm _ _ cursor_proof_preempts_cursor_assertion,
    lexLt_asymm _ _ cursor_proof_preempts_cursor_fault,
    Bool.false_eq_true, ↓reduceIte, List.foldl_nil]

theorem lookup_select_fault_initial_proof :
    selectNextScheduled
        [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
         compressedProofStepDirective, compressedAssertionLaunchDirective] =
      some compressedProofStepDirective := by
  unfold selectNextScheduled
  simp only [List.foldl_cons, cursor_fault_preempts_cursor_advance,
    cursor_proof_preempts_cursor_fault,
    lexLt_asymm _ _ cursor_proof_preempts_cursor_assertion,
    Bool.false_eq_true, ↓reduceIte, List.foldl_nil]

theorem lookup_select_hit_fault_probe :
    selectNextScheduled
        [compressedHeapLookupAdvanceDirective, compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective] =
      some compressedHeapLookupFaultDirective := by
  unfold selectNextScheduled
  simp only [List.foldl_cons, lookup_assertion_preempts_advance,
    cursor_fault_preempts_cursor_assertion, ↓reduceIte, List.foldl_nil]

theorem lookup_select_fault_probe :
    selectNextScheduled
        [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
         compressedAssertionLaunchDirective] =
      some compressedHeapLookupFaultDirective := by
  unfold selectNextScheduled
  simp only [List.foldl_cons, cursor_fault_preempts_cursor_advance,
    lexLt_asymm _ _ cursor_fault_preempts_cursor_assertion,
    Bool.false_eq_true, ↓reduceIte, List.foldl_nil]

theorem lookup_select_assertion_probe :
    selectNextScheduled
        [compressedHeapLookupAdvanceDirective, compressedAssertionLaunchDirective] =
      some compressedAssertionLaunchDirective := by
  unfold selectNextScheduled
  simp only [List.foldl_cons, lookup_assertion_preempts_advance,
    ↓reduceIte, List.foldl_nil]

/-- At cursor zero the proof handler is tried but cannot resolve target one. -/
theorem lookup_hit_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitAfterTerminal =
      some lookupHitAfterProofProbe := by
  exact lookup_step_of_selected lookupHitAfterTerminal compressedProofStepDirective
    (Eq.trans (congrArg selectNextScheduled lookup_hit_after_terminal_supported_exact)
      lookup_select_hit_initial_proof)

theorem lookup_hit_initial_proof_no_matches :
    cmatchInputSpec []
        (compressedProofStepDirective.atom ::
          lookupHitAfterTerminal.erase compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  decide +kernel

theorem lookup_hit_after_proof_supported_exact :
    cSupportedSourceExecFacts lookupHitAfterProofProbe =
      [compressedHeapLookupAdvanceDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupHitAfterTerminal
      compressedProofStepDirective _ extract_compressedProofStepRule_exact
      lookup_hit_initial_proof_no_matches lookup_hit_after_terminal_supported_exact)
    (by decide +kernel)

theorem lookup_hit_fault_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitAfterProofProbe =
      some lookupHitAfterFaultProbe := by
  exact lookup_step_of_selected lookupHitAfterProofProbe compressedHeapLookupFaultDirective
    (Eq.trans (congrArg selectNextScheduled lookup_hit_after_proof_supported_exact)
      lookup_select_hit_fault_probe)

theorem lookup_hit_fault_no_matches :
    cmatchInputSpec []
        (compressedHeapLookupFaultDirective.atom ::
          lookupHitAfterProofProbe.erase compressedHeapLookupFaultDirective.atom)
        compressedHeapLookupFaultDirective.rule.input = [] := by
  decide +kernel

theorem lookup_hit_after_fault_supported_exact :
    cSupportedSourceExecFacts lookupHitAfterFaultProbe =
      [compressedHeapLookupAdvanceDirective, compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupHitAfterProofProbe
      compressedHeapLookupFaultDirective _ extract_compressedHeapLookupFaultRule_exact
      lookup_hit_fault_no_matches lookup_hit_after_proof_supported_exact)
    (by decide +kernel)

theorem lookup_hit_assertion_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitAfterFaultProbe =
      some lookupHitAfterAssertionProbe := by
  exact lookup_step_of_selected lookupHitAfterFaultProbe compressedAssertionLaunchDirective
    (Eq.trans (congrArg selectNextScheduled lookup_hit_after_fault_supported_exact)
      lookup_select_assertion_probe)

theorem lookup_hit_assertion_no_matches :
    cmatchInputSpec []
        (compressedAssertionLaunchDirective.atom ::
          lookupHitAfterFaultProbe.erase compressedAssertionLaunchDirective.atom)
        compressedAssertionLaunchDirective.rule.input = [] := by
  decide +kernel

theorem lookup_hit_after_assertion_supported_exact :
    cSupportedSourceExecFacts lookupHitAfterAssertionProbe =
      [compressedHeapLookupAdvanceDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupHitAfterFaultProbe
      compressedAssertionLaunchDirective _ extract_compressedAssertionLaunchRule_exact
      lookup_hit_assertion_no_matches lookup_hit_after_fault_supported_exact)
    (by decide +kernel)

#print axioms lookup_hit_probe_selected
#print axioms lookup_hit_fault_probe_selected
#print axioms lookup_hit_assertion_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
