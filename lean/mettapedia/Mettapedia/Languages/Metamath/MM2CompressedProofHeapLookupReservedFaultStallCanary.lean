import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultAdvanceCanary

/-!
# Anti-stall regression with a reserved heap successor

An extra successor edge beyond the live frontier does not suppress the
scheduled frontier fault or permit the lookup to cross that frontier.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultStallCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

private theorem reserved_after_advance_supported_exact :
    cSupportedSourceExecFacts lookupReservedFaultAfterAdvance =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedProofStepDirective, compressedAssertionLaunchDirective] := by
  decide +kernel

theorem reserved_fault_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterAdvance =
      some lookupReservedFaultAfterProofProbe := by
  exact lookup_step_of_selected lookupReservedFaultAfterAdvance
    compressedProofStepDirective
    (Eq.trans (congrArg selectNextScheduled reserved_after_advance_supported_exact)
      lookup_select_fault_initial_proof)

private theorem reserved_frontier_proof_no_matches :
    cmatchInputSpec []
        (compressedProofStepDirective.atom ::
          lookupReservedFaultAfterAdvance.erase compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  decide +kernel

private theorem reserved_after_proof_supported_exact :
    cSupportedSourceExecFacts lookupReservedFaultAfterProofProbe =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupReservedFaultAfterAdvance
      compressedProofStepDirective _ extract_compressedProofStepRule_exact
      reserved_frontier_proof_no_matches reserved_after_advance_supported_exact)
    (by decide +kernel)

theorem reserved_frontier_fault_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterProofProbe =
      some lookupReservedFaultAfterFault := by
  exact lookup_step_of_selected lookupReservedFaultAfterProofProbe
    compressedHeapLookupFaultDirective
    (Eq.trans (congrArg selectNextScheduled reserved_after_proof_supported_exact)
      lookup_select_fault_probe)

/-- Advancing to the live frontier reinstalls its exact consumers, so the
next scheduled proof probe is a genuine step rather than quiescence. -/
theorem reserved_fault_advance_is_not_quiescent :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterAdvance ≠ none := by
  rw [reserved_fault_proof_probe_selected]
  simp

theorem reserved_fault_advance_emits_no_frontier_fault :
    missingOneFault ∉ lookupReservedFaultAfterAdvance := by
  decide +kernel

theorem reserved_successor_faults_continuously :
    CReflectiveReachable .leaveInert 7 lookupReservedFaultProgram
      lookupReservedFaultAfterFault :=
  .step reserved_fault_terminal_selected
    (.step reserved_fault_initial_proof_probe_selected
      (.step reserved_fault_probe_selected
        (.step reserved_fault_assertion_probe_selected
          (.step reserved_fault_advance_selected
            (.step reserved_fault_proof_probe_selected
              (.step reserved_frontier_fault_selected .refl))))))

theorem reserved_successor_frontier_fault_no_proof :
    missingOneFault ∈ lookupReservedFaultAfterFault ∧
      resolvedStackCell ∉ lookupReservedFaultAfterFault := by
  decide +kernel

/-- No prefix through the frontier-fault transition advances to cursor two,
even though the physical successor edge from one to two is present. -/
theorem reserved_successor_never_crosses_frontier :
    ∀ fuel : Fin 8,
      reservedOutOfFrontierLookup ∉
        (cReflectiveSourceWorkQueueRunN .leaveInert fuel.val
          lookupReservedFaultProgram).1 := by
  intro fuel
  fin_cases fuel <;>
    simp only [cReflectiveSourceWorkQueueRunN, reserved_fault_terminal_selected,
      reserved_fault_initial_proof_probe_selected, reserved_fault_probe_selected,
      reserved_fault_assertion_probe_selected, reserved_fault_advance_selected,
      reserved_fault_proof_probe_selected, reserved_frontier_fault_selected] <;>
    decide +kernel

#print axioms reserved_fault_advance_is_not_quiescent
#print axioms reserved_fault_advance_emits_no_frontier_fault
#print axioms reserved_successor_faults_continuously
#print axioms reserved_successor_frontier_fault_no_proof
#print axioms reserved_successor_never_crosses_frontier

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultStallCanary
