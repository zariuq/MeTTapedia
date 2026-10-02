import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

theorem reserved_fault_initial_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterTerminal =
      some lookupReservedFaultAfterInitialProofProbe := by
  exact lookup_step_of_selected lookupReservedFaultAfterTerminal
    compressedProofStepDirective
    (Eq.trans (congrArg selectNextScheduled reserved_fault_after_terminal_supported_exact)
      lookup_select_fault_initial_proof)

private theorem reserved_initial_proof_no_matches :
    cmatchInputSpec []
        (compressedProofStepDirective.atom ::
          lookupReservedFaultAfterTerminal.erase compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  decide +kernel

private theorem reserved_after_initial_proof_supported_exact :
    cSupportedSourceExecFacts lookupReservedFaultAfterInitialProofProbe =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupReservedFaultAfterTerminal
      compressedProofStepDirective _ extract_compressedProofStepRule_exact
      reserved_initial_proof_no_matches reserved_fault_after_terminal_supported_exact)
    (by decide +kernel)

theorem reserved_fault_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterInitialProofProbe =
      some lookupReservedFaultAfterProbe := by
  exact lookup_step_of_selected lookupReservedFaultAfterInitialProofProbe
    compressedHeapLookupFaultDirective
    (Eq.trans (congrArg selectNextScheduled reserved_after_initial_proof_supported_exact)
      lookup_select_fault_probe)

private theorem reserved_initial_fault_no_matches :
    cmatchInputSpec []
        (compressedHeapLookupFaultDirective.atom ::
          lookupReservedFaultAfterInitialProofProbe.erase
            compressedHeapLookupFaultDirective.atom)
        compressedHeapLookupFaultDirective.rule.input = [] := by
  decide +kernel

private theorem reserved_after_initial_fault_supported_exact :
    cSupportedSourceExecFacts lookupReservedFaultAfterProbe =
      [compressedHeapLookupAdvanceDirective, compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupReservedFaultAfterInitialProofProbe
      compressedHeapLookupFaultDirective _ extract_compressedHeapLookupFaultRule_exact
      reserved_initial_fault_no_matches reserved_after_initial_proof_supported_exact)
    (by decide +kernel)

theorem reserved_fault_assertion_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupReservedFaultAfterProbe =
      some lookupReservedFaultAfterAssertionProbe := by
  exact lookup_step_of_selected lookupReservedFaultAfterProbe
    compressedAssertionLaunchDirective
    (Eq.trans (congrArg selectNextScheduled reserved_after_initial_fault_supported_exact)
      lookup_select_assertion_probe)

private theorem reserved_initial_assertion_no_matches :
    cmatchInputSpec []
        (compressedAssertionLaunchDirective.atom ::
          lookupReservedFaultAfterProbe.erase compressedAssertionLaunchDirective.atom)
        compressedAssertionLaunchDirective.rule.input = [] := by
  decide +kernel

theorem reserved_after_initial_assertion_supported_exact :
    cSupportedSourceExecFacts lookupReservedFaultAfterAssertionProbe =
      [compressedHeapLookupAdvanceDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupReservedFaultAfterProbe
      compressedAssertionLaunchDirective _ extract_compressedAssertionLaunchRule_exact
      reserved_initial_assertion_no_matches reserved_after_initial_fault_supported_exact)
    (by decide +kernel)

#print axioms reserved_fault_initial_proof_probe_selected
#print axioms reserved_fault_probe_selected
#print axioms reserved_fault_assertion_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary
