import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- The terminal reinstalls the ordinary proof handler even when no
proof-valued heap row can resolve the requested index. -/
theorem lookup_fault_initial_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterTerminal =
      some lookupFaultAfterInitialProofProbe := by
  exact lookup_step_of_selected lookupFaultAfterTerminal compressedProofStepDirective
    (Eq.trans (congrArg selectNextScheduled lookup_fault_after_terminal_supported_exact)
      lookup_select_fault_initial_proof)

theorem lookup_fault_initial_proof_no_matches :
    cmatchInputSpec []
        (compressedProofStepDirective.atom ::
          lookupFaultAfterTerminal.erase compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  decide +kernel

theorem lookup_fault_after_initial_proof_supported_exact :
    cSupportedSourceExecFacts lookupFaultAfterInitialProofProbe =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupFaultAfterTerminal
      compressedProofStepDirective _ extract_compressedProofStepRule_exact
      lookup_fault_initial_proof_no_matches lookup_fault_after_terminal_supported_exact)
    (by decide +kernel)

/-- Cursor zero has not reached frontier one, so the first fault probe is
inert and consumed by the ordinary scheduler. -/
theorem lookup_fault_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterInitialProofProbe =
      some lookupFaultAfterProbe := by
  exact lookup_step_of_selected lookupFaultAfterInitialProofProbe
    compressedHeapLookupFaultDirective
    (Eq.trans (congrArg selectNextScheduled lookup_fault_after_initial_proof_supported_exact)
      lookup_select_fault_probe)

theorem lookup_fault_no_matches :
    cmatchInputSpec []
        (compressedHeapLookupFaultDirective.atom ::
          lookupFaultAfterInitialProofProbe.erase
            compressedHeapLookupFaultDirective.atom)
        compressedHeapLookupFaultDirective.rule.input = [] := by
  decide +kernel

theorem lookup_fault_after_fault_supported_exact :
    cSupportedSourceExecFacts lookupFaultAfterProbe =
      [compressedHeapLookupAdvanceDirective, compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupFaultAfterInitialProofProbe
      compressedHeapLookupFaultDirective _ extract_compressedHeapLookupFaultRule_exact
      lookup_fault_no_matches lookup_fault_after_initial_proof_supported_exact)
    (by decide +kernel)

theorem lookup_fault_assertion_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterProbe =
      some lookupFaultAfterAssertionProbe := by
  exact lookup_step_of_selected lookupFaultAfterProbe compressedAssertionLaunchDirective
    (Eq.trans (congrArg selectNextScheduled lookup_fault_after_fault_supported_exact)
      lookup_select_assertion_probe)

theorem lookup_fault_assertion_no_matches :
    cmatchInputSpec []
        (compressedAssertionLaunchDirective.atom ::
          lookupFaultAfterProbe.erase compressedAssertionLaunchDirective.atom)
        compressedAssertionLaunchDirective.rule.input = [] := by
  decide +kernel

theorem lookup_fault_after_assertion_supported_exact :
    cSupportedSourceExecFacts lookupFaultAfterAssertionProbe =
      [compressedHeapLookupAdvanceDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupFaultAfterProbe
      compressedAssertionLaunchDirective _ extract_compressedAssertionLaunchRule_exact
      lookup_fault_assertion_no_matches lookup_fault_after_fault_supported_exact)
    (by decide +kernel)

#print axioms lookup_fault_initial_proof_probe_selected
#print axioms lookup_fault_probe_selected
#print axioms lookup_fault_assertion_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary
