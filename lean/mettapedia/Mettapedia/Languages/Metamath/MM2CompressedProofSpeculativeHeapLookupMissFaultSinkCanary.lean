import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- The authored handler is exactly a three-consume/one-emit transition. -/
theorem speculative_miss_fault_sinks_exact :
    compressedHeapLookupFaultDirective.rule.tmpl.sinks =
      [.remove missingStepPendingTemplate,
       .remove missingHeapLookupTemplate,
       .remove missingMachineTemplate,
       .add missingHeapReferenceFaultTemplate] := by
  rfl

/-- The fault observation is the terminal add sink of the authored handler;
the preceding sinks consume the pending request, lookup cursor, and machine
state. -/
theorem speculative_miss_fault_sink_is_last :
    ∃ before,
      compressedHeapLookupFaultDirective.rule.tmpl.sinks =
        before ++ [.add missingHeapReferenceFaultTemplate] := by
  refine ⟨[.remove missingStepPendingTemplate,
    .remove missingHeapLookupTemplate, .remove missingMachineTemplate], ?_⟩
  exact speculative_miss_fault_sinks_exact

#print axioms speculative_miss_fault_sinks_exact
#print axioms speculative_miss_fault_sink_is_last

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
