import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoPendingCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem fault_output_ne_pending (substitution : Subst) :
    instantiateTemplateAtom? substitution missingHeapReferenceFaultTemplate ≠
      some directStepPending := by
  unfold missingHeapReferenceFaultTemplate directStepPending
  apply instantiateTemplateAtom?_expression_symbol_head_ne
  decide

theorem speculative_miss_has_no_pending_step :
    directStepPending ∉ speculativeMissAfterFrontierFault := by
  rcases speculative_miss_fault_full_instantiates_all with
    ⟨substitution, rowMember, pending, _lookup, _machine, _fault⟩
  unfold speculativeMissAfterFrontierFault
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_miss_fault_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    speculativeMissFrontierFaultRows
    (speculativeMissAfterFrontierProofProbe.erase
      compressedHeapLookupFaultDirective.atom)
    [] missingStepPendingTemplate directStepPending
    [.remove missingHeapLookupTemplate, .remove missingMachineTemplate,
      .add missingHeapReferenceFaultTemplate]
    substitution rowMember pending
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Or.inl ⟨missingHeapLookupTemplate, rfl⟩
  · exact Or.inl ⟨missingMachineTemplate, rfl⟩
  · exact Or.inr ⟨missingHeapReferenceFaultTemplate, rfl,
      fun laterSubstitution _ => fault_output_ne_pending laterSubstitution⟩

#print axioms fault_output_ne_pending
#print axioms speculative_miss_has_no_pending_step

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoPendingCanary
