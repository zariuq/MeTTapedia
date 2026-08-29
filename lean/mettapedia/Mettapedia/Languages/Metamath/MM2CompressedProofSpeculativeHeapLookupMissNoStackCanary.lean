import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoStackCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem fault_output_ne_resolved_stack (substitution : Subst) :
    instantiateTemplateAtom? substitution missingHeapReferenceFaultTemplate ≠
      some resolvedStackCell := by
  unfold missingHeapReferenceFaultTemplate resolvedStackCell
  apply instantiateTemplateAtom?_expression_symbol_head_ne
  decide

theorem resolved_stack_absent_before_frontier_fault :
    resolvedStackCell ∉
      speculativeMissAfterFrontierProofProbe.erase
        compressedHeapLookupFaultDirective.atom := by
  decide +kernel

theorem speculative_miss_has_no_resolved_stack_cell :
    resolvedStackCell ∉ speculativeMissAfterFrontierFault := by
  unfold speculativeMissAfterFrontierFault
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_miss_fault_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_of_remove_or_nonproducing_add
    speculativeMissFrontierFaultRows
  · intro sink member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨missingStepPendingTemplate, rfl⟩
    · exact Or.inl ⟨missingHeapLookupTemplate, rfl⟩
    · exact Or.inl ⟨missingMachineTemplate, rfl⟩
    · exact Or.inr ⟨missingHeapReferenceFaultTemplate, rfl,
        fun substitution _ => fault_output_ne_resolved_stack substitution⟩
  · exact resolved_stack_absent_before_frontier_fault

#print axioms fault_output_ne_resolved_stack
#print axioms resolved_stack_absent_before_frontier_fault
#print axioms speculative_miss_has_no_resolved_stack_cell

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoStackCanary
