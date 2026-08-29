import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoLookupCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem fault_output_ne_lookup (substitution : Subst)
    (lookup : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (lookupHead : ∃ tail,
      lookup = .expression (.symbol "mm-compressed-heap-lookup" :: tail)) :
    instantiateTemplateAtom? substitution missingHeapReferenceFaultTemplate ≠
      some lookup := by
  obtain ⟨tail, rfl⟩ := lookupHead
  unfold missingHeapReferenceFaultTemplate
  apply instantiateTemplateAtom?_expression_symbol_head_ne
  decide

theorem fault_output_ne_direct_lookup (substitution : Subst) :
    instantiateTemplateAtom? substitution missingHeapReferenceFaultTemplate ≠
      some directLookupOne := by
  apply fault_output_ne_lookup substitution directLookupOne
  unfold directLookupOne
  exact ⟨_, rfl⟩

theorem fault_output_ne_frontier_lookup (substitution : Subst) :
    instantiateTemplateAtom? substitution missingHeapReferenceFaultTemplate ≠
      some frontierLookupOne := by
  apply fault_output_ne_lookup substitution frontierLookupOne
  unfold frontierLookupOne
  exact ⟨_, rfl⟩

/-- Cursor one, the actual first-free heap frontier, is consumed by the fault
transition and cannot be recreated by its output sink. -/
theorem speculative_miss_has_no_frontier_lookup :
    frontierLookupOne ∉ speculativeMissAfterFrontierFault := by
  rcases speculative_miss_fault_full_instantiates_all with
    ⟨substitution, rowMember, _pending, lookup, _machine, _fault⟩
  unfold speculativeMissAfterFrontierFault
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_miss_fault_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    speculativeMissFrontierFaultRows
    (speculativeMissAfterFrontierProofProbe.erase
      compressedHeapLookupFaultDirective.atom)
    [.remove missingStepPendingTemplate]
    missingHeapLookupTemplate frontierLookupOne
    [.remove missingMachineTemplate, .add missingHeapReferenceFaultTemplate]
    substitution rowMember lookup
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl ⟨missingMachineTemplate, rfl⟩
  · exact Or.inr ⟨missingHeapReferenceFaultTemplate, rfl,
      fun laterSubstitution _ =>
        fault_output_ne_frontier_lookup laterSubstitution⟩

theorem direct_lookup_absent_before_frontier_fault :
    directLookupOne ∉
      speculativeMissAfterFrontierProofProbe.erase
        compressedHeapLookupFaultDirective.atom := by
  decide +kernel

theorem speculative_miss_has_no_live_lookup :
    directLookupOne ∉ speculativeMissAfterFrontierFault := by
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
        fun substitution _ => fault_output_ne_direct_lookup substitution⟩
  · exact direct_lookup_absent_before_frontier_fault

#print axioms fault_output_ne_lookup
#print axioms fault_output_ne_direct_lookup
#print axioms fault_output_ne_frontier_lookup
#print axioms speculative_miss_has_no_frontier_lookup
#print axioms direct_lookup_absent_before_frontier_fault
#print axioms speculative_miss_has_no_live_lookup

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoLookupCanary
