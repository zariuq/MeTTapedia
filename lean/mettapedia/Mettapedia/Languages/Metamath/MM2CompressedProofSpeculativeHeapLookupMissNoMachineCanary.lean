import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoMachineCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem fault_output_ne_machine (substitution : Subst) :
    instantiateTemplateAtom? substitution missingHeapReferenceFaultTemplate ≠
      some machineWithOneHeapEntry := by
  unfold missingHeapReferenceFaultTemplate machineWithOneHeapEntry
  apply instantiateTemplateAtom?_expression_symbol_head_ne
  decide

/-- The frontier machine is consumed after supplying the heap boundary; the
fault result does not leave a live compressed machine behind. -/
theorem speculative_miss_has_no_live_machine :
    machineWithOneHeapEntry ∉ speculativeMissAfterFrontierFault := by
  rcases speculative_miss_fault_full_instantiates_all with
    ⟨substitution, rowMember, _pending, _lookup, machine, _fault⟩
  unfold speculativeMissAfterFrontierFault
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_miss_fault_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    speculativeMissFrontierFaultRows
    (speculativeMissAfterFrontierProofProbe.erase
      compressedHeapLookupFaultDirective.atom)
    [.remove missingStepPendingTemplate, .remove missingHeapLookupTemplate]
    missingMachineTemplate machineWithOneHeapEntry
    [.add missingHeapReferenceFaultTemplate]
    substitution rowMember machine
  intro sink member
  simp only [List.mem_singleton] at member
  subst sink
  exact Or.inr ⟨missingHeapReferenceFaultTemplate, rfl,
    fun laterSubstitution _ => fault_output_ne_machine laterSubstitution⟩

#print axioms fault_output_ne_machine
#print axioms speculative_miss_has_no_live_machine

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoMachineCanary
