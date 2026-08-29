import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultMachineCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPendingCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultMachineCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultSliceMatchCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Matching rows used by the actual final fault firing. -/
def speculativeMissFrontierFaultRows : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (compressedHeapLookupFaultDirective.atom ::
        speculativeMissAfterFrontierProofProbe.erase
          compressedHeapLookupFaultDirective.atom)
      compressedHeapLookupFaultDirective.rule.input).map Prod.fst

theorem speculative_miss_fault_slice_in_full_read :
    ∀ atom ∈ speculativeMissFaultInputSlice,
      atom ∈
        compressedHeapLookupFaultDirective.atom ::
          speculativeMissAfterFrontierProofProbe.erase
            compressedHeapLookupFaultDirective.atom := by
  intro atom member
  simp only [speculativeMissFaultInputSlice, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _
      direct_step_pending_in_speculative_miss_fault_live_space
  · exact List.mem_cons_of_mem _
      frontier_lookup_in_speculative_miss_fault_live_space
  · exact List.mem_cons_of_mem _
      machine_in_speculative_miss_fault_live_space

theorem speculative_miss_fault_slice_row_in_full
    {substitution : Subst}
    (sliceRow : substitution ∈ speculativeMissFaultSliceRows) :
    substitution ∈ speculativeMissFrontierFaultRows := by
  unfold speculativeMissFaultSliceRows at sliceRow
  unfold speculativeMissFrontierFaultRows
  rw [List.mem_map] at sliceRow ⊢
  obtain ⟨⟨sliceSubstitution, consumed⟩, matched, rfl⟩ := sliceRow
  refine ⟨(sliceSubstitution, consumed), ?_, rfl⟩
  obtain ⟨pattern, inputEq⟩ :
      ∃ pattern,
        compressedHeapLookupFaultDirective.rule.input = .compat pattern := by
    simp [compressedHeapLookupFaultDirective]
  rw [inputEq] at matched ⊢
  exact Conformance.Computable.cmatchPattern_mono []
    speculativeMissFaultInputSlice
    (compressedHeapLookupFaultDirective.atom ::
      speculativeMissAfterFrontierProofProbe.erase
        compressedHeapLookupFaultDirective.atom)
    pattern speculative_miss_fault_slice_in_full_read sliceSubstitution consumed
    matched

/-- The concrete frontier state supplies a real matcher row instantiating the
authored fault observation.  This computes matching and substitution without
reducing the complete successor state. -/
theorem speculative_miss_fault_instantiation_witness :
    ∃ substitution ∈ speculativeMissFrontierFaultRows,
      instantiateTemplateAtom? substitution
          missingHeapReferenceFaultTemplate =
        some missingOneFault := by
  rcases speculative_miss_fault_slice_instantiates with
    ⟨substitution, sliceRow, instantiates⟩
  exact ⟨substitution,
    speculative_miss_fault_slice_row_in_full sliceRow, instantiates⟩

/-- The live frontier match instantiates all three consumed atoms and the
exact emitted fault with one substitution. -/
theorem speculative_miss_fault_full_instantiates_all :
    ∃ substitution ∈ speculativeMissFrontierFaultRows,
      instantiateTemplateAtom? substitution missingStepPendingTemplate =
          some directStepPending ∧
        instantiateTemplateAtom? substitution missingHeapLookupTemplate =
          some frontierLookupOne ∧
        instantiateTemplateAtom? substitution missingMachineTemplate =
          some machineWithOneHeapEntry ∧
        instantiateTemplateAtom? substitution
            missingHeapReferenceFaultTemplate =
          some missingOneFault := by
  rcases speculative_miss_fault_slice_instantiates_all with
    ⟨substitution, sliceRow, pending, lookup, machine, fault⟩
  exact ⟨substitution,
    speculative_miss_fault_slice_row_in_full sliceRow,
    pending, lookup, machine, fault⟩

#print axioms speculative_miss_fault_slice_row_in_full
#print axioms speculative_miss_fault_instantiation_witness
#print axioms speculative_miss_fault_full_instantiates_all

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInstantiationCanary
