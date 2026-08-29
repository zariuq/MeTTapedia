import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Matcher witness for the direct speculative proof hit

A row computed on the minimal positive interface is lifted monotonically into
the actual assembled post-terminal state.  The one row instantiates every
consumed and emitted datum of the transition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.ProcessCalculi.MORK

def directHitSliceRows : List Subst :=
  (Conformance.Computable.cmatchInputSpec [] directHitInputSlice
      speculativeDirectProofDirective.rule.input).map Prod.fst

def directHitFullRows : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
      (speculativeDirectProofDirective.atom ::
        speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
      speculativeDirectProofDirective.rule.input).map Prod.fst

theorem direct_hit_slice_instantiates_frame :
    ∃ substitution ∈ directHitSliceRows,
      instantiateTemplateAtom? substitution directPendingTemplate =
          some directStepPending ∧
        instantiateTemplateAtom? substitution directLookupTemplate =
          some directLookupOne ∧
        instantiateTemplateAtom? substitution directMachineTemplate =
          some machineWithTwoHeapEntries ∧
        instantiateTemplateAtom? substitution directNextMachineTemplate =
          some directNextMachine ∧
        instantiateTemplateAtom? substitution directStackCellTemplate =
          some resolvedStackCell ∧
        instantiateTemplateAtom? substitution directNormalStackCellTemplate =
          some directNormalStackCell ∧
        instantiateTemplateAtom? substitution directResumedScanTemplate =
          some directResumedScan := by
  decide +kernel

theorem direct_hit_slice_in_full_read :
    ∀ atom ∈ directHitInputSlice,
      atom ∈ speculativeDirectProofDirective.atom ::
        speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom := by
  decide +kernel

theorem direct_hit_slice_row_in_full {substitution : Subst}
    (sliceRow : substitution ∈ directHitSliceRows) :
    substitution ∈ directHitFullRows := by
  unfold directHitSliceRows at sliceRow
  unfold directHitFullRows
  rw [List.mem_map] at sliceRow ⊢
  obtain ⟨⟨sliceSubstitution, consumed⟩, matched, rfl⟩ := sliceRow
  refine ⟨(sliceSubstitution, consumed), ?_, rfl⟩
  have compat :
      speculativeDirectProofDirective.rule.input.toPattern?.isSome = true := by
    decide +kernel
  cases inputEq : speculativeDirectProofDirective.rule.input with
  | compat pattern =>
      rw [inputEq] at matched
      exact Conformance.Computable.cmatchPattern_mono [] directHitInputSlice
        (speculativeDirectProofDirective.atom ::
          speculativeHitAfterTerminal.erase
            speculativeDirectProofDirective.atom)
        pattern direct_hit_slice_in_full_read sliceSubstitution consumed matched
  | explicit factors =>
      rw [inputEq] at compat
      simp [InputSpec.toPattern?] at compat

theorem direct_hit_full_instantiates_frame :
    ∃ substitution ∈ directHitFullRows,
      instantiateTemplateAtom? substitution directPendingTemplate =
          some directStepPending ∧
        instantiateTemplateAtom? substitution directLookupTemplate =
          some directLookupOne ∧
        instantiateTemplateAtom? substitution directMachineTemplate =
          some machineWithTwoHeapEntries ∧
        instantiateTemplateAtom? substitution directNextMachineTemplate =
          some directNextMachine ∧
        instantiateTemplateAtom? substitution directStackCellTemplate =
          some resolvedStackCell ∧
        instantiateTemplateAtom? substitution directNormalStackCellTemplate =
          some directNormalStackCell ∧
        instantiateTemplateAtom? substitution directResumedScanTemplate =
          some directResumedScan := by
  rcases direct_hit_slice_instantiates_frame with
    ⟨substitution, sliceRow, pending, lookup, machine, nextMachine, stack,
      normalStack, scan⟩
  exact ⟨substitution, direct_hit_slice_row_in_full sliceRow, pending, lookup,
    machine, nextMachine, stack, normalStack, scan⟩

#print axioms direct_hit_slice_instantiates_frame
#print axioms direct_hit_slice_in_full_read
#print axioms direct_hit_slice_row_in_full
#print axioms direct_hit_full_instantiates_frame

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
