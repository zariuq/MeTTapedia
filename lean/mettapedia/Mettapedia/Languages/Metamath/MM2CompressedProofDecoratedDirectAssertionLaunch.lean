import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionMatch
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Scheduled launch of the decorated speculative assertion handler

This is the compact-to-normal handoff used by the ordered verifier.  The
compiler-produced direct assertion handler is matched and scheduled with its
cursor fallbacks, then one concrete MM2 transition publishes both the normal
assertion interface and the admitted normal-dispatch bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionMatch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def ExactDecoratedDirectAssertionLaunch
    (context : DirectAssertionContext) (space : List Atom) : Prop :=
  ∃ substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst,
    instantiateTemplateAtom? substitution directAssertionPendingTemplate =
        some context.pendingRow ∧
      instantiateTemplateAtom? substitution directAssertionLookupTemplate =
        some context.lookupRow ∧
      instantiateTemplateAtom? substitution directAssertionMachineTemplate =
        some context.machineRow ∧
      instantiateTemplateAtom? substitution directAssertionContextTemplate =
        some context.assertionContextRow ∧
      instantiateTemplateAtom? substitution
          directAssertionNormalControlTemplate = some context.normalControlRow ∧
      instantiateTemplateAtom? substitution directAssertionNormalLabelTemplate =
        some context.normalLabelRow ∧
      instantiateTemplateAtom? substitution directAssertionReloadTemplate =
        some context.reloadRow ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule ∧
      instantiateTemplateAtom? substitution (.var "normal-bridge-rule") =
        some compressedNormalDispatchBridgeRule

@[simp] theorem canonical_decorated_direct_assertion_live_exact
    (context : DirectAssertionContext) :
    decoratedDirectAssertionLive
        (canonicalDecoratedDirectAssertionSpace context) =
      [context.pendingRow, context.lookupRow, context.heapRow,
       context.machineRow, context.headerRow, context.rejoinCaptureRow,
       decoratedDirectAssertionBridgeCaptureRow] ++
        decoratedDirectAssertionSchedulerFrame := by
  unfold decoratedDirectAssertionLive canonicalDecoratedDirectAssertionSpace
  unfold decoratedDirectAssertionMatchSlice decoratedDirectAssertionDataSlice
  change
    (decoratedDirectAssertionDirective.atom ::
      ([context.pendingRow, context.lookupRow, context.heapRow,
        context.machineRow, context.headerRow, context.rejoinCaptureRow,
        decoratedDirectAssertionBridgeCaptureRow] ++
        decoratedDirectAssertionSchedulerFrame)).erase
          decoratedDirectAssertionDirective.atom = _
  rw [List.erase_cons_head]

theorem canonical_decorated_direct_assertion_full_read
    (context : DirectAssertionContext) :
    decoratedDirectAssertionDirective.atom ::
        decoratedDirectAssertionLive
          (canonicalDecoratedDirectAssertionSpace context) =
      decoratedDirectAssertionMatchSlice context ++
        decoratedDirectAssertionSchedulerFrame := by
  rw [canonical_decorated_direct_assertion_live_exact]
  rfl

private theorem decorated_assertion_slice_row_in_full
    (context : DirectAssertionContext) {substitution : Subst}
    (sliceRow : substitution ∈ decoratedDirectAssertionSliceRows context) :
    substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          decoratedDirectAssertionLive
            (canonicalDecoratedDirectAssertionSpace context))
        decoratedDirectAssertionDirective.rule.input).map Prod.fst := by
  unfold decoratedDirectAssertionSliceRows at sliceRow
  rw [List.mem_map] at sliceRow ⊢
  obtain ⟨⟨sliceSubstitution, consumed⟩, matched, rfl⟩ := sliceRow
  refine ⟨(sliceSubstitution, consumed), ?_, rfl⟩
  rw [decoratedDirectAssertionDirective_input_exact] at matched ⊢
  rw [canonical_decorated_direct_assertion_full_read]
  exact Conformance.Computable.cmatchPattern_mono []
    (decoratedDirectAssertionMatchSlice context)
    (decoratedDirectAssertionMatchSlice context ++
      decoratedDirectAssertionSchedulerFrame)
    (mkPattern decoratedDirectAssertionPatterns)
    (fun atom member => List.mem_append_left _ member)
    sliceSubstitution consumed matched

theorem canonical_exact_decorated_direct_assertion_launch
    (context : DirectAssertionContext) :
    ExactDecoratedDirectAssertionLaunch context
      (canonicalDecoratedDirectAssertionSpace context) := by
  rcases decorated_assertion_slice_instantiates_launch context with
    ⟨substitution, sliceRow, outputs⟩
  exact ⟨substitution,
    decorated_assertion_slice_row_in_full context sliceRow, outputs⟩

private theorem pendingRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.pendingRow = none := by rfl

private theorem lookupRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.lookupRow = none := by rfl

private theorem heapRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.heapRow = none := by rfl

private theorem machineRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.machineRow = none := by rfl

private theorem headerRow_no_supported (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.headerRow = none := by rfl

private theorem rejoinCaptureRow_no_supported
    (context : DirectAssertionContext) :
    extractSupportedSourceExecFact context.rejoinCaptureRow = none := by rfl

private theorem bridgeCaptureRow_no_supported :
    extractSupportedSourceExecFact decoratedDirectAssertionBridgeCaptureRow =
      none := by rfl

theorem decoratedDirectAssertionMatchSlice_supported
    (context : DirectAssertionContext) :
    cSupportedSourceExecFacts (decoratedDirectAssertionMatchSlice context) =
      [decoratedDirectAssertionDirective] := by
  have directDecoded :
      extractSupportedSourceExecFact decoratedDirectAssertionDirective.atom =
        some decoratedDirectAssertionDirective := by
    rw [decoratedDirectAssertionDirective_atom_exact]
    exact extract_decoratedDirectAssertionRule_exact
  unfold decoratedDirectAssertionMatchSlice decoratedDirectAssertionDataSlice
    cSupportedSourceExecFacts
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [directDecoded,
    pendingRow_no_supported, lookupRow_no_supported, heapRow_no_supported,
    machineRow_no_supported, headerRow_no_supported,
    rejoinCaptureRow_no_supported, bridgeCaptureRow_no_supported]

private theorem proofDirective_decodes :
    extractSupportedSourceExecFact compressedProofStepDirective.atom =
      some compressedProofStepDirective := by
  change extractSupportedSourceExecFact compressedProofStepRule = _
  exact extract_compressedProofStepRule_exact

private theorem decoratedCursorAssertionDirective_decodes :
    extractSupportedSourceExecFact decoratedCursorAssertionDirective.atom =
      some decoratedCursorAssertionDirective := by
  rw [decoratedCursorAssertionDirective_atom_exact]
  exact extract_decoratedCursorAssertionRule_exact

private theorem lookupFaultDirective_decodes :
    extractSupportedSourceExecFact compressedHeapLookupFaultDirective.atom =
      some compressedHeapLookupFaultDirective := by
  change extractSupportedSourceExecFact compressedHeapLookupFaultRule = _
  exact extract_compressedHeapLookupFaultRule_exact

private theorem lookupAdvanceDirective_decodes :
    extractSupportedSourceExecFact compressedHeapLookupAdvanceDirective.atom =
      some compressedHeapLookupAdvanceDirective := by
  change extractSupportedSourceExecFact compressedHeapLookupAdvanceRule = _
  exact extract_compressedHeapLookupAdvanceRule_exact

theorem decoratedDirectAssertionSchedulerFrame_supported :
    cSupportedSourceExecFacts decoratedDirectAssertionSchedulerFrame =
      [compressedProofStepDirective, decoratedCursorAssertionDirective,
       compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective] := by
  unfold decoratedDirectAssertionSchedulerFrame cSupportedSourceExecFacts
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [proofDirective_decodes, decoratedCursorAssertionDirective_decodes,
    lookupFaultDirective_decodes, lookupAdvanceDirective_decodes]

theorem decoratedAssertionSchedulerAuthority_decodes
    (authority : DecoratedAssertionSchedulerAuthority) :
    extractSupportedSourceExecFact authority.atom =
      some authority.directive := by
  cases authority with
  | proofStep => exact proofDirective_decodes
  | cursorAssertion => exact decoratedCursorAssertionDirective_decodes
  | lookupFault => exact lookupFaultDirective_decodes
  | lookupAdvance => exact lookupAdvanceDirective_decodes

/-- Every physical scheduler atom is the interpretation of a particular
small authority code, and that interpretation passes strict decoding. -/
theorem decoratedDirectAssertionSchedulerFrame_atom_decodes
    {atom : Atom} (member : atom ∈ decoratedDirectAssertionSchedulerFrame) :
    ∃ authority ∈ DecoratedAssertionSchedulerAuthority.all,
      atom = authority.atom ∧
        extractSupportedSourceExecFact atom = some authority.directive := by
  rw [decoratedDirectAssertionSchedulerFrame_eq_atoms] at member
  rcases List.mem_map.mp member with ⟨authority, authorityMember, rfl⟩
  exact ⟨authority, authorityMember, rfl,
    decoratedAssertionSchedulerAuthority_decodes authority⟩

theorem decoratedDirectAssertionSchedulerFrame_not_predecessor_shape
    {atom : Atom} (member : atom ∈ decoratedDirectAssertionSchedulerFrame)
    (tail : List Atom) :
    atom ≠ .expression (.symbol "mm-compressed-step-pending" :: tail) ∧
      atom ≠ .expression (.symbol "mm-compressed-heap-lookup" :: tail) := by
  obtain ⟨authority, _authorityMember, _atomExact, decoded⟩ :=
    decoratedDirectAssertionSchedulerFrame_atom_decodes member
  constructor
  · exact supportedExecAtom_ne_expression_head decoded
      "mm-compressed-step-pending" tail (by decide)
  · exact supportedExecAtom_ne_expression_head decoded
      "mm-compressed-heap-lookup" tail (by decide)

theorem select_decorated_direct_assertion_from_canonical_inventory :
    selectNextScheduled
        [decoratedDirectAssertionDirective, compressedProofStepDirective,
         decoratedCursorAssertionDirective,
         compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective] =
      some decoratedDirectAssertionDirective := by
  decide +kernel

theorem canonicalDecoratedDirectAssertionSpace_supported
    (context : DirectAssertionContext) :
    cSupportedSourceExecFacts
        (canonicalDecoratedDirectAssertionSpace context) =
      [decoratedDirectAssertionDirective, compressedProofStepDirective,
       decoratedCursorAssertionDirective,
       compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective] := by
  unfold canonicalDecoratedDirectAssertionSpace cSupportedSourceExecFacts
  rw [List.filterMap_append]
  change cSupportedSourceExecFacts
      (decoratedDirectAssertionMatchSlice context) ++
      cSupportedSourceExecFacts decoratedDirectAssertionSchedulerFrame = _
  rw [decoratedDirectAssertionMatchSlice_supported,
    decoratedDirectAssertionSchedulerFrame_supported]
  rfl

theorem canonicalDecoratedDirectAssertionSpace_selects
    (context : DirectAssertionContext) :
    selectNextScheduled
        (cSupportedSourceExecFacts
          (canonicalDecoratedDirectAssertionSpace context)) =
      some decoratedDirectAssertionDirective := by
  rw [canonicalDecoratedDirectAssertionSpace_supported]
  exact select_decorated_direct_assertion_from_canonical_inventory

theorem canonicalDecoratedDirectAssertionSpace_steps
    (context : DirectAssertionContext) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (canonicalDecoratedDirectAssertionSpace context) =
      some (cFireReflectiveSourceExecFact
        (canonicalDecoratedDirectAssertionSpace context)
        decoratedDirectAssertionDirective) := by
  simp only [cReflectiveSourceWorkQueueStep,
    canonicalDecoratedDirectAssertionSpace_selects context]

theorem canonicalDecoratedDirectAssertionSpace_inhabits_exact_native_target
    (context : DirectAssertionContext) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (canonicalDecoratedDirectAssertionSpace context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (cFireReflectiveSourceExecFact
          (canonicalDecoratedDirectAssertionSpace context)
          decoratedDirectAssertionDirective)).pred := by
  apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    .leaveInert _ _).2
  exact canonicalDecoratedDirectAssertionSpace_steps context

#print axioms canonical_exact_decorated_direct_assertion_launch
#print axioms decoratedDirectAssertionMatchSlice_supported
#print axioms decoratedDirectAssertionSchedulerFrame_supported
#print axioms decoratedAssertionSchedulerAuthority_decodes
#print axioms decoratedDirectAssertionSchedulerFrame_atom_decodes
#print axioms decoratedDirectAssertionSchedulerFrame_not_predecessor_shape
#print axioms select_decorated_direct_assertion_from_canonical_inventory
#print axioms canonicalDecoratedDirectAssertionSpace_steps
#print axioms canonicalDecoratedDirectAssertionSpace_inhabits_exact_native_target

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
