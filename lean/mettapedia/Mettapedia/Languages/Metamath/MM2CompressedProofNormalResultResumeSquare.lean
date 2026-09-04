import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoinSquare
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Three-stage normal-result to resumed-scanner square

The actual output of the transformed normal-result rule feeds the actual
compressed rejoin rule.  Its output then feeds the assertion-resume rule,
using the verifier-owned scanner frame retained across both earlier firings.
No intermediate execution carrier is reconstructed independently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultResumeSquare

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoinSquare
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem scannerCapture_shape {row : Atom}
    (member : row ∈ compressedScannerRuleCaptureRows) :
    ∃ tail, row =
      .expression (.symbol "mm-compressed-owned-runtime-rule" :: tail) := by
  simp only [compressedScannerRuleCaptureRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    unfold compressedOwnedRuntimeRuleRow <;>
    exact ⟨_, rfl⟩

theorem scanner_capture_live_before_normal_result
    (context : NormalResultContext) {row : Atom}
    (member : row ∈ compressedScannerRuleCaptureRows) :
    row ∈ (normalToRejoinSlice context).erase normalResultDirective.atom := by
  unfold normalToRejoinSlice
  rw [List.erase_cons_head]
  exact List.mem_append_right _ member

theorem scanner_capture_survives_normal_result
    (context : NormalResultContext) {row : Atom}
    (member : row ∈ compressedScannerRuleCaptureRows) :
    row ∈ normalToRejoinAfter context := by
  obtain ⟨tail, rfl⟩ := scannerCapture_shape member
  apply normal_result_fire_preserves_expression_head
    (normalToRejoinSlice context)
    "mm-compressed-owned-runtime-rule" tail (by decide)
  exact scanner_capture_live_before_normal_result context member

theorem scanner_capture_survives_rejoin
    (context : NormalResultContext) {row : Atom}
    (member : row ∈ compressedScannerRuleCaptureRows) :
    row ∈ normalResultRejoinResult context := by
  obtain ⟨tail, rfl⟩ := scannerCapture_shape member
  apply compressed_assertion_rejoin_fire_preserves_expression_head
    (normalToRejoinAfter context)
    "mm-compressed-owned-runtime-rule" tail
    (by decide) (by decide) (by decide)
  exact (List.mem_erase_of_ne (by
    change .expression
      (.symbol "mm-compressed-owned-runtime-rule" :: tail) ≠
        compressedAssertionRejoinRule
    simp [compressedAssertionRejoinRule])).2
      (scanner_capture_survives_normal_result context member)

private theorem requiredResumeCaptureRows_subset
    (context : RejoinContext) {row : Atom}
    (member : row ∈ requiredResumeCaptureRows context) :
    row ∈ compressedScannerRuleCaptureRows := by
  simp only [requiredResumeCaptureRows, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    simp [compressedScannerRuleCaptureRows]

private theorem resume_rule_live_after_rejoin (context : NormalResultContext) :
    compressedAssertionResumeDirective.atom ∈
      normalResultRejoinResult context := by
  change compressedAssertionResumeRule ∈ normalResultRejoinResult context
  exact normal_result_then_rejoin_publishes_compact_boundary context
    compressedAssertionResumeRule (by simp [RejoinContext.outputRows])

private theorem resume_row_live_after_rejoin (context : NormalResultContext) :
    context.rejoinContext.resumeRow ∈ normalResultRejoinResult context :=
  normal_result_then_rejoin_publishes_compact_boundary context
    context.rejoinContext.resumeRow (by simp [RejoinContext.outputRows])

theorem normal_result_rejoin_supplies_exact_resume
    (context : NormalResultContext) :
    ExactCompressedAssertionResume context.rejoinContext
      (normalResultRejoinResult context) := by
  apply exact_compressed_assertion_resume_of_live_rows
  intro row member
  simp only [resumeMatchSlice, List.mem_cons] at member
  rcases member with rfl | member
  · exact List.mem_cons_self
  rcases member with rfl | member
  · apply List.mem_cons_of_mem
    exact (List.mem_erase_of_ne (by
      change context.rejoinContext.resumeRow ≠ compressedAssertionResumeRule
      simp [RejoinContext.resumeRow, compressedAssertionResumeRule])).2
        (resume_row_live_after_rejoin context)
  · apply List.mem_cons_of_mem
    have captureMember :=
      requiredResumeCaptureRows_subset context.rejoinContext member
    obtain ⟨tail, rowEq⟩ := scannerCapture_shape captureMember
    subst row
    exact (List.mem_erase_of_ne (by
      change .expression
        (.symbol "mm-compressed-owned-runtime-rule" :: tail) ≠
          compressedAssertionResumeRule
      simp [compressedAssertionResumeRule])).2
        (scanner_capture_survives_rejoin context captureMember)

def normalResultResumeResult (context : NormalResultContext) : List Atom :=
  cFireReflectiveSourceExecFact (normalResultRejoinResult context)
    compressedAssertionResumeDirective

theorem normal_result_rejoin_then_resume_publishes_scanner
    (context : NormalResultContext) :
    ∀ row ∈ resumeOutputRows context.rejoinContext,
      row ∈ normalResultResumeResult context :=
  compressed_assertion_resume_fire_adds_output_rows context.rejoinContext
    (normalResultRejoinResult context)
    (normal_result_rejoin_supplies_exact_resume context)

private theorem rejoin_output_live_for_resume
    (context : NormalResultContext) {row : Atom}
    (member : row ∈ context.rejoinContext.outputRows)
    (notResumeDirective : row ≠ compressedAssertionResumeDirective.atom) :
    row ∈ (normalResultRejoinResult context).erase
      compressedAssertionResumeDirective.atom :=
  (List.mem_erase_of_ne notResumeDirective).2
    (normal_result_then_rejoin_publishes_compact_boundary context row member)

theorem resume_preserves_returned_machine (context : NormalResultContext) :
    context.rejoinContext.returnedMachineRow ∈
      normalResultResumeResult context := by
  apply compressed_assertion_resume_fire_preserves_expression_head
    (normalResultRejoinResult context) "mm-compressed-machine"
    [context.scopeOwner, context.proofOwner,
      context.code context.heapNext, context.code (context.nodeNext + 1),
      context.code (context.stackBase + 1)] (by decide)
  change context.rejoinContext.returnedMachineRow ∈
    (normalResultRejoinResult context).erase
      compressedAssertionResumeDirective.atom
  apply rejoin_output_live_for_resume context
  · exact List.mem_cons_self
  · change context.rejoinContext.returnedMachineRow ≠
      compressedAssertionResumeRule
    simp [RejoinContext.returnedMachineRow, compressedAssertionResumeRule]

theorem resume_preserves_result_node (context : NormalResultContext) :
    context.rejoinContext.resultNodeRow ∈ normalResultResumeResult context := by
  apply compressed_assertion_resume_fire_preserves_expression_head
    (normalResultRejoinResult context) "mm-compressed-node"
    [context.proofOwner, context.code context.nodeNext,
      context.resultFormula, context.rejoinContext.occurrence] (by decide)
  change context.rejoinContext.resultNodeRow ∈
    (normalResultRejoinResult context).erase
      compressedAssertionResumeDirective.atom
  apply rejoin_output_live_for_resume context
  · exact List.mem_cons_of_mem _ (List.mem_cons_self)
  · change context.rejoinContext.resultNodeRow ≠ compressedAssertionResumeRule
    simp [RejoinContext.resultNodeRow, compressedAssertionResumeRule]

theorem resume_preserves_result_stack (context : NormalResultContext) :
    context.rejoinContext.resultStackRow ∈ normalResultResumeResult context := by
  apply compressed_assertion_resume_fire_preserves_expression_head
    (normalResultRejoinResult context) "mm-compressed-stack-cell"
    [context.proofOwner, context.code context.stackBase,
      context.code context.nodeNext] (by decide)
  change context.rejoinContext.resultStackRow ∈
    (normalResultRejoinResult context).erase
      compressedAssertionResumeDirective.atom
  apply rejoin_output_live_for_resume context
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · change context.rejoinContext.resultStackRow ≠
      compressedAssertionResumeRule
    simp [RejoinContext.resultStackRow, compressedAssertionResumeRule]

private def SupportedExecAtomOnly (expected : SourceExecFact)
    (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate = expected

private theorem instantiated_nonexec_supportedOnly
    (expected : SourceExecFact) (substitution : Subst)
    (authoredHead : String) (authoredTail : List Atom) (atom : Atom)
    (headNe : authoredHead ≠ "exec")
    (instantiated : instantiateTemplateAtom? substitution
      (.expression (.symbol authoredHead :: authoredTail)) = some atom) :
    SupportedExecAtomOnly expected atom := by
  unfold instantiateTemplateAtom? at instantiated
  split at instantiated
  · injection instantiated with atomEq
    subst atom
    intro candidate extracted
    simp [applySubst, applySubst.applySubstList,
      extractSupportedSourceExecFact, extractRawExecFact, headNe] at extracted
  · contradiction

private theorem rejoin_template_supportSet :
    ReflectiveSupportSetTemplate
      compressedAssertionRejoinDirective.rule.tmpl := by
  unfold ReflectiveSupportSetTemplate
  rw [compressedAssertionRejoin_sinks_exact]
  intro sink member
  simp only [rejoinSinks, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ReflectiveSupportSetSink]

private theorem supportedFacts_nodup_of_space_nodup
    {space : List Atom} (nodup : space.Nodup) :
    (cSupportedSourceExecFacts space).Nodup := by
  unfold cSupportedSourceExecFacts
  induction space with
  | nil => simp
  | cons atom tail induction =>
      have atomFresh : atom ∉ tail := nodup.notMem
      have tailNodup : tail.Nodup := nodup.of_cons
      simp only [List.filterMap_cons]
      cases decoded : extractSupportedSourceExecFact atom with
      | none => exact induction tailNodup
      | some directive =>
          apply List.nodup_cons.mpr
          constructor
          · intro member
            rcases List.mem_filterMap.mp member with
              ⟨candidate, candidateMember, candidateDecoded⟩
            have atomEq := extractSupportedSourceExecFact_atom decoded
            have candidateEq :=
              extractSupportedSourceExecFact_atom candidateDecoded
            have same : candidate = atom := candidateEq.symm.trans atomEq
            exact atomFresh (same ▸ candidateMember)
          · exact induction tailNodup

private theorem list_eq_singleton_of_nodup_mem_unique
    {items : List SourceExecFact} {expected : SourceExecFact}
    (nodup : items.Nodup) (present : expected ∈ items)
    (unique : ∀ candidate ∈ items, candidate = expected) :
    items = [expected] := by
  cases items with
  | nil => simp at present
  | cons head tail =>
      have headEq := unique head (by simp)
      subst head
      cases tail with
      | nil => rfl
      | cons candidate remaining =>
          have candidateEq : candidate = expected :=
            unique candidate (by simp)
          subst candidate
          simp at nodup

private theorem no_supported_atomsWithin
    {space : List Atom} {expected : SourceExecFact}
    (noneSupported : cSupportedSourceExecFacts space = []) :
    AtomsWithin (SupportedExecAtomOnly expected) space := by
  intro atom member candidate extracted
  have candidateMember : candidate ∈ cSupportedSourceExecFacts space :=
    List.mem_filterMap.mpr ⟨atom, member, extracted⟩
  rw [noneSupported] at candidateMember
  contradiction

private theorem normalToRejoinAfter_supported_exact
    (context : NormalResultContext) :
    cSupportedSourceExecFacts (normalToRejoinAfter context) =
      [compressedAssertionRejoinDirective] := by
  exact list_eq_singleton_of_nodup_mem_unique
    (supportedFacts_nodup_of_space_nodup
      (normalToRejoinAfter_nodup context))
    (compressed_rejoin_supported_after_normal_result context)
    (normalToRejoinAfter_supported_unique context)

private theorem rejoin_live_supported_none
    (context : NormalResultContext) :
    cSupportedSourceExecFacts
        ((normalToRejoinAfter context).erase
          compressedAssertionRejoinDirective.atom) = [] := by
  calc
    cSupportedSourceExecFacts
          ((normalToRejoinAfter context).erase
            compressedAssertionRejoinDirective.atom) =
        (cSupportedSourceExecFacts (normalToRejoinAfter context)).erase
          compressedAssertionRejoinDirective :=
      cSupportedSourceExecFacts_erase _ compressedAssertionRejoinDirective
        extract_compressedAssertionRejoinRule_exact
    _ = [compressedAssertionRejoinDirective].erase
          compressedAssertionRejoinDirective :=
      congrArg (fun facts => facts.erase compressedAssertionRejoinDirective)
        (normalToRejoinAfter_supported_exact context)
    _ = [] := by rw [List.erase_cons_head]

private theorem rejoin_live_without_supported
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionResumeDirective)
      ((normalToRejoinAfter context).erase
        compressedAssertionRejoinDirective.atom) := by
  exact no_supported_atomsWithin (rejoin_live_supported_none context)

private theorem rejoin_added_supportedOnly
    (context : NormalResultContext) :
    ReflectiveAddedAtomsWithin
      (SupportedExecAtomOnly compressedAssertionResumeDirective)
      ((Conformance.Computable.cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          (normalToRejoinAfter context).erase
            compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.rule.input).map Prod.fst)
      compressedAssertionRejoinDirective.rule.tmpl := by
  intro atom added
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq, substitution,
      substitutionMember, instantiated⟩
  rw [compressedAssertionRejoin_sinks_exact] at sinkMember
  simp only [rejoinSinks, List.mem_cons, List.not_mem_nil,
    or_false] at sinkMember
  rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases sinkEq
  · cases sinkEq
  · cases sinkEq
  · cases sinkEq
    unfold rejoinReturnedMachineTemplate at instantiated
    exact instantiated_nonexec_supportedOnly _ _ _ _ _ (by decide)
      instantiated
  · cases sinkEq
    unfold rejoinResultNodeTemplate at instantiated
    exact instantiated_nonexec_supportedOnly _ _ _ _ _ (by decide)
      instantiated
  · cases sinkEq
    unfold rejoinResultStackTemplate at instantiated
    exact instantiated_nonexec_supportedOnly _ _ _ _ _ (by decide)
      instantiated
  · cases sinkEq
    unfold rejoinResumeTemplate at instantiated
    exact instantiated_nonexec_supportedOnly _ _ _ _ _ (by decide)
      instantiated
  · cases sinkEq
    have payloadExact := assertionRejoinMatcherRow_resume_exact
      (normalToRejoinAfter_resume_capabilities context)
      substitutionMember instantiated
    subst atom
    intro candidate extracted
    rw [extract_compressedAssertionResumeRule_exact] at extracted
    exact (Option.some.inj extracted).symm

private theorem normalResultRejoinResult_supportedOnly
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionResumeDirective)
      (normalResultRejoinResult context) := by
  change AtomsWithin
    (SupportedExecAtomOnly compressedAssertionResumeDirective)
    (cApplyReflectiveTemplate
      ((normalToRejoinAfter context).erase
        compressedAssertionRejoinDirective.atom)
      ((Conformance.Computable.cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          (normalToRejoinAfter context).erase
            compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.rule.input).map Prod.fst)
      compressedAssertionRejoinDirective.rule.tmpl)
  exact cApplyReflectiveTemplate_atomsWithin _ _ _ _
    rejoin_template_supportSet
    (rejoin_live_without_supported context)
    (rejoin_added_supportedOnly context)

private theorem normalResultRejoinResult_supported_unique
    (context : NormalResultContext) :
    ∀ candidate ∈ cSupportedSourceExecFacts
        (normalResultRejoinResult context),
      candidate = compressedAssertionResumeDirective := by
  intro candidate member
  rcases List.mem_filterMap.mp member with
    ⟨atom, atomMember, extracted⟩
  exact normalResultRejoinResult_supportedOnly context atom atomMember
    candidate extracted

private theorem normalResultRejoinResult_nodup
    (context : NormalResultContext) :
    (normalResultRejoinResult context).Nodup := by
  exact cFireReflectiveSourceExecFact_nodup _ _ rejoin_template_supportSet
    (normalToRejoinAfter_nodup context)

theorem normalResultRejoinResult_supported
    (context : NormalResultContext) :
    cSupportedSourceExecFacts (normalResultRejoinResult context) =
      [compressedAssertionResumeDirective] := by
  exact list_eq_singleton_of_nodup_mem_unique
    (supportedFacts_nodup_of_space_nodup
      (normalResultRejoinResult_nodup context))
    (List.mem_filterMap.mpr
      ⟨compressedAssertionResumeRule,
        resume_rule_live_after_rejoin context,
        extract_compressedAssertionResumeRule_exact⟩)
    (normalResultRejoinResult_supported_unique context)

theorem normalResultRejoinResult_selects_resume
    (context : NormalResultContext) :
    selectNextScheduled
        (cSupportedSourceExecFacts (normalResultRejoinResult context)) =
      some compressedAssertionResumeDirective := by
  rw [normalResultRejoinResult_supported]
  rfl

theorem normalResultRejoinResult_steps (context : NormalResultContext) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalResultRejoinResult context) =
      some (normalResultResumeResult context) := by
  simp only [cReflectiveSourceWorkQueueStep,
    normalResultRejoinResult_selects_resume, normalResultResumeResult]

theorem normalResultResume_run_three_exact
    (context : NormalResultContext) :
    cReflectiveSourceWorkQueueRunN .leaveInert 3
        (normalToRejoinSlice context) =
      (normalResultResumeResult context, 3) := by
  simp [cReflectiveSourceWorkQueueRunN, normalToRejoinSlice_steps,
    normalToRejoinAfter_steps, normalResultRejoinResult_steps]

theorem normalResultRejoinResult_inhabits_exact_native_target
    (context : NormalResultContext) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (normalResultRejoinResult context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (normalResultResumeResult context)).pred := by
  apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    .leaveInert _ _).2
  exact normalResultRejoinResult_steps context

structure NormalResultCompressedResumeSquare
    (context : NormalResultContext) : Prop where
  exactResume :
    ExactCompressedAssertionResume context.rejoinContext
      (normalResultRejoinResult context)
  resumeScheduled :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalResultRejoinResult context) =
      some (normalResultResumeResult context)
  threeStepRun :
    cReflectiveSourceWorkQueueRunN .leaveInert 3
        (normalToRejoinSlice context) =
      (normalResultResumeResult context, 3)
  publishesScanner :
    ∀ row ∈ resumeOutputRows context.rejoinContext,
      row ∈ normalResultResumeResult context
  preservesMachine :
    context.rejoinContext.returnedMachineRow ∈
      normalResultResumeResult context
  preservesNode :
    context.rejoinContext.resultNodeRow ∈ normalResultResumeResult context
  preservesStack :
    context.rejoinContext.resultStackRow ∈ normalResultResumeResult context
  resumeNativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (normalResultRejoinResult context)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (normalResultResumeResult context)).pred

theorem normal_result_compressed_resume_square
    (context : NormalResultContext) :
    NormalResultCompressedResumeSquare context where
  exactResume := normal_result_rejoin_supplies_exact_resume context
  resumeScheduled := normalResultRejoinResult_steps context
  threeStepRun := normalResultResume_run_three_exact context
  publishesScanner :=
    normal_result_rejoin_then_resume_publishes_scanner context
  preservesMachine := resume_preserves_returned_machine context
  preservesNode := resume_preserves_result_node context
  preservesStack := resume_preserves_result_stack context
  resumeNativeTarget :=
    normalResultRejoinResult_inhabits_exact_native_target context

section AxiomAudit

#print axioms scanner_capture_survives_normal_result
#print axioms scanner_capture_survives_rejoin
#print axioms normal_result_rejoin_supplies_exact_resume
#print axioms normal_result_rejoin_then_resume_publishes_scanner
#print axioms normalResultRejoinResult_supported
#print axioms normalResultRejoinResult_steps
#print axioms normalResultResume_run_three_exact
#print axioms normalResultRejoinResult_inhabits_exact_native_target
#print axioms normal_result_compressed_resume_square

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultResumeSquare
