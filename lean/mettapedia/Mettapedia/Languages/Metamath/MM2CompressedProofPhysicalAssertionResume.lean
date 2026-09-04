import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionRejoin
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous

/-!
# Physical compressed-assertion resume

The exact physical assertion-rejoin successor schedules and executes the
scanner-resume directive under rule-scoped MORK execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionResume

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalResult
open Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private theorem instantiateRuleTemplateAtom?_of_reflective
    (input : InputSpec) {substitution : Subst} {template candidate : Atom}
    (instantiated : instantiateTemplateAtom? substitution template =
      some candidate) :
    instantiateRuleTemplateAtom? input substitution template =
      some candidate := by
  cases covered : templateCovered substitution template with
  | false => simp [instantiateTemplateAtom?, covered] at instantiated
  | true =>
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?_of_covered
        input substitution template covered]
      exact instantiated

/-! ## Physical assertion resume -/

def physicalAssertionResumeMatcherRows (space : List Atom) : List Subst :=
  let live := morkEraseSupport space compressedAssertionResumeDirective.atom
  let read := morkInsertSupport live compressedAssertionResumeDirective.atom
  ((cMatchInputSpecMork [] read
      compressedAssertionResumeDirective.rule.input).filter fun
      (substitution, _) =>
        matchSourceGuards substitution
          compressedAssertionResumeDirective.rule.guards).map Prod.fst

theorem compressedAssertionResumeDirective_guards_exact :
    compressedAssertionResumeDirective.rule.guards = [] := by
  decide +kernel

theorem physical_assertion_resume_live_eq
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionResumeDirective.atom ∈ space) :
    morkEraseSupport space compressedAssertionResumeDirective.atom =
      space.erase compressedAssertionResumeDirective.atom :=
  morkEraseSupport_eq_erase_of_mem space
    compressedAssertionResumeDirective.atom listNodup morkNodup
      directivePresent

theorem physical_assertion_resume_read_perm
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionResumeDirective.atom ∈ space) :
    (morkInsertSupport
        (morkEraseSupport space compressedAssertionResumeDirective.atom)
        compressedAssertionResumeDirective.atom).Perm
      (compressedAssertionResumeDirective.atom ::
        space.erase compressedAssertionResumeDirective.atom) := by
  rw [physical_assertion_resume_live_eq listNodup morkNodup
    directivePresent]
  have absent : morkSupportContains
      (space.erase compressedAssertionResumeDirective.atom)
        compressedAssertionResumeDirective.atom = false := by
    rw [← physical_assertion_resume_live_eq listNodup morkNodup
      directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      compressedAssertionResumeDirective.atom
  unfold morkInsertSupport
  rw [absent]
  exact List.perm_append_singleton compressedAssertionResumeDirective.atom
    (space.erase compressedAssertionResumeDirective.atom)

theorem physical_assertion_resume_matcher_mem_iff
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionResumeDirective.atom ∈ space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedAssertionResumeDirective.atom)
            compressedAssertionResumeDirective.atom)
          compressedAssertionResumeDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (compressedAssertionResumeDirective.atom ::
            space.erase compressedAssertionResumeDirective.atom)
          compressedAssertionResumeDirective.rule.input := by
  rw [compressedAssertionResume_input_exact]
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  have readPerm := physical_assertion_resume_read_perm listNodup morkNodup
    directivePresent
  constructor
  · intro member
    exact cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mp atomMember)
      substitution consumed member
  · intro member
    exact cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mpr atomMember)
      substitution consumed member

def PhysicalExactCompressedAssertionResumeFor
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalAssertionResumeMatcherRows space,
    List.Forall₂
      (fun authored concrete =>
        instantiateRuleTemplateAtom?
          compressedAssertionResumeDirective.rule.input substitution
            authored = some concrete)
      assertionResumeOutputTemplates (resumeOutputRowsFor rules context)

def PhysicalExactCompressedAssertionResume (context : RejoinContext)
    (space : List Atom) : Prop :=
  PhysicalExactCompressedAssertionResumeFor baseScannerRuntimeRuleBundle
    context space

theorem physical_exact_assertion_resume_for_of_reflective
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionResumeDirective.atom ∈ space)
    (matched : ExactCompressedAssertionResumeFor rules context space) :
    PhysicalExactCompressedAssertionResumeFor rules context space := by
  rcases matched with ⟨substitution, rowMember, outputs⟩
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, reflected, equal⟩ := rowMember
  simp only at equal
  subst matchedSubstitution
  have reflected' :=
    (physical_assertion_resume_matcher_mem_iff listNodup morkNodup
      directivePresent substitution consumed).2 reflected
  have physicalRow : substitution ∈ physicalAssertionResumeMatcherRows space := by
    unfold physicalAssertionResumeMatcherRows
    rw [List.mem_map]
    refine ⟨(substitution, consumed), ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨reflected', ?_⟩
    rw [compressedAssertionResumeDirective_guards_exact]
    rfl
  refine ⟨substitution, physicalRow, ?_⟩
  exact outputs.imp fun authored concrete instantiated =>
    instantiateRuleTemplateAtom?_of_reflective _ instantiated

theorem physical_exact_assertion_resume_of_reflective
    (context : RejoinContext) {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionResumeDirective.atom ∈ space)
    (matched : ExactCompressedAssertionResume context space) :
    PhysicalExactCompressedAssertionResume context space := by
  exact physical_exact_assertion_resume_for_of_reflective
    baseScannerRuntimeRuleBundle context listNodup morkNodup directivePresent
    matched

/-- Any physical frame containing the selected inventory's complete resume
slice admits the same exact MORK matcher and output substitution. -/
theorem physical_exact_assertion_resume_for_of_live_rows
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionResumeDirective.atom ∈ space)
    (included : ∀ row ∈ resumeMatchSliceFor rules context,
      row ∈ compressedAssertionResumeDirective.atom ::
        space.erase compressedAssertionResumeDirective.atom) :
    PhysicalExactCompressedAssertionResumeFor rules context space := by
  apply physical_exact_assertion_resume_for_of_reflective rules context
    listNodup morkNodup directivePresent
  exact exact_compressed_assertion_resume_for_of_live_rows rules context space
    included

private theorem physical_output_rows_support_of_forall₂
    (input : InputSpec) (matcherRows : List Subst) (space : List Atom)
    (substitution : Subst) (rowMember : substitution ∈ matcherRows)
    {templates concreteRows : List Atom}
    (outputs : List.Forall₂
      (fun authored concrete =>
        instantiateRuleTemplateAtom? input substitution authored =
          some concrete)
      templates concreteRows) (before : List Sink) :
    ∀ row ∈ concreteRows,
      morkSupportContains
        (cApplyRuleScopedSinkBatch input matcherRows space
          (before ++ templates.map Sink.add)) row = true := by
  induction outputs generalizing before with
  | nil => simp
  | cons instantiated remaining induction =>
      rename_i authored concrete tailTemplates concreteRows
      intro row member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
          input matcherRows space before authored row
          (tailTemplates.map Sink.add) substitution rowMember instantiated
        intro sink sinkMember
        rcases List.mem_map.mp sinkMember with ⟨later, _, rfl⟩
        exact Or.inl ⟨later, rfl⟩
      · have retained := induction (before ++ [.add authored]) row member
        simpa [List.map_cons, List.append_assoc] using retained

/-- Every row instantiated by a physical assertion-resume match survives the
complete MORK sink batch at its compact support key.  The theorem is relative
to the selected scanner inventory, so transformed continuations cannot fall
back to base-verifier constants. -/
theorem physical_assertion_resume_fire_adds_output_support_for
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    (space : List Atom)
    (matched : PhysicalExactCompressedAssertionResumeFor rules context
      space) :
    ∀ row ∈ resumeOutputRowsFor rules context,
      morkSupportContains
        (cFireRuleScopedSourceExecFact space
          compressedAssertionResumeDirective) row = true := by
  intro row member
  rcases matched with ⟨substitution, rowMember, outputs⟩
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  rw [compressedAssertionResume_sinks_exact]
  unfold assertionResumeSinks
  simpa [physicalAssertionResumeMatcherRows] using
    (physical_output_rows_support_of_forall₂
      compressedAssertionResumeDirective.rule.input
      (physicalAssertionResumeMatcherRows space)
      (morkEraseSupport space compressedAssertionResumeDirective.atom)
      substitution rowMember outputs [.remove assertionResumeRequestTemplate]
      row member)

/-- Actual physical successor of an assertion-resume directive in an
arbitrary represented execution frame. -/
def physicalAssertionResumeResultFrom (space : List Atom) : List Atom :=
  cFireRuleScopedSourceExecFact space compressedAssertionResumeDirective

/-- If resume is the unique scheduled directive, the work queue performs the
physical resume firing rather than an independently reconstructed step. -/
theorem physical_assertion_resume_ruleScoped_step_from
    (space : List Atom)
    (supportedExact :
      cSupportedSourceExecFacts space =
        [compressedAssertionResumeDirective]) :
    cRuleScopedSourceWorkQueueStep .leaveInert space =
      some (physicalAssertionResumeResultFrom space) := by
  unfold cRuleScopedSourceWorkQueueStep physicalAssertionResumeResultFrom
  rw [supportedExact]
  rfl

/-- One presentation-relative assertion resume is an actual nonempty MORK
segment, classified by the OSLF-generated native type, preserving both forms
of duplicate freedom and publishing the complete selected scanner inventory.
-/
structure PhysicalAssertionResumeScheduledSegmentFor
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    (space : List Atom) : Type where
  exactPhysicalMatch : PhysicalExactCompressedAssertionResumeFor rules
    context space
  supportedExact : cSupportedSourceExecFacts space =
    [compressedAssertionResumeDirective]
  concreteStep : cRuleScopedSourceWorkQueueStep .leaveInert space =
    some (physicalAssertionResumeResultFrom space)
  trace : CRuleScopedTrace .leaveInert 1 space
    (physicalAssertionResumeResultFrom space)
  nativeTypeTrace : RuleScopedNativeTypeTrace .leaveInert 1 space
    (physicalAssertionResumeResultFrom space)
  outputSupport : ∀ row ∈ resumeOutputRowsFor rules context,
    morkSupportContains (physicalAssertionResumeResultFrom space) row = true
  resultListNodup : (physicalAssertionResumeResultFrom space).Nodup
  resultMorkNodup : MorkSupportNodup
    (physicalAssertionResumeResultFrom space)

def physical_assertion_resume_scheduled_segment_for
    (rules : ScannerRuntimeRuleBundle) (context : RejoinContext)
    (space : List Atom) (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (exactMatch : PhysicalExactCompressedAssertionResumeFor rules context
      space)
    (supportedExact : cSupportedSourceExecFacts space =
      [compressedAssertionResumeDirective]) :
    PhysicalAssertionResumeScheduledSegmentFor rules context space := by
  have moved := physical_assertion_resume_ruleScoped_step_from space
    supportedExact
  let executionTrace : CRuleScopedTrace .leaveInert 1 space
      (physicalAssertionResumeResultFrom space) := .step moved .refl
  exact
    { exactPhysicalMatch := exactMatch
      supportedExact := supportedExact
      concreteStep := moved
      trace := executionTrace
      nativeTypeTrace := executionTrace.toNativeTypeTrace
      outputSupport := by
        simpa [physicalAssertionResumeResultFrom] using
          physical_assertion_resume_fire_adds_output_support_for rules context
            space exactMatch
      resultListNodup :=
        cFireRuleScopedSourceExecFact_list_nodup space
          compressedAssertionResumeDirective listNodup
      resultMorkNodup :=
        cFireRuleScopedSourceExecFact_mork_nodup space
          compressedAssertionResumeDirective morkNodup }

private theorem required_resume_capture_mem_reference_live
    (context : NormalResultContext)
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) {row : Atom}
    (member : row ∈ requiredResumeCaptureRows context.rejoinContext) :
    row ∈ ((((physicalNormalResultReference context).erase
        compressedAssertionRejoinDirective.atom).erase
        context.rejoinContext.contextRow).erase
        context.rejoinContext.returnedControlRow).erase
        context.rejoinContext.normalLabelRow := by
  have scannerMember : row ∈ compressedScannerRuleCaptureRows := by
    simp only [requiredResumeCaptureRows, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [compressedScannerRuleCaptureRows]
  have tailMember : row ∈
      [context.bodyBuiltRow, context.rejoinCaptureRow,
        context.rejoinContext.contextRow,
        context.rejoinContext.normalStackSuccessorRow,
        context.rejoinContext.nodeSuccessorRow,
        context.rejoinContext.normalLabelRow,
        context.rejoinContext.resumeCaptureRow] ++
          compressedScannerRuleCaptureRows :=
    List.mem_append_right _ scannerMember
  have sliceNodup := normalToRejoinSlice_nodup context
  have notNormalResult : row ≠ normalResultDirective.atom := by
    intro equal
    subst row
    exact sliceNodup.notMem tailMember
  have tailNodup := sliceNodup.of_cons
  have crossPrefix := (List.nodup_append.mp tailNodup).2.2
  have notBody : row ≠ context.bodyBuiltRow :=
    (crossPrefix context.bodyBuiltRow (by simp) row scannerMember).symm
  have notContext : row ≠ context.rejoinContext.contextRow :=
    (crossPrefix context.rejoinContext.contextRow (by simp) row
      scannerMember).symm
  have notLabel : row ≠ context.rejoinContext.normalLabelRow :=
    (crossPrefix context.rejoinContext.normalLabelRow (by simp) row
      scannerMember).symm
  have sliceMember : row ∈ normalToRejoinSlice context :=
    List.mem_cons_of_mem normalResultDirective.atom tailMember
  have afterNormal := (List.mem_erase_of_ne notNormalResult).2 sliceMember
  have afterBody := (List.mem_erase_of_ne notBody).2 afterNormal
  have preNodup : (physicalNormalResultReference context).Nodup :=
    List.Nodup.of_map morkSupportKey preReferenceMorkNodup
  have preSplit :
      (((normalToRejoinSlice context).erase
          normalResultDirective.atom).erase context.bodyBuiltRow ++
        [context.rejoinContext.returnedControlRow,
         context.rejoinContext.returnedStackRow,
         normalAssertionReloadAtom context.proofOwner,
         compressedAssertionRejoinRule]).Nodup := by
    simpa [physicalNormalResultReference] using preNodup
  have crossOutput := (List.nodup_append.mp preSplit).2.2
  have notControl : row ≠ context.rejoinContext.returnedControlRow :=
    crossOutput row afterBody context.rejoinContext.returnedControlRow (by simp)
  have notRejoin : row ≠ compressedAssertionRejoinDirective.atom := by
    change row ≠ compressedAssertionRejoinRule
    exact crossOutput row afterBody compressedAssertionRejoinRule (by simp)
  have preReference : row ∈ physicalNormalResultReference context :=
    List.mem_append_left _ afterBody
  have afterRejoin := (List.mem_erase_of_ne notRejoin).2 preReference
  have afterContext := (List.mem_erase_of_ne notContext).2 afterRejoin
  have afterControl := (List.mem_erase_of_ne notControl).2 afterContext
  have afterLabel := (List.mem_erase_of_ne notLabel).2 afterControl
  exact afterLabel

private theorem resume_row_mem_reference (context : NormalResultContext) :
    context.rejoinContext.resumeRow ∈
      physicalAssertionRejoinReference context := by
  unfold physicalAssertionRejoinReference
  apply List.mem_append_right
  simp [RejoinContext.outputRows]

private theorem resume_directive_mem_reference
    (context : NormalResultContext) :
    compressedAssertionResumeDirective.atom ∈
      physicalAssertionRejoinReference context := by
  unfold physicalAssertionRejoinReference
  apply List.mem_append_right
  change compressedAssertionResumeRule ∈ context.rejoinContext.outputRows
  simp [RejoinContext.outputRows]

private theorem resume_output_rows_nodup
    (context : NormalResultContext)
    (referenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    context.rejoinContext.outputRows.Nodup := by
  have referenceNodup : (physicalAssertionRejoinReference context).Nodup :=
    List.Nodup.of_map morkSupportKey referenceMorkNodup
  unfold physicalAssertionRejoinReference at referenceNodup
  exact (List.nodup_append.mp referenceNodup).2.1

private theorem resume_row_ne_resume_directive
    (context : NormalResultContext)
    (referenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    context.rejoinContext.resumeRow ≠
      compressedAssertionResumeDirective.atom := by
  have outputNodup := resume_output_rows_nodup context referenceMorkNodup
  change [context.rejoinContext.returnedMachineRow,
    context.rejoinContext.resultNodeRow,
    context.rejoinContext.resultStackRow,
    context.rejoinContext.resumeRow,
    compressedAssertionResumeRule].Nodup at outputNodup
  have resumeFresh := outputNodup.of_cons.of_cons.of_cons.notMem
  change context.rejoinContext.resumeRow ≠ compressedAssertionResumeRule
  simpa only [List.mem_singleton] using resumeFresh

theorem physical_assertion_rejoin_supplies_exact_resume
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (resultReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    PhysicalExactCompressedAssertionResume context.rejoinContext
      (physicalAssertionRejoinResult context) := by
  have perm := physical_assertion_rejoin_perm_reference context inputMorkNodup
    preReferenceMorkNodup resultReferenceMorkNodup
  have listNodup : (physicalAssertionRejoinResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (cFireRuleScopedSourceExecFact_list_nodup _ _
        (normalToRejoinSlice_nodup context))
  have morkNodup : MorkSupportNodup
      (physicalAssertionRejoinResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _
      (cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup)
  have directivePresent : compressedAssertionResumeDirective.atom ∈
      physicalAssertionRejoinResult context := by
    apply perm.mem_iff.mpr
    exact resume_directive_mem_reference context
  apply physical_exact_assertion_resume_of_reflective context.rejoinContext
    listNodup morkNodup directivePresent
  apply exact_compressed_assertion_resume_of_live_rows
  intro row member
  simp only [resumeMatchSlice, List.mem_cons] at member
  rcases member with rfl | member
  · exact List.mem_cons_self
  rcases member with rfl | member
  · apply List.mem_cons_of_mem
    apply (List.mem_erase_of_ne ?_).2
    · exact perm.mem_iff.mpr (resume_row_mem_reference context)
    · exact resume_row_ne_resume_directive context resultReferenceMorkNodup
  · apply List.mem_cons_of_mem
    apply (List.mem_erase_of_ne ?_).2
    · apply perm.mem_iff.mpr
      unfold physicalAssertionRejoinReference
      apply List.mem_append_left
      exact required_resume_capture_mem_reference_live context
        preReferenceMorkNodup member
    · have captureLive := required_resume_capture_mem_reference_live context
        preReferenceMorkNodup member
      have referenceNodup : (physicalAssertionRejoinReference context).Nodup :=
        List.Nodup.of_map morkSupportKey resultReferenceMorkNodup
      unfold physicalAssertionRejoinReference at referenceNodup
      have cross := (List.nodup_append.mp referenceNodup).2.2
      apply cross row captureLive compressedAssertionResumeDirective.atom
      change compressedAssertionResumeRule ∈ context.rejoinContext.outputRows
      simp [RejoinContext.outputRows]

def physicalAssertionResumeResult (context : NormalResultContext) : List Atom :=
  cFireRuleScopedSourceExecFact (physicalAssertionRejoinResult context)
    compressedAssertionResumeDirective

private theorem extract_supported_none_of_expression_head_ne
    (head : String) (tail : List Atom) (different : head ≠ "exec") :
    extractSupportedSourceExecFact
      (.expression (.symbol head :: tail)) = none := by
  simp [extractSupportedSourceExecFact, extractRawExecFact, different]

private theorem supported_facts_nodup_of_space_nodup
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
            exact atomFresh (candidateEq.symm.trans atomEq ▸ candidateMember)
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

theorem physicalAssertionRejoinReference_supported_exact
    (context : NormalResultContext)
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    cSupportedSourceExecFacts (physicalAssertionRejoinReference context) =
      [compressedAssertionResumeDirective] := by
  apply list_eq_singleton_of_nodup_mem_unique
  · exact supported_facts_nodup_of_space_nodup
      (List.Nodup.of_map morkSupportKey referenceMorkNodup)
  · exact List.mem_filterMap.mpr
      ⟨compressedAssertionResumeRule,
        resume_directive_mem_reference context,
        extract_compressedAssertionResumeRule_exact⟩
  · intro candidate candidateMember
    rcases List.mem_filterMap.mp candidateMember with
      ⟨atom, atomMember, extracted⟩
    simp only [physicalAssertionRejoinReference, List.mem_append] at atomMember
    rcases atomMember with live | output
    · have firstEraseMember := List.mem_of_mem_erase
        (List.mem_of_mem_erase (List.mem_of_mem_erase live))
      have preMember := List.mem_of_mem_erase firstEraseMember
      have candidateInPre : candidate ∈
          cSupportedSourceExecFacts (physicalNormalResultReference context) :=
        List.mem_filterMap.mpr ⟨atom, preMember, extracted⟩
      rw [physicalNormalResultReference_supported_exact context
        preReferenceMorkNodup] at candidateInPre
      have candidateExact : candidate =
          compressedAssertionRejoinDirective := by simpa using candidateInPre
      subst candidate
      have atomExact := extractSupportedSourceExecFact_atom extracted
      subst atom
      have preNodup : (physicalNormalResultReference context).Nodup :=
        List.Nodup.of_map morkSupportKey preReferenceMorkNodup
      exact False.elim
        (preNodup.not_mem_erase firstEraseMember)
    · simp only [RejoinContext.outputRows, List.mem_cons,
        List.not_mem_nil, or_false] at output
      rcases output with rfl | rfl | rfl | rfl | rfl
      · unfold RejoinContext.returnedMachineRow at extracted
        rw [extract_supported_none_of_expression_head_ne _ _ (by decide)]
          at extracted
        contradiction
      · unfold RejoinContext.resultNodeRow at extracted
        rw [extract_supported_none_of_expression_head_ne _ _ (by decide)]
          at extracted
        contradiction
      · unfold RejoinContext.resultStackRow at extracted
        rw [extract_supported_none_of_expression_head_ne _ _ (by decide)]
          at extracted
        contradiction
      · unfold RejoinContext.resumeRow at extracted
        rw [extract_supported_none_of_expression_head_ne _ _ (by decide)]
          at extracted
        contradiction
      · rw [extract_compressedAssertionResumeRule_exact] at extracted
        exact (Option.some.inj extracted).symm

theorem physicalAssertionRejoinResult_supported_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (resultReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    cSupportedSourceExecFacts (physicalAssertionRejoinResult context) =
      [compressedAssertionResumeDirective] := by
  have rowsPerm := physical_assertion_rejoin_perm_reference context
    inputMorkNodup preReferenceMorkNodup resultReferenceMorkNodup
  have supportedPerm := rowsPerm.filterMap extractSupportedSourceExecFact
  change (cSupportedSourceExecFacts (physicalAssertionRejoinResult context)).Perm
    (cSupportedSourceExecFacts (physicalAssertionRejoinReference context))
    at supportedPerm
  rw [physicalAssertionRejoinReference_supported_exact context
    preReferenceMorkNodup resultReferenceMorkNodup] at supportedPerm
  exact List.perm_singleton.mp supportedPerm

theorem physicalAssertionRejoin_selects_resume
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (resultReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    selectNextScheduled
        (cSupportedSourceExecFacts (physicalAssertionRejoinResult context)) =
      some compressedAssertionResumeDirective := by
  rw [physicalAssertionRejoinResult_supported_exact context inputMorkNodup
    preReferenceMorkNodup resultReferenceMorkNodup]
  rfl

theorem physicalAssertionRejoin_ruleScoped_resume_step
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (resultReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (physicalAssertionRejoinResult context) =
      some (physicalAssertionResumeResult context) := by
  unfold cRuleScopedSourceWorkQueueStep physicalAssertionResumeResult
  rw [physicalAssertionRejoin_selects_resume context inputMorkNodup
    preReferenceMorkNodup resultReferenceMorkNodup]

/-- Normal-result publication, assertion rejoin, and scanner resume form three
actual nonempty MORK transitions, each classified by the OSLF-generated native
target. -/
structure PhysicalAssertionResumeSegment
    (context : NormalResultContext) : Prop where
  inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context)
  preReferenceMorkNodup : MorkSupportNodup
    (physicalNormalResultReference context)
  rejoinReferenceMorkNodup : MorkSupportNodup
    (physicalAssertionRejoinReference context)
  exactPhysicalMatch : PhysicalExactCompressedAssertionResume
    context.rejoinContext (physicalAssertionRejoinResult context)
  concreteStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (physicalAssertionRejoinResult context) =
    some (physicalAssertionResumeResult context)
  concreteTrace : Nonempty (CRuleScopedTrace .leaveInert 1
    (physicalAssertionRejoinResult context)
    (physicalAssertionResumeResult context))
  nativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 1
    (physicalAssertionRejoinResult context)
    (physicalAssertionResumeResult context))
  wholeTrace : Nonempty (CRuleScopedTrace .leaveInert 3
    (normalToRejoinSlice context) (physicalAssertionResumeResult context))
  wholeNativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 3
    (normalToRejoinSlice context) (physicalAssertionResumeResult context))
  resultListNodup : (physicalAssertionResumeResult context).Nodup
  resultMorkNodup : MorkSupportNodup
    (physicalAssertionResumeResult context)

def physical_assertion_resume_segment
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (rejoinReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    PhysicalAssertionResumeSegment context := by
  have exactMatch := physical_assertion_rejoin_supplies_exact_resume context
    inputMorkNodup preReferenceMorkNodup rejoinReferenceMorkNodup
  have moved := physicalAssertionRejoin_ruleScoped_resume_step context
    inputMorkNodup preReferenceMorkNodup rejoinReferenceMorkNodup
  have first := normalToRejoinSlice_ruleScoped_steps context
  have second := physicalNormalResult_ruleScoped_rejoin_step context
    inputMorkNodup preReferenceMorkNodup
  let one : CRuleScopedTrace .leaveInert 1
      (physicalAssertionRejoinResult context)
      (physicalAssertionResumeResult context) := .step moved .refl
  let whole : CRuleScopedTrace .leaveInert 3
      (normalToRejoinSlice context) (physicalAssertionResumeResult context) :=
    .step first (.step second (.step moved .refl))
  have rejoinListNodup : (physicalAssertionRejoinResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (cFireRuleScopedSourceExecFact_list_nodup _ _
        (normalToRejoinSlice_nodup context))
  have rejoinMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _
      (cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup)
  exact
    { inputMorkNodup := inputMorkNodup
      preReferenceMorkNodup := preReferenceMorkNodup
      rejoinReferenceMorkNodup := rejoinReferenceMorkNodup
      exactPhysicalMatch := exactMatch
      concreteStep := moved
      concreteTrace := ⟨one⟩
      nativeTypeTrace := ⟨one.toNativeTypeTrace⟩
      wholeTrace := ⟨whole⟩
      wholeNativeTypeTrace := ⟨whole.toNativeTypeTrace⟩
      resultListNodup :=
        cFireRuleScopedSourceExecFact_list_nodup _ _ rejoinListNodup
      resultMorkNodup :=
        cFireRuleScopedSourceExecFact_mork_nodup _ _ rejoinMorkNodup }
#print axioms compressedAssertionResumeDirective_guards_exact
#print axioms physical_assertion_resume_matcher_mem_iff
#print axioms physical_exact_assertion_resume_for_of_reflective
#print axioms physical_exact_assertion_resume_of_reflective
#print axioms physical_exact_assertion_resume_for_of_live_rows
#print axioms physical_assertion_resume_fire_adds_output_support_for
#print axioms physical_assertion_resume_ruleScoped_step_from
#print axioms physical_assertion_resume_scheduled_segment_for
#print axioms physical_assertion_rejoin_supplies_exact_resume
#print axioms physicalAssertionRejoinReference_supported_exact
#print axioms physicalAssertionRejoinResult_supported_exact
#print axioms physicalAssertionRejoin_ruleScoped_resume_step
#print axioms physical_assertion_resume_segment

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionResume
