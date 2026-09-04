import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalResult
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness

/-!
# Physical compressed-assertion rejoin

The exact physical output of the shared normal verifier schedules and matches
the compressed rejoin directive under rule-scoped MORK execution.  Every
primitive transition is classified by the native target generated through
OSLF from that executable GSLT.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionRejoin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalResult
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

def physicalAssertionRejoinMatcherRows (space : List Atom) : List Subst :=
  let live := morkEraseSupport space compressedAssertionRejoinDirective.atom
  let read := morkInsertSupport live compressedAssertionRejoinDirective.atom
  ((cMatchInputSpecMork [] read
      compressedAssertionRejoinDirective.rule.input).filter fun
      (substitution, _) =>
        matchSourceGuards substitution
          compressedAssertionRejoinDirective.rule.guards).map Prod.fst

theorem compressedAssertionRejoinDirective_guards_exact :
    compressedAssertionRejoinDirective.rule.guards = [] := by
  decide +kernel

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

theorem physical_assertion_rejoin_live_eq
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space) :
    morkEraseSupport space compressedAssertionRejoinDirective.atom =
      space.erase compressedAssertionRejoinDirective.atom :=
  morkEraseSupport_eq_erase_of_mem space
    compressedAssertionRejoinDirective.atom listNodup morkNodup
      directivePresent

theorem physical_assertion_rejoin_read_perm
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space) :
    (morkInsertSupport
        (morkEraseSupport space compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.atom).Perm
      (compressedAssertionRejoinDirective.atom ::
        space.erase compressedAssertionRejoinDirective.atom) := by
  rw [physical_assertion_rejoin_live_eq listNodup morkNodup
    directivePresent]
  have absent : morkSupportContains
      (space.erase compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.atom = false := by
    rw [← physical_assertion_rejoin_live_eq listNodup morkNodup
      directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      compressedAssertionRejoinDirective.atom
  unfold morkInsertSupport
  rw [absent]
  exact List.perm_append_singleton compressedAssertionRejoinDirective.atom
    (space.erase compressedAssertionRejoinDirective.atom)

theorem physical_assertion_rejoin_matcher_mem_iff
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space compressedAssertionRejoinDirective.atom)
            compressedAssertionRejoinDirective.atom)
          compressedAssertionRejoinDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (compressedAssertionRejoinDirective.atom ::
            space.erase compressedAssertionRejoinDirective.atom)
          compressedAssertionRejoinDirective.rule.input := by
  rw [compressedAssertionRejoin_input_exact]
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  have readPerm := physical_assertion_rejoin_read_perm listNodup morkNodup
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

def PhysicalExactCompressedAssertionRejoin (context : RejoinContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalAssertionRejoinMatcherRows space,
    instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
          substitution rejoinReturnedMachineTemplate =
        some context.returnedMachineRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultNodeTemplate = some context.resultNodeRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultStackTemplate = some context.resultStackRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResumeTemplate = some context.resumeRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          (.var "compressed-assertion-resume-rule") =
        some compressedAssertionResumeRule

/-- Every physical matcher row presents the same source-indexed successor
interface.  This is stronger than existence of one exact match and is the
right premise for no-invention properties of a complete sink batch. -/
def PhysicalAssertionRejoinMatcherInterfaceExact (context : RejoinContext)
    (space : List Atom) : Prop :=
  ∀ substitution ∈ physicalAssertionRejoinMatcherRows space,
    instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
          substitution rejoinReturnedMachineTemplate =
        some context.returnedMachineRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultNodeTemplate = some context.resultNodeRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultStackTemplate = some context.resultStackRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResumeTemplate = some context.resumeRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          (.var "compressed-assertion-resume-rule") =
        some compressedAssertionResumeRule

theorem physical_exact_assertion_rejoin_of_reflective
    (context : RejoinContext) {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    (matched : ExactCompressedAssertionRejoin context space) :
    PhysicalExactCompressedAssertionRejoin context space := by
  rcases matched with
    ⟨substitution, rowMember, machine, node, stack, resume, resumeRule⟩
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, reflected, equal⟩ := rowMember
  have reflected' : (substitution, consumed) ∈
      Conformance.Computable.cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.rule.input := by
    cases equal
    exact reflected
  have physicalMatch :=
    (physical_assertion_rejoin_matcher_mem_iff listNodup morkNodup
      directivePresent substitution consumed).2 reflected'
  have physicalRow : substitution ∈
      physicalAssertionRejoinMatcherRows space := by
    unfold physicalAssertionRejoinMatcherRows
    rw [List.mem_map]
    refine ⟨(substitution, consumed), ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨physicalMatch, ?_⟩
    rw [compressedAssertionRejoinDirective_guards_exact]
    rfl
  exact ⟨substitution, physicalRow,
    instantiateRuleTemplateAtom?_of_reflective _ machine,
    instantiateRuleTemplateAtom?_of_reflective _ node,
    instantiateRuleTemplateAtom?_of_reflective _ stack,
    instantiateRuleTemplateAtom?_of_reflective _ resume,
    instantiateRuleTemplateAtom?_of_reflective _ resumeRule⟩

/-- Every substitution selected by the physical matcher retains the exact
carrier, intermediate substitution, extension, and replay witness for any
designated authored premise. -/
theorem physical_assertion_rejoin_factor_origin
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    {substitution : Subst} (factor : Atom)
    (factorMember : factor ∈ rejoinPatterns)
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows space) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom ∧
        Conformance.Computable.cmatchAtom beforeFactor factor carrier =
          some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution factor = carrier := by
  unfold physicalAssertionRejoinMatcherRows at matcherMember
  rw [List.mem_map] at matcherMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ :=
    matcherMember
  simp only at equal
  subst matchedSubstitution
  rw [List.mem_filter] at filtered
  have ordinaryPair :=
    (physical_assertion_rejoin_matcher_mem_iff listNodup morkNodup
      directivePresent substitution consumed).1 filtered.1
  have ordinaryMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom)
        (.compat (mkPattern rejoinPatterns))).map Prod.fst := by
    rw [List.mem_map]
    exact ⟨(substitution, consumed), ordinaryPair, rfl⟩
  exact Conformance.Computable.cmatchInputSpec_compat_factor_match_origin
    (compressedAssertionRejoinDirective.atom ::
      space.erase compressedAssertionRejoinDirective.atom)
    (mkPattern rejoinPatterns) factor
    (by simpa [mkPattern] using factorMember) ordinaryMember

/-- A non-executable fixed-head rejoin premise cannot obtain its carrier from
the selected executable directive.  Its replay witness therefore originates
in the physical pre-state itself. -/
theorem physical_assertion_rejoin_fixed_head_origin
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    {substitution : Subst} (head : String) (tail : List Atom)
    (headNe : head ≠ "exec")
    (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
      rejoinPatterns)
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows space) :
    ∃ carrier ∈ space,
      applySubst substitution
        (.expression (.symbol head :: tail)) = carrier := by
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, matched,
      _extension, replay⟩ :=
    physical_assertion_rejoin_factor_origin listNodup morkNodup
      directivePresent (.expression (.symbol head :: tail)) factorMember
      matcherMember
  rcases List.mem_cons.mp carrierMember with selected | prior
  · rw [selected] at matched
    change Conformance.Computable.cmatchAtom beforeFactor
      (.expression (.symbol head :: tail))
        compressedAssertionRejoinRule = some afterFactor at matched
    unfold compressedAssertionRejoinRule at matched
    rw [Conformance.Computable.cmatchAtom_expression_symbol_head_ne
      beforeFactor head "exec" tail _ headNe] at matched
    contradiction
  · exact ⟨carrier, List.mem_of_mem_erase prior, replay⟩

/-- At the connected physical normal-result successor, every fixed-head
rejoin premise replays a carrier from the canonical physical reference. -/
theorem physical_normal_result_rejoin_fixed_head_origin
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst} (head : String) (tail : List Atom)
    (headNe : head ≠ "exec")
    (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
      rejoinPatterns)
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    ∃ carrier ∈ physicalNormalResultReference context,
      applySubst substitution
        (.expression (.symbol head :: tail)) = carrier := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    physical_assertion_rejoin_fixed_head_origin
      (cFireRuleScopedSourceExecFact_list_nodup _ _
        (normalToRejoinSlice_nodup context))
      (cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup)
      (by
        have perm := physical_normal_result_perm_reference context
          inputMorkNodup referenceMorkNodup
        apply perm.mem_iff.mpr
        simp [physicalNormalResultReference,
          compressedAssertionRejoinDirective])
      head tail headNe factorMember matcherMember
  exact ⟨carrier,
    physical_normal_result_rows_within_reference context inputMorkNodup
      carrier carrierMember,
    replay⟩

private theorem applySubst_expression_symbol_head_ne
    (substitution : Subst) (head otherHead : String)
    (tail otherTail : List Atom) (different : head ≠ otherHead) :
    applySubst substitution (.expression (.symbol head :: tail)) ≠
      .expression (.symbol otherHead :: otherTail) := by
  simp [applySubst, applySubst.applySubstList, different]

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

/-- Exhaustive row provenance for the canonical physical normal-result
successor.  The consumed normal-result directive and body row are absent;
every remaining row is either a retained authored input or one of the four
exact normal-result outputs. -/
private theorem physicalNormalResultReference_cases
    (context : NormalResultContext) {row : Atom}
    (member : row ∈ physicalNormalResultReference context) :
    row = context.rejoinCaptureRow ∨
      row = context.rejoinContext.contextRow ∨
      row = context.rejoinContext.normalStackSuccessorRow ∨
      row = context.rejoinContext.nodeSuccessorRow ∨
      row = context.rejoinContext.normalLabelRow ∨
      row = context.rejoinContext.resumeCaptureRow ∨
      row ∈ compressedScannerRuleCaptureRows ∨
      row = context.rejoinContext.returnedControlRow ∨
      row = context.rejoinContext.returnedStackRow ∨
      row = normalAssertionReloadAtom context.proofOwner ∨
      row = compressedAssertionRejoinRule := by
  simp only [physicalNormalResultReference, List.mem_append] at member
  rcases member with live | output
  · have afterBody := List.mem_of_mem_erase live
    have notBody : row ≠ context.bodyBuiltRow := by
      intro equal
      subst row
      exact ((normalToRejoinSlice_nodup context).erase
        normalResultDirective.atom).not_mem_erase live
    have notDirective : row ≠ normalResultDirective.atom := by
      intro equal
      subst row
      exact (normalToRejoinSlice_nodup context).not_mem_erase afterBody
    have original := List.mem_of_mem_erase afterBody
    change row ∈ normalResultDirective.atom ::
      ([context.bodyBuiltRow, context.rejoinCaptureRow,
        context.rejoinContext.contextRow,
        context.rejoinContext.normalStackSuccessorRow,
        context.rejoinContext.nodeSuccessorRow,
        context.rejoinContext.normalLabelRow,
        context.rejoinContext.resumeCaptureRow] ++
          compressedScannerRuleCaptureRows) at original
    rw [List.mem_cons] at original
    rcases original with directive | original
    · exact False.elim (notDirective directive)
    rw [List.mem_append] at original
    rcases original with fixed | scanner
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with body | capture | contextRow | normalSuccessor |
        nodeSuccessor | normalLabel | resumeCapture
      · exact False.elim (notBody body)
      · exact Or.inl capture
      · exact Or.inr (Or.inl contextRow)
      · exact Or.inr (Or.inr (Or.inl normalSuccessor))
      · exact Or.inr (Or.inr (Or.inr (Or.inl nodeSuccessor)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl normalLabel))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl resumeCapture)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl scanner))))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at output
    rcases output with rfl | rfl | rfl | rfl <;> simp

private theorem physical_normal_result_rejoin_fixed_head_exact_of_unique
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst} (head : String) (tail : List Atom)
    (headNe : head ≠ "exec")
    (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
      rejoinPatterns)
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context))
    (expected : Atom)
    (unique : ∀ carrier ∈ physicalNormalResultReference context,
      compressedDynamicRowHead? carrier = some head → carrier = expected) :
    applySubst substitution (.expression (.symbol head :: tail)) =
      expected := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    physical_normal_result_rejoin_fixed_head_origin context inputMorkNodup
      referenceMorkNodup head tail headNe factorMember matcherMember
  have carrierHead : compressedDynamicRowHead? carrier = some head := by
    rw [← replay]
    simp [applySubst, applySubst.applySubstList, compressedDynamicRowHead?]
  exact replay.trans (unique carrier carrierMember carrierHead)

private theorem physicalNormalResultReference_fixed_head_unique
    (context : NormalResultContext) {carrier : Atom}
    (member : carrier ∈ physicalNormalResultReference context) :
    (compressedDynamicRowHead? carrier = some "mm-normal-control" →
      carrier = context.rejoinContext.returnedControlRow) ∧
    (compressedDynamicRowHead? carrier = some "mm-stack-cell" →
      carrier = context.rejoinContext.returnedStackRow) ∧
    (compressedDynamicRowHead? carrier = some "mm-index-successor" →
      carrier = context.rejoinContext.normalStackSuccessorRow) ∧
    (compressedDynamicRowHead? carrier =
        some "mm-compressed-index-successor" →
      carrier = context.rejoinContext.nodeSuccessorRow) ∧
    (compressedDynamicRowHead? carrier = some "mm-linked-row" →
      carrier = context.rejoinContext.normalLabelRow) := by
  rcases physicalNormalResultReference_cases context member with
    rfl | rfl | rfl | rfl | rfl | rfl | scanner | rfl | rfl | rfl | rfl
  all_goals try
    simp [compressedDynamicRowHead?, NormalResultContext.rejoinCaptureRow,
      RejoinContext.contextRow, RejoinContext.normalStackSuccessorRow,
      RejoinContext.nodeSuccessorRow, RejoinContext.normalLabelRow,
      RejoinContext.resumeCaptureRow, RejoinContext.returnedControlRow,
      RejoinContext.returnedStackRow, normalAssertionReloadAtom,
      compressedAssertionRejoinRule, compressedOwnedRuntimeRuleRow,
      compressedIndexSuccessorRow]
  obtain ⟨tail, rfl⟩ := scannerCapture_shape scanner
  simp

private theorem physicalNormalResultReference_unique_context
    (context : NormalResultContext) {carrier : Atom}
    (member : carrier ∈ physicalNormalResultReference context)
    (head : compressedDynamicRowHead? carrier =
      some "mm-compressed-assertion-context") :
    carrier = context.rejoinContext.contextRow := by
  rcases physicalNormalResultReference_cases context member with
    rfl | rfl | rfl | rfl | rfl | rfl | scanner | rfl | rfl | rfl | rfl
  all_goals try
    simp [compressedDynamicRowHead?, NormalResultContext.rejoinCaptureRow,
      RejoinContext.contextRow, RejoinContext.normalStackSuccessorRow,
      RejoinContext.nodeSuccessorRow, RejoinContext.normalLabelRow,
      RejoinContext.resumeCaptureRow, RejoinContext.returnedControlRow,
      RejoinContext.returnedStackRow, normalAssertionReloadAtom,
      compressedAssertionRejoinRule, compressedOwnedRuntimeRuleRow,
      compressedIndexSuccessorRow] at head ⊢
  obtain ⟨tail, rfl⟩ := scannerCapture_shape scanner
  simp at head

/-- Every physical rejoin matcher row replays the exact source-indexed
assertion context.  Fixed-head discrimination reconstructs the row from the
canonical physical reference rather than accepting it as a witness. -/
theorem physical_normal_result_rejoin_context_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinContextTemplate =
      context.rejoinContext.contextRow := by
  exact physical_normal_result_rejoin_fixed_head_exact_of_unique context
    inputMorkNodup referenceMorkNodup "mm-compressed-assertion-context"
      [.var "scope-owner", .var "proof-owner", .var "word-position",
       .var "remaining-bytes", rejoinPCTemplate, rejoinNextPCTemplate,
       .var "assertion-label", .var "heap-next", .var "node-next"]
      (by decide) (by simp [rejoinPatterns, rejoinContextTemplate])
      matcherMember context.rejoinContext.contextRow
      (fun carrier member head =>
        physicalNormalResultReference_unique_context context member head)

/-- Every physical rejoin matcher row replays the exact returned normal
control produced by the preceding normal-result transition. -/
theorem physical_normal_result_rejoin_returned_control_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinReturnedControlTemplate =
      context.rejoinContext.returnedControlRow := by
  exact physical_normal_result_rejoin_fixed_head_exact_of_unique context
    inputMorkNodup referenceMorkNodup "mm-normal-control"
      [.var "scope-owner", .var "proof-owner", rejoinNextPCTemplate,
       .var "next-stack-position"]
      (by decide)
      (by simp [rejoinPatterns, rejoinReturnedControlTemplate])
      matcherMember context.rejoinContext.returnedControlRow
      (fun carrier member head =>
        (physicalNormalResultReference_fixed_head_unique context member).1 head)

/-- Every physical rejoin matcher row replays the exact returned assertion
stack cell produced by the preceding normal-result transition. -/
theorem physical_normal_result_rejoin_returned_stack_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinReturnedStackTemplate =
      context.rejoinContext.returnedStackRow := by
  exact physical_normal_result_rejoin_fixed_head_exact_of_unique context
    inputMorkNodup referenceMorkNodup "mm-stack-cell"
      [.var "proof-owner", .var "stack-base", .var "result-formula",
       rejoinOccurrenceTemplate]
      (by decide)
      (by simp [rejoinPatterns, rejoinReturnedStackTemplate])
      matcherMember context.rejoinContext.returnedStackRow
      (fun carrier member head =>
        (physicalNormalResultReference_fixed_head_unique context member).2.1 head)

/-- Every physical rejoin matcher row replays the exact normal-stack
successor row retained across the normal-result transition. -/
theorem physical_normal_result_rejoin_normal_stack_successor_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinNormalStackSuccessorTemplate =
      context.rejoinContext.normalStackSuccessorRow := by
  exact physical_normal_result_rejoin_fixed_head_exact_of_unique context
    inputMorkNodup referenceMorkNodup "mm-index-successor"
      [.var "proof-owner", .var "stack-base", .var "next-stack-position"]
      (by decide)
      (by simp [rejoinPatterns, rejoinNormalStackSuccessorTemplate])
      matcherMember context.rejoinContext.normalStackSuccessorRow
      (fun carrier member head =>
        (physicalNormalResultReference_fixed_head_unique context member).2.2.1 head)

/-- Every physical rejoin matcher row replays the exact compressed-node
successor row retained across the normal-result transition. -/
theorem physical_normal_result_rejoin_node_successor_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinNodeSuccessorTemplate =
      context.rejoinContext.nodeSuccessorRow := by
  exact physical_normal_result_rejoin_fixed_head_exact_of_unique context
    inputMorkNodup referenceMorkNodup "mm-compressed-index-successor"
      [.expression [.symbol "mm-compressed-node-owner", .var "proof-owner"],
       .var "node-next", .var "next-node"]
      (by decide)
      (by simp [rejoinPatterns, rejoinNodeSuccessorTemplate])
      matcherMember context.rejoinContext.nodeSuccessorRow
      (fun carrier member head =>
        (physicalNormalResultReference_fixed_head_unique context member).2.2.2.1 head)

/-- Every physical rejoin matcher row replays the exact source-ordered normal
proof label row retained across the normal-result transition. -/
theorem physical_normal_result_rejoin_normal_label_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinNormalLabelTemplate =
      context.rejoinContext.normalLabelRow := by
  exact physical_normal_result_rejoin_fixed_head_exact_of_unique context
    inputMorkNodup referenceMorkNodup "mm-linked-row"
      [MM2DataEncoding.stringAtom "normal-proof-label", .var "proof-owner",
       rejoinPCTemplate,
       rejoinNextPCTemplate, .var "assertion-label"]
      (by decide)
      (by simp [rejoinPatterns, rejoinNormalLabelTemplate])
      matcherMember context.rejoinContext.normalLabelRow
      (fun carrier member head =>
        (physicalNormalResultReference_fixed_head_unique context member).2.2.2.2 head)

private theorem physicalNormalResultReference_resume_capabilities
    (context : NormalResultContext) :
    AssertionResumeCapabilities compressedAssertionResumeRule
      (physicalNormalResultReference context) := by
  intro carrier member payload captured
  rcases physicalNormalResultReference_cases context member with
    rfl | rfl | rfl | rfl | rfl | rfl | scanner | rfl | rfl | rfl | rfl
  · simp [AssertionResumeCapture, NormalResultContext.rejoinCaptureRow,
      compressedOwnedRuntimeRuleRow, decodeCompressedExecutableCapture]
      at captured
  · simp [AssertionResumeCapture, RejoinContext.contextRow,
      decodeCompressedExecutableCapture] at captured
  · simp [AssertionResumeCapture, RejoinContext.normalStackSuccessorRow,
      decodeCompressedExecutableCapture] at captured
  · simp [AssertionResumeCapture, RejoinContext.nodeSuccessorRow,
      compressedIndexSuccessorRow, decodeCompressedExecutableCapture]
      at captured
  · simp [AssertionResumeCapture, RejoinContext.normalLabelRow,
      decodeCompressedExecutableCapture] at captured
  · have equal := Option.some.inj captured
    exact (congrArg CompressedExecutableCapture.payload equal).symm
  · simp only [compressedScannerRuleCaptureRows, List.mem_cons,
      List.not_mem_nil, or_false] at scanner
    rcases scanner with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;>
      simp [AssertionResumeCapture, compressedOwnedRuntimeRuleRow,
        decodeCompressedExecutableCapture] at captured
  · simp [AssertionResumeCapture, RejoinContext.returnedControlRow,
      decodeCompressedExecutableCapture] at captured
  · simp [AssertionResumeCapture, RejoinContext.returnedStackRow,
      decodeCompressedExecutableCapture] at captured
  · simp [AssertionResumeCapture, normalAssertionReloadAtom,
      decodeCompressedExecutableCapture] at captured
  · simp [AssertionResumeCapture, compressedAssertionRejoinRule,
      decodeCompressedExecutableCapture] at captured

/-- The shared runtime-rule constructor cannot let a scanner rule masquerade
as the assertion-resume capability.  Every physical rejoin matcher therefore
replays the exact source-authored resume rule. -/
theorem physical_normal_result_rejoin_resume_capture_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    applySubst substitution rejoinResumeCaptureTemplate =
      context.rejoinContext.resumeCaptureRow := by
  obtain ⟨carrier, carrierMember, replay⟩ :=
    physical_normal_result_rejoin_fixed_head_origin context inputMorkNodup
      referenceMorkNodup "mm-compressed-owned-runtime-rule"
      [.symbol "assertion-resume", .var "compressed-assertion-resume-rule"]
      (by decide) (by simp [rejoinPatterns, rejoinResumeCaptureTemplate])
      matcherMember
  have captured : AssertionResumeCapture carrier
      (applySubst substitution (.var "compressed-assertion-resume-rule")) := by
    rw [← replay]
    rfl
  have payloadExact :=
    physicalNormalResultReference_resume_capabilities context carrier
      carrierMember
      (applySubst substitution (.var "compressed-assertion-resume-rule"))
      captured
  unfold rejoinResumeCaptureTemplate RejoinContext.resumeCaptureRow
  unfold compressedOwnedRuntimeRuleRow
  simp only [applySubst, applySubst.applySubstList]
  simpa only [applySubst] using congrArg
    (fun payload => Atom.expression
      [Atom.symbol "mm-compressed-owned-runtime-rule",
       Atom.symbol "assertion-resume", payload]) payloadExact

theorem rejoin_output_applySubst_exact_of_inputs
    (context : RejoinContext) (substitution : Subst)
    (contextExact : applySubst substitution rejoinContextTemplate =
      context.contextRow)
    (controlExact : applySubst substitution rejoinReturnedControlTemplate =
      context.returnedControlRow)
    (stackExact : applySubst substitution rejoinReturnedStackTemplate =
      context.returnedStackRow)
    (nodeSuccessorExact : applySubst substitution rejoinNodeSuccessorTemplate =
      context.nodeSuccessorRow)
    (resumeCaptureExact : applySubst substitution rejoinResumeCaptureTemplate =
      context.resumeCaptureRow) :
    applySubst substitution rejoinReturnedMachineTemplate =
        context.returnedMachineRow ∧
      applySubst substitution rejoinResultNodeTemplate =
        context.resultNodeRow ∧
      applySubst substitution rejoinResultStackTemplate =
        context.resultStackRow ∧
      applySubst substitution rejoinResumeTemplate = context.resumeRow ∧
      applySubst substitution (.var "compressed-assertion-resume-rule") =
        compressedAssertionResumeRule := by
  cases context
  simp_all [rejoinContextTemplate, rejoinReturnedControlTemplate,
    rejoinReturnedStackTemplate, rejoinNodeSuccessorTemplate,
    rejoinResumeCaptureTemplate, rejoinReturnedMachineTemplate,
    rejoinResultNodeTemplate, rejoinResultStackTemplate,
    rejoinResumeTemplate, rejoinOccurrenceTemplate, rejoinPCTemplate,
    rejoinNextPCTemplate, RejoinContext.contextRow,
    RejoinContext.returnedControlRow, RejoinContext.returnedStackRow,
    RejoinContext.nodeSuccessorRow, RejoinContext.resumeCaptureRow,
    RejoinContext.returnedMachineRow, RejoinContext.resultNodeRow,
    RejoinContext.resultStackRow, RejoinContext.resumeRow,
    RejoinContext.occurrence, RejoinContext.pc, RejoinContext.nextPC,
    RejoinContext.bytes, RejoinContext.code, compressedIndexSuccessorRow,
    compressedOwnedRuntimeRuleRow, compressedAssertionOccurrenceSurface,
    applySubst, applySubst.applySubstList]

theorem physical_assertion_rejoin_factor_covered
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    {substitution : Subst} (factor : Atom)
    (factorMember : factor ∈ rejoinPatterns)
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows space) :
    templateCovered substitution factor = true := by
  obtain ⟨beforeFactor, afterFactor, carrier, _carrierMember, matched,
      lookupExtension, _replay⟩ :=
    physical_assertion_rejoin_factor_origin listNodup morkNodup
      directivePresent factor factorMember matcherMember
  exact Conformance.Computable.templateCovered_of_lookupExtends
    lookupExtension factor
    (Conformance.Computable.cmatchAtom_templateCovered beforeFactor factor
      carrier afterFactor matched)

private theorem physical_normal_result_rejoin_factor_covered
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst} (factor : Atom)
    (factorMember : factor ∈ rejoinPatterns)
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    templateCovered substitution factor = true := by
  have resultListNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have resultMorkNodup : MorkSupportNodup (physicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have directivePresent : compressedAssertionRejoinDirective.atom ∈
      physicalNormalResult context := by
    have perm := physical_normal_result_perm_reference context inputMorkNodup
      referenceMorkNodup
    apply perm.mem_iff.mpr
    simp [physicalNormalResultReference, compressedAssertionRejoinDirective]
  exact physical_assertion_rejoin_factor_covered resultListNodup
    resultMorkNodup directivePresent factor factorMember matcherMember

/-- Every substitution selected by the physical rejoin matcher produces the
same complete compact successor interface.  This excludes alternate physical
matches that consume valid-looking rows but publish a different node, stack,
resume cursor, or executable continuation. -/
theorem physical_normal_result_rejoin_matcher_interface_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
          substitution rejoinReturnedMachineTemplate =
        some context.rejoinContext.returnedMachineRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultNodeTemplate = some context.rejoinContext.resultNodeRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultStackTemplate =
        some context.rejoinContext.resultStackRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResumeTemplate = some context.rejoinContext.resumeRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          (.var "compressed-assertion-resume-rule") =
        some compressedAssertionResumeRule := by
  have contextExact := physical_normal_result_rejoin_context_exact context
    inputMorkNodup referenceMorkNodup matcherMember
  have controlExact :=
    physical_normal_result_rejoin_returned_control_exact context
      inputMorkNodup referenceMorkNodup matcherMember
  have stackExact := physical_normal_result_rejoin_returned_stack_exact context
    inputMorkNodup referenceMorkNodup matcherMember
  have nodeSuccessorExact :=
    physical_normal_result_rejoin_node_successor_exact context inputMorkNodup
      referenceMorkNodup matcherMember
  have resumeCaptureExact :=
    physical_normal_result_rejoin_resume_capture_exact context inputMorkNodup
      referenceMorkNodup matcherMember
  have applied := rejoin_output_applySubst_exact_of_inputs
    context.rejoinContext substitution contextExact controlExact stackExact
      nodeSuccessorExact resumeCaptureExact
  have contextCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinContextTemplate
      (by simp [rejoinPatterns]) matcherMember
  have controlCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinReturnedControlTemplate
      (by simp [rejoinPatterns]) matcherMember
  have stackCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinReturnedStackTemplate
      (by simp [rejoinPatterns]) matcherMember
  have nodeCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinNodeSuccessorTemplate
      (by simp [rejoinPatterns]) matcherMember
  have resumeCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinResumeCaptureTemplate
      (by simp [rejoinPatterns]) matcherMember
  have outputCovered :
      templateCovered substitution rejoinReturnedMachineTemplate = true ∧
      templateCovered substitution rejoinResultNodeTemplate = true ∧
      templateCovered substitution rejoinResultStackTemplate = true ∧
      templateCovered substitution rejoinResumeTemplate = true ∧
      templateCovered substitution
        (.var "compressed-assertion-resume-rule") = true := by
    simp_all [templateCovered, templatesCovered, rejoinContextTemplate,
      rejoinReturnedControlTemplate, rejoinReturnedStackTemplate,
      rejoinNodeSuccessorTemplate, rejoinResumeCaptureTemplate,
      rejoinReturnedMachineTemplate, rejoinResultNodeTemplate,
      rejoinResultStackTemplate, rejoinResumeTemplate,
      rejoinOccurrenceTemplate, rejoinPCTemplate, rejoinNextPCTemplate,
      compressedAssertionOccurrenceSurface]
  have reflective :
      instantiateTemplateAtom? substitution rejoinReturnedMachineTemplate =
          some context.rejoinContext.returnedMachineRow ∧
        instantiateTemplateAtom? substitution rejoinResultNodeTemplate =
          some context.rejoinContext.resultNodeRow ∧
        instantiateTemplateAtom? substitution rejoinResultStackTemplate =
          some context.rejoinContext.resultStackRow ∧
        instantiateTemplateAtom? substitution rejoinResumeTemplate =
          some context.rejoinContext.resumeRow ∧
        instantiateTemplateAtom? substitution
          (.var "compressed-assertion-resume-rule") =
          some compressedAssertionResumeRule := by
    simp [instantiateTemplateAtom?, outputCovered.1, outputCovered.2.1,
      outputCovered.2.2.1, outputCovered.2.2.2.1,
      outputCovered.2.2.2.2, applied]
  exact ⟨instantiateRuleTemplateAtom?_of_reflective _ reflective.1,
    instantiateRuleTemplateAtom?_of_reflective _ reflective.2.1,
    instantiateRuleTemplateAtom?_of_reflective _ reflective.2.2.1,
    instantiateRuleTemplateAtom?_of_reflective _ reflective.2.2.2.1,
    instantiateRuleTemplateAtom?_of_reflective _ reflective.2.2.2.2⟩

/-- Every physical matcher row also identifies the three exact carriers
consumed by the rejoin transaction. -/
theorem physical_normal_result_rejoin_remove_interface_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    {substitution : Subst}
    (matcherMember : substitution ∈
      physicalAssertionRejoinMatcherRows (physicalNormalResult context)) :
    instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
          substitution rejoinContextTemplate =
        some context.rejoinContext.contextRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinReturnedControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinNormalLabelTemplate =
        some context.rejoinContext.normalLabelRow := by
  have contextExact := physical_normal_result_rejoin_context_exact context
    inputMorkNodup referenceMorkNodup matcherMember
  have controlExact :=
    physical_normal_result_rejoin_returned_control_exact context
      inputMorkNodup referenceMorkNodup matcherMember
  have labelExact := physical_normal_result_rejoin_normal_label_exact context
    inputMorkNodup referenceMorkNodup matcherMember
  have contextCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinContextTemplate
      (by simp [rejoinPatterns]) matcherMember
  have controlCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinReturnedControlTemplate
      (by simp [rejoinPatterns]) matcherMember
  have labelCovered := physical_normal_result_rejoin_factor_covered context
    inputMorkNodup referenceMorkNodup rejoinNormalLabelTemplate
      (by simp [rejoinPatterns]) matcherMember
  have contextReflective : instantiateTemplateAtom? substitution
      rejoinContextTemplate = some context.rejoinContext.contextRow := by
    simp [instantiateTemplateAtom?, contextCovered, contextExact]
  have controlReflective : instantiateTemplateAtom? substitution
      rejoinReturnedControlTemplate =
        some context.rejoinContext.returnedControlRow := by
    simp [instantiateTemplateAtom?, controlCovered, controlExact]
  have labelReflective : instantiateTemplateAtom? substitution
      rejoinNormalLabelTemplate = some context.rejoinContext.normalLabelRow := by
    simp [instantiateTemplateAtom?, labelCovered, labelExact]
  exact ⟨instantiateRuleTemplateAtom?_of_reflective _ contextReflective,
    instantiateRuleTemplateAtom?_of_reflective _ controlReflective,
    instantiateRuleTemplateAtom?_of_reflective _ labelReflective⟩

theorem compressedAssertionRejoinDirective_supportSet :
    ReflectiveSupportSetTemplate
      compressedAssertionRejoinDirective.rule.tmpl := by
  intro sink member
  rw [compressedAssertionRejoin_sinks_exact] at member
  simp only [rejoinSinks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    trivial

private theorem rejoinSinks_machine_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate] ++
      .add rejoinReturnedMachineTemplate ::
        [.add rejoinResultNodeTemplate, .add rejoinResultStackTemplate,
         .add rejoinResumeTemplate,
         .add (.var "compressed-assertion-resume-rule")] := by
  rfl

private theorem rejoinSinks_node_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate] ++
      .add rejoinResultNodeTemplate ::
        [.add rejoinResultStackTemplate, .add rejoinResumeTemplate,
         .add (.var "compressed-assertion-resume-rule")] := by
  rfl

private theorem rejoinSinks_stack_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate,
       .add rejoinResultNodeTemplate] ++
      .add rejoinResultStackTemplate ::
        [.add rejoinResumeTemplate,
         .add (.var "compressed-assertion-resume-rule")] := by
  rfl

private theorem rejoinSinks_resume_split :
    rejoinSinks =
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate,
       .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate] ++
      .add rejoinResumeTemplate ::
        [.add (.var "compressed-assertion-resume-rule")] := by
  rfl

/-- The actual rule-scoped rejoin firing contains the compact support keys of
all five source-indexed successor products.  This is a physical receipt; atom
equality is deliberately left to the separate matcher-inversion boundary. -/
theorem physical_assertion_rejoin_support_present
    (context : RejoinContext) (space : List Atom)
    (matched : PhysicalExactCompressedAssertionRejoin context space) :
    let result := cFireRuleScopedSourceExecFact space
      compressedAssertionRejoinDirective
    morkSupportContains result context.returnedMachineRow = true ∧
      morkSupportContains result context.resultNodeRow = true ∧
      morkSupportContains result context.resultStackRow = true ∧
      morkSupportContains result context.resumeRow = true ∧
      morkSupportContains result compressedAssertionResumeRule = true := by
  dsimp only
  rcases matched with
    ⟨substitution, rowMember, machine, node, stack, resume, resumeRule⟩
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change
    let live := morkEraseSupport space
      compressedAssertionRejoinDirective.atom
    cApplyRuleScopedSinkBatch compressedAssertionRejoinDirective.rule.input
        (physicalAssertionRejoinMatcherRows space) live
          compressedAssertionRejoinDirective.rule.tmpl.sinks |> fun result =>
      morkSupportContains result context.returnedMachineRow = true ∧
        morkSupportContains result context.resultNodeRow = true ∧
        morkSupportContains result context.resultStackRow = true ∧
        morkSupportContains result context.resumeRow = true ∧
        morkSupportContains result compressedAssertionResumeRule = true
  dsimp only
  rw [compressedAssertionRejoin_sinks_exact]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rejoinSinks_machine_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember machine (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl | rfl <;>
          exact Or.inl ⟨_, rfl⟩)
  · rw [rejoinSinks_node_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember node (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl <;>
          exact Or.inl ⟨_, rfl⟩)
  · rw [rejoinSinks_stack_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember stack (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩)
  · rw [rejoinSinks_resume_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember resume (by
        intro sink sinkMember
        simp only [List.mem_singleton] at sinkMember
        subst sink
        exact Or.inl ⟨_, rfl⟩)
  · exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _
      [.remove rejoinContextTemplate,
       .remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate,
       .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate,
       .add rejoinResumeTemplate]
      (.var "compressed-assertion-resume-rule")
      compressedAssertionResumeRule [] substitution rowMember resumeRule (by
        intro sink sinkMember
        simp at sinkMember)

/-- Erasing the uniquely admitted rejoin directive leaves no supported
executable fact.  The theorem is presentation-independent and uses physical
MORK erasure only through its exact-list characterization. -/
theorem physical_assertion_rejoin_live_supported_only_of_exact
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    {next : SourceExecFact}
    (supportedExact : cSupportedSourceExecFacts space =
      [compressedAssertionRejoinDirective]) :
    AtomsWithin
      (fun atom => ∀ candidate,
        extractSupportedSourceExecFact atom = some candidate →
          candidate = next)
      (morkEraseSupport space compressedAssertionRejoinDirective.atom) := by
  rw [physical_assertion_rejoin_live_eq listNodup morkNodup
    directivePresent]
  have erasedNone : cSupportedSourceExecFacts
      (space.erase compressedAssertionRejoinDirective.atom) = [] := by
    calc
      cSupportedSourceExecFacts
            (space.erase compressedAssertionRejoinDirective.atom) =
          (cSupportedSourceExecFacts space).erase
            compressedAssertionRejoinDirective :=
        cSupportedSourceExecFacts_erase _ compressedAssertionRejoinDirective
          extract_compressedAssertionRejoinRule_exact
      _ = [compressedAssertionRejoinDirective].erase
            compressedAssertionRejoinDirective :=
        congrArg (fun facts => facts.erase compressedAssertionRejoinDirective)
          supportedExact
      _ = [] := by rw [List.erase_cons_head]
  intro atom member candidate extracted
  have candidateMember : candidate ∈ cSupportedSourceExecFacts
      (space.erase compressedAssertionRejoinDirective.atom) :=
    List.mem_filterMap.mpr ⟨atom, member, extracted⟩
  rw [erasedNone] at candidateMember
  contradiction

/-- The exact all-matchers interface transports any atom-local invariant from
the five canonical rejoin outputs to every atom that an add sink can stage. -/
theorem physical_assertion_rejoin_additions_within_of_interface
    {context : RejoinContext} {space : List Atom} {property : Atom → Prop}
    (outputWithin : AtomsWithin property context.outputRows)
    (interfaceExact :
      PhysicalAssertionRejoinMatcherInterfaceExact context space) :
    RuleScopedTemplateAdditionsWithin property
      compressedAssertionRejoinDirective.rule.input
      (physicalAssertionRejoinMatcherRows space)
      compressedAssertionRejoinDirective.rule.tmpl := by
  intro sink sinkMember
  rw [compressedAssertionRejoin_sinks_exact] at sinkMember
  simp only [rejoinSinks, List.mem_cons, List.not_mem_nil, or_false]
    at sinkMember
  rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · intro substitution substitutionMember atom instantiated
    have exact := interfaceExact substitution substitutionMember
    have atomExact := Option.some.inj (instantiated.symm.trans exact.1)
    subst atom
    exact outputWithin _ (by simp [RejoinContext.outputRows])
  · intro substitution substitutionMember atom instantiated
    have exact := interfaceExact substitution substitutionMember
    have atomExact := Option.some.inj (instantiated.symm.trans exact.2.1)
    subst atom
    exact outputWithin _ (by simp [RejoinContext.outputRows])
  · intro substitution substitutionMember atom instantiated
    have exact := interfaceExact substitution substitutionMember
    have atomExact := Option.some.inj (instantiated.symm.trans exact.2.2.1)
    subst atom
    exact outputWithin _ (by simp [RejoinContext.outputRows])
  · intro substitution substitutionMember atom instantiated
    have exact := interfaceExact substitution substitutionMember
    have atomExact := Option.some.inj (instantiated.symm.trans exact.2.2.2.1)
    subst atom
    exact outputWithin _ (by simp [RejoinContext.outputRows])
  · intro substitution substitutionMember atom instantiated
    have exact := interfaceExact substitution substitutionMember
    have atomExact := Option.some.inj (instantiated.symm.trans exact.2.2.2.2)
    subst atom
    exact outputWithin _ (by simp [RejoinContext.outputRows])

/-- One physical assertion-rejoin firing preserves an atom-local invariant
from its live support and its exact source-indexed output interface. -/
theorem physical_assertion_rejoin_result_atoms_within_of_interface
    {context : RejoinContext} {space : List Atom} {property : Atom → Prop}
    (liveWithin : AtomsWithin property
      (morkEraseSupport space compressedAssertionRejoinDirective.atom))
    (outputWithin : AtomsWithin property context.outputRows)
    (interfaceExact :
      PhysicalAssertionRejoinMatcherInterfaceExact context space) :
    AtomsWithin property
      (cFireRuleScopedSourceExecFact space
        compressedAssertionRejoinDirective) := by
  unfold cFireRuleScopedSourceExecFact
  apply cApplyRuleScopedTemplate_atomsWithin_of_additions
  · exact liveWithin
  · simpa [physicalAssertionRejoinMatcherRows] using
      physical_assertion_rejoin_additions_within_of_interface outputWithin
        interfaceExact

/-- An exact input row survives the physical assertion-rejoin transaction
when its compact key differs from the three source-derived interface rows
that the transaction consumes.  Additions are unrestricted: only the exact
remove receipts of every physical matcher assignment matter. -/
theorem physical_assertion_rejoin_preserves_input_row_of_frame
    {context : RejoinContext} {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    (removeExact : ∀ substitution ∈ physicalAssertionRejoinMatcherRows space,
      instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input substitution
            rejoinContextTemplate = some context.contextRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input substitution
            rejoinReturnedControlTemplate = some context.returnedControlRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input substitution
            rejoinNormalLabelTemplate = some context.normalLabelRow)
    (row : Atom) (rowMember : row ∈ space)
    (notDirective : row ≠ compressedAssertionRejoinDirective.atom)
    (notContextKey :
      morkSupportKey row ≠ morkSupportKey context.contextRow)
    (notControlKey :
      morkSupportKey row ≠ morkSupportKey context.returnedControlRow)
    (notLabelKey :
      morkSupportKey row ≠ morkSupportKey context.normalLabelRow) :
    row ∈ cFireRuleScopedSourceExecFact space
      compressedAssertionRejoinDirective := by
  let rows := physicalAssertionRejoinMatcherRows space
  have liveMember : row ∈
      morkEraseSupport space compressedAssertionRejoinDirective.atom := by
    rw [physical_assertion_rejoin_live_eq listNodup morkNodup
      directivePresent]
    exact (List.mem_erase_of_ne notDirective).2 rowMember
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change row ∈ cApplyRuleScopedSinkBatch
    compressedAssertionRejoinDirective.rule.input rows
    (morkEraseSupport space compressedAssertionRejoinDirective.atom)
    compressedAssertionRejoinDirective.rule.tmpl.sinks
  rw [compressedAssertionRejoin_sinks_exact]
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    compressedAssertionRejoinDirective.rule.input rows
  · intro sink sinkMember
    simp only [rejoinSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨rejoinContextTemplate, rfl, by
        intro substitution substitutionMember removed instantiated
        have removedExact : removed = context.contextRow :=
          Option.some.inj
            (instantiated.symm.trans
              (removeExact substitution (by simpa [rows] using
                substitutionMember)).1)
        simpa [removedExact] using notContextKey⟩
    · exact Or.inr ⟨rejoinReturnedControlTemplate, rfl, by
        intro substitution substitutionMember removed instantiated
        have removedExact : removed = context.returnedControlRow :=
          Option.some.inj
            (instantiated.symm.trans
              (removeExact substitution (by simpa [rows] using
                substitutionMember)).2.1)
        simpa [removedExact] using notControlKey⟩
    · exact Or.inr ⟨rejoinNormalLabelTemplate, rfl, by
        intro substitution substitutionMember removed instantiated
        have removedExact : removed = context.normalLabelRow :=
          Option.some.inj
            (instantiated.symm.trans
              (removeExact substitution (by simpa [rows] using
                substitutionMember)).2.2)
        simpa [removedExact] using notLabelKey⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · exact liveMember

private theorem applySubstList_length (substitution : Subst) :
    ∀ atoms,
      (applySubst.applySubstList substitution atoms).length = atoms.length
  | [] => rfl
  | _ :: tail => by
      simp [applySubst.applySubstList,
        applySubstList_length substitution tail]

private theorem instantiateRuleTemplateAtom?_expression_shape
    (input : InputSpec) (substitution : Subst) (head : String)
    (tail : List Atom) (removed : Atom)
    (instantiated : instantiateRuleTemplateAtom? input substitution
      (.expression (.symbol head :: tail)) = some removed) :
    ∃ removedTail,
      removed = .expression (.symbol head :: removedTail) ∧
        removedTail.length = tail.length := by
  unfold instantiateRuleTemplateAtom? at instantiated
  split at instantiated
  · simp only [applySubst, applySubst.applySubstList,
      Option.some.injEq] at instantiated
    subst removed
    exact ⟨applySubst.applySubstList substitution tail, rfl,
      applySubstList_length substitution tail⟩
  · simp at instantiated

/-- Compiler-owned runtime captures are a physical frame of assertion
rejoin in every admitted space.  This does not depend on a canonical matcher
witness: substitution preserves each authored remove template's literal
outer head, whose compact identity differs from the capture constructor. -/
theorem physical_assertion_rejoin_preserves_runtime_capture
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    (kind : String) (runtimeRule : Atom)
    (captureMember : compressedOwnedRuntimeRuleRow kind runtimeRule ∈ space) :
    compressedOwnedRuntimeRuleRow kind runtimeRule ∈
      cFireRuleScopedSourceExecFact space
        compressedAssertionRejoinDirective := by
  let rows := physicalAssertionRejoinMatcherRows space
  have notDirective : compressedOwnedRuntimeRuleRow kind runtimeRule ≠
      compressedAssertionRejoinDirective.atom := by
    simp [compressedOwnedRuntimeRuleRow, compressedAssertionRejoinDirective,
      compressedAssertionRejoinRule]
  have liveMember : compressedOwnedRuntimeRuleRow kind runtimeRule ∈
      morkEraseSupport space compressedAssertionRejoinDirective.atom := by
    rw [physical_assertion_rejoin_live_eq listNodup morkNodup
      directivePresent]
    exact (List.mem_erase_of_ne notDirective).2 captureMember
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change compressedOwnedRuntimeRuleRow kind runtimeRule ∈
    cApplyRuleScopedSinkBatch compressedAssertionRejoinDirective.rule.input
      rows (morkEraseSupport space compressedAssertionRejoinDirective.atom)
      compressedAssertionRejoinDirective.rule.tmpl.sinks
  rw [compressedAssertionRejoin_sinks_exact]
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    compressedAssertionRejoinDirective.rule.input rows
  · intro sink sinkMember
    simp only [rejoinSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨rejoinContextTemplate, rfl, by
        intro substitution _substitutionMember removed instantiated
        unfold rejoinContextTemplate at instantiated
        obtain ⟨removedTail, rfl, removedLength⟩ :=
          instantiateRuleTemplateAtom?_expression_shape _ _ _ _ _
            instantiated
        norm_num at removedLength
        unfold compressedOwnedRuntimeRuleRow
        exact morkSupportKey_expression_symbol_head_ne
          "mm-compressed-owned-runtime-rule"
          "mm-compressed-assertion-context"
          [.symbol kind, runtimeRule] removedTail
          (by norm_num) (by omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)⟩
    · exact Or.inr ⟨rejoinReturnedControlTemplate, rfl, by
        intro substitution _substitutionMember removed instantiated
        unfold rejoinReturnedControlTemplate at instantiated
        obtain ⟨removedTail, rfl, removedLength⟩ :=
          instantiateRuleTemplateAtom?_expression_shape _ _ _ _ _
            instantiated
        norm_num at removedLength
        unfold compressedOwnedRuntimeRuleRow
        exact morkSupportKey_expression_symbol_head_ne
          "mm-compressed-owned-runtime-rule" "mm-normal-control"
          [.symbol kind, runtimeRule] removedTail
          (by norm_num) (by omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)⟩
    · exact Or.inr ⟨rejoinNormalLabelTemplate, rfl, by
        intro substitution _substitutionMember removed instantiated
        unfold rejoinNormalLabelTemplate at instantiated
        obtain ⟨removedTail, rfl, removedLength⟩ :=
          instantiateRuleTemplateAtom?_expression_shape _ _ _ _ _
            instantiated
        norm_num at removedLength
        unfold compressedOwnedRuntimeRuleRow
        exact morkSupportKey_expression_symbol_head_ne
          "mm-compressed-owned-runtime-rule" "mm-linked-row"
          [.symbol kind, runtimeRule] removedTail
          (by norm_num) (by omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · exact liveMember

private def SupportedExecAtomOnly (expected : SourceExecFact)
    (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate = expected

private theorem nonexec_expression_supportedOnly
    (expected : SourceExecFact) (head : String) (tail : List Atom)
    (different : head ≠ "exec") :
    SupportedExecAtomOnly expected
      (.expression (.symbol head :: tail)) := by
  intro candidate extracted
  simp [extractSupportedSourceExecFact, extractRawExecFact, different]
    at extracted

private theorem normalAssertionReload_no_supported
    (proofOwner : Atom) :
    extractSupportedSourceExecFact (normalAssertionReloadAtom proofOwner) =
      none := by
  rfl

private theorem physicalNormalResultReference_supportedOnly
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionRejoinDirective)
      (physicalNormalResultReference context) := by
  intro atom member
  simp only [physicalNormalResultReference, List.mem_append] at member
  rcases member with live | output
  · have liveNodup :=
      (normalToRejoinSlice_nodup context).erase normalResultDirective.atom
    have notBody : atom ≠ context.bodyBuiltRow := by
      intro equal
      subst atom
      exact liveNodup.not_mem_erase live
    have afterDirective := List.mem_of_mem_erase live
    have notDirective : atom ≠ normalResultDirective.atom := by
      intro equal
      subst atom
      exact (normalToRejoinSlice_nodup context).not_mem_erase afterDirective
    have original := List.mem_of_mem_erase afterDirective
    change atom ∈ normalResultDirective.atom ::
      ([context.bodyBuiltRow, context.rejoinCaptureRow,
        context.rejoinContext.contextRow,
        context.rejoinContext.normalStackSuccessorRow,
        context.rejoinContext.nodeSuccessorRow,
        context.rejoinContext.normalLabelRow,
        context.rejoinContext.resumeCaptureRow] ++
          compressedScannerRuleCaptureRows) at original
    rw [List.mem_cons] at original
    rcases original with directive | original
    · exact False.elim (notDirective directive)
    rw [List.mem_append] at original
    rcases original with fixed | scanner
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with body | capture | contextRow | normalSuccessor |
        nodeSuccessor | normalLabel | resumeCapture
      · exact False.elim (notBody body)
      · subst atom
        unfold NormalResultContext.rejoinCaptureRow
        exact nonexec_expression_supportedOnly _ _ _ (by decide)
      · subst atom
        unfold RejoinContext.contextRow
        exact nonexec_expression_supportedOnly _ _ _ (by decide)
      · subst atom
        unfold RejoinContext.normalStackSuccessorRow
        exact nonexec_expression_supportedOnly _ _ _ (by decide)
      · subst atom
        unfold RejoinContext.nodeSuccessorRow compressedIndexSuccessorRow
        exact nonexec_expression_supportedOnly _ _ _ (by decide)
      · subst atom
        unfold RejoinContext.normalLabelRow
        exact nonexec_expression_supportedOnly _ _ _ (by decide)
      · subst atom
        unfold RejoinContext.resumeCaptureRow compressedOwnedRuntimeRuleRow
        exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · obtain ⟨tail, rfl⟩ := scannerCapture_shape scanner
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at output
    rcases output with rfl | rfl | rfl | rfl
    · unfold RejoinContext.returnedControlRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold RejoinContext.returnedStackRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · intro candidate extracted
      rw [normalAssertionReload_no_supported] at extracted
      contradiction
    · intro candidate extracted
      rw [extract_compressedAssertionRejoinRule_exact] at extracted
      exact (Option.some.inj extracted).symm

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

/-- The explicit canonical successor contains exactly the one supported
rejoin directive; the normal reload row is outside this supported executor
vocabulary. -/
theorem physicalNormalResultReference_supported_exact
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    cSupportedSourceExecFacts (physicalNormalResultReference context) =
      [compressedAssertionRejoinDirective] := by
  apply list_eq_singleton_of_nodup_mem_unique
  · exact supportedFacts_nodup_of_space_nodup
      (List.Nodup.of_map morkSupportKey morkNodup)
  · exact List.mem_filterMap.mpr
      ⟨compressedAssertionRejoinRule,
        (by simp [physicalNormalResultReference]),
        extract_compressedAssertionRejoinRule_exact⟩
  · intro candidate member
    rcases List.mem_filterMap.mp member with
      ⟨atom, atomMember, extracted⟩
    exact physicalNormalResultReference_supportedOnly context atom atomMember
      candidate extracted

theorem physicalNormalResult_supported_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    cSupportedSourceExecFacts (physicalNormalResult context) =
      [compressedAssertionRejoinDirective] := by
  have rowsPerm := physical_normal_result_perm_reference context
    inputMorkNodup referenceMorkNodup
  have supportedPerm := rowsPerm.filterMap extractSupportedSourceExecFact
  change (cSupportedSourceExecFacts (physicalNormalResult context)).Perm
    (cSupportedSourceExecFacts (physicalNormalResultReference context))
    at supportedPerm
  rw [physicalNormalResultReference_supported_exact context
    referenceMorkNodup] at supportedPerm
  exact List.perm_singleton.mp supportedPerm

def physicalAssertionRejoinResult (context : NormalResultContext) : List Atom :=
  cFireRuleScopedSourceExecFact (physicalNormalResult context)
    compressedAssertionRejoinDirective

def physicalAssertionRejoinReference (context : NormalResultContext) :
    List Atom :=
  ((((physicalNormalResultReference context).erase
        compressedAssertionRejoinDirective.atom).erase
      context.rejoinContext.contextRow).erase
      context.rejoinContext.returnedControlRow).erase
      context.rejoinContext.normalLabelRow ++
    context.rejoinContext.outputRows

/-- The physical transaction consumes exactly its context, returned control,
and normal-label carriers.  Later add sinks cannot recreate any of them. -/
theorem physical_assertion_rejoin_consumes_inputs
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    context.rejoinContext.contextRow ∉ physicalAssertionRejoinResult context ∧
      context.rejoinContext.returnedControlRow ∉
        physicalAssertionRejoinResult context ∧
      context.rejoinContext.normalLabelRow ∉
        physicalAssertionRejoinResult context := by
  let rows := physicalAssertionRejoinMatcherRows (physicalNormalResult context)
  have preListNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have preMorkNodup : MorkSupportNodup (physicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have prePerm := physical_normal_result_perm_reference context inputMorkNodup
    referenceMorkNodup
  have directivePresent : compressedAssertionRejoinDirective.atom ∈
      physicalNormalResult context := by
    apply prePerm.mem_iff.mpr
    simp [physicalNormalResultReference, compressedAssertionRejoinDirective]
  have exactMatch := physical_exact_assertion_rejoin_of_reflective
    context.rejoinContext preListNodup preMorkNodup directivePresent
      (physical_normal_result_supplies_exact_rejoin context inputMorkNodup
        referenceMorkNodup)
  obtain ⟨substitution, substitutionMember, _machine, _node, _stack, _resume,
      _resumeRule⟩ := exactMatch
  have outputExact : ∀ candidate ∈ rows,
      instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
            candidate rejoinReturnedMachineTemplate =
          some context.rejoinContext.returnedMachineRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinResultNodeTemplate =
          some context.rejoinContext.resultNodeRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinResultStackTemplate =
          some context.rejoinContext.resultStackRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinResumeTemplate = some context.rejoinContext.resumeRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            (.var "compressed-assertion-resume-rule") =
          some compressedAssertionResumeRule := by
    intro candidate member
    exact physical_normal_result_rejoin_matcher_interface_exact context
      inputMorkNodup referenceMorkNodup (by simpa [rows] using member)
  have removeExact : ∀ candidate ∈ rows,
      instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
            candidate rejoinContextTemplate =
          some context.rejoinContext.contextRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinReturnedControlTemplate =
          some context.rejoinContext.returnedControlRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinNormalLabelTemplate =
          some context.rejoinContext.normalLabelRow := by
    intro candidate member
    exact physical_normal_result_rejoin_remove_interface_exact context
      inputMorkNodup referenceMorkNodup (by simpa [rows] using member)
  have contextAbsent : context.rejoinContext.contextRow ∉
      cApplyRuleScopedSinkBatch compressedAssertionRejoinDirective.rule.input
        rows
        (morkEraseSupport (physicalNormalResult context)
          compressedAssertionRejoinDirective.atom) rejoinSinks := by
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      compressedAssertionRejoinDirective.rule.input rows
      (morkEraseSupport (physicalNormalResult context)
        compressedAssertionRejoinDirective.atom) [] rejoinContextTemplate
      context.rejoinContext.contextRow
      [.remove rejoinReturnedControlTemplate,
       .remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate, .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate, .add rejoinResumeTemplate,
       .add (.var "compressed-assertion-resume-rule")]
      substitution (by simpa [rows] using substitutionMember)
      (removeExact substitution (by simpa [rows] using substitutionMember)).1
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).1]
        simp [RejoinContext.contextRow, RejoinContext.returnedMachineRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.1]
        simp [RejoinContext.contextRow, RejoinContext.resultNodeRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.1]
        simp [RejoinContext.contextRow, RejoinContext.resultStackRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.2.1]
        simp [RejoinContext.contextRow, RejoinContext.resumeRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.2.2]
        simp [RejoinContext.contextRow, compressedAssertionResumeRule]⟩
  have controlAbsent : context.rejoinContext.returnedControlRow ∉
      cApplyRuleScopedSinkBatch compressedAssertionRejoinDirective.rule.input
        rows
        (morkEraseSupport (physicalNormalResult context)
          compressedAssertionRejoinDirective.atom) rejoinSinks := by
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      compressedAssertionRejoinDirective.rule.input rows
      (morkEraseSupport (physicalNormalResult context)
        compressedAssertionRejoinDirective.atom)
      [.remove rejoinContextTemplate] rejoinReturnedControlTemplate
      context.rejoinContext.returnedControlRow
      [.remove rejoinNormalLabelTemplate,
       .add rejoinReturnedMachineTemplate, .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate, .add rejoinResumeTemplate,
       .add (.var "compressed-assertion-resume-rule")]
      substitution (by simpa [rows] using substitutionMember)
      (removeExact substitution
        (by simpa [rows] using substitutionMember)).2.1
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).1]
        simp [RejoinContext.returnedControlRow,
          RejoinContext.returnedMachineRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.1]
        simp [RejoinContext.returnedControlRow, RejoinContext.resultNodeRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.1]
        simp [RejoinContext.returnedControlRow, RejoinContext.resultStackRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.2.1]
        simp [RejoinContext.returnedControlRow, RejoinContext.resumeRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.2.2]
        simp [RejoinContext.returnedControlRow,
          compressedAssertionResumeRule]⟩
  have labelAbsent : context.rejoinContext.normalLabelRow ∉
      cApplyRuleScopedSinkBatch compressedAssertionRejoinDirective.rule.input
        rows
        (morkEraseSupport (physicalNormalResult context)
          compressedAssertionRejoinDirective.atom) rejoinSinks := by
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      compressedAssertionRejoinDirective.rule.input rows
      (morkEraseSupport (physicalNormalResult context)
        compressedAssertionRejoinDirective.atom)
      [.remove rejoinContextTemplate, .remove rejoinReturnedControlTemplate]
      rejoinNormalLabelTemplate context.rejoinContext.normalLabelRow
      [.add rejoinReturnedMachineTemplate, .add rejoinResultNodeTemplate,
       .add rejoinResultStackTemplate, .add rejoinResumeTemplate,
       .add (.var "compressed-assertion-resume-rule")]
      substitution (by simpa [rows] using substitutionMember)
      (removeExact substitution
        (by simpa [rows] using substitutionMember)).2.2
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).1]
        simp [RejoinContext.normalLabelRow, RejoinContext.returnedMachineRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.1]
        simp [RejoinContext.normalLabelRow, RejoinContext.resultNodeRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.1]
        simp [RejoinContext.normalLabelRow, RejoinContext.resultStackRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.2.1]
        simp [RejoinContext.normalLabelRow, RejoinContext.resumeRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(outputExact candidate member).2.2.2.2]
        simp [RejoinContext.normalLabelRow, compressedAssertionResumeRule]⟩
  simpa [physicalAssertionRejoinResult, cFireRuleScopedSourceExecFact,
    cApplyRuleScopedTemplate, rows, physicalAssertionRejoinMatcherRows,
    compressedAssertionRejoin_sinks_exact] using
      And.intro contextAbsent (And.intro controlAbsent labelAbsent)

/-- Every atom produced or retained by physical rejoin execution belongs to
the one canonical duplicate-aware successor. -/
theorem physical_assertion_rejoin_rows_within_reference
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    ∀ row ∈ physicalAssertionRejoinResult context,
      row ∈ physicalAssertionRejoinReference context := by
  intro row rowMember
  let rows := physicalAssertionRejoinMatcherRows (physicalNormalResult context)
  let live := morkEraseSupport (physicalNormalResult context)
    compressedAssertionRejoinDirective.atom
  have preListNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have preMorkNodup : MorkSupportNodup (physicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have prePerm := physical_normal_result_perm_reference context inputMorkNodup
    preReferenceMorkNodup
  have directivePresent : compressedAssertionRejoinDirective.atom ∈
      physicalNormalResult context := by
    apply prePerm.mem_iff.mpr
    simp [physicalNormalResultReference, compressedAssertionRejoinDirective]
  have origin : row ∈ live ∨
      RuleScopedAddedAtom compressedAssertionRejoinDirective.rule.input rows
        compressedAssertionRejoinDirective.rule.tmpl.sinks row := by
    apply mem_cApplyRuleScopedTemplate_of_supportSet
      compressedAssertionRejoinDirective.rule.input live rows
        compressedAssertionRejoinDirective.rule.tmpl
        compressedAssertionRejoinDirective_supportSet
    simpa [physicalAssertionRejoinResult, cFireRuleScopedSourceExecFact,
      live, rows, physicalAssertionRejoinMatcherRows] using rowMember
  rcases origin with prior | added
  · have prior' : row ∈ (physicalNormalResult context).erase
        compressedAssertionRejoinDirective.atom := by
      dsimp only [live] at prior
      rw [physical_assertion_rejoin_live_eq preListNodup preMorkNodup
        directivePresent] at prior
      exact prior
    have preMember : row ∈ physicalNormalResult context :=
      List.mem_of_mem_erase prior'
    have referenceMember : row ∈ physicalNormalResultReference context :=
      prePerm.mem_iff.mp preMember
    have notDirective : row ≠ compressedAssertionRejoinDirective.atom := by
      intro equal
      subst row
      exact preListNodup.not_mem_erase prior'
    have afterDirective : row ∈
        (physicalNormalResultReference context).erase
          compressedAssertionRejoinDirective.atom :=
      (List.mem_erase_of_ne notDirective).2 referenceMember
    have consumed := physical_assertion_rejoin_consumes_inputs context
      inputMorkNodup preReferenceMorkNodup
    have notContext : row ≠ context.rejoinContext.contextRow := by
      intro equal
      subst row
      exact consumed.1 rowMember
    have notControl : row ≠ context.rejoinContext.returnedControlRow := by
      intro equal
      subst row
      exact consumed.2.1 rowMember
    have notLabel : row ≠ context.rejoinContext.normalLabelRow := by
      intro equal
      subst row
      exact consumed.2.2 rowMember
    simp [physicalAssertionRejoinReference, afterDirective, notContext,
      notControl, notLabel]
  · rcases added with
      ⟨sink, sinkMember, authored, sinkEq, substitution,
        substitutionMember, instantiated⟩
    have exact := physical_normal_result_rejoin_matcher_interface_exact
      context inputMorkNodup preReferenceMorkNodup
        (by simpa [rows] using substitutionMember)
    rw [compressedAssertionRejoin_sinks_exact] at sinkMember
    simp only [rejoinSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases sinkEq
    · cases sinkEq
    · cases sinkEq
    · cases sinkEq
      have rowExact := Option.some.inj (instantiated.symm.trans exact.1)
      subst row
      simp [physicalAssertionRejoinReference, RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.1)
      subst row
      simp [physicalAssertionRejoinReference, RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.1)
      subst row
      simp [physicalAssertionRejoinReference, RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.1)
      subst row
      simp [physicalAssertionRejoinReference, RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.2)
      subst row
      simp [physicalAssertionRejoinReference, RejoinContext.outputRows]

/-- Every row of the canonical rejoin successor is physically present after
the transaction.  Retained rows survive by compact-key separation; the five
new products use the exact matcher-interface receipt. -/
theorem physical_assertion_rejoin_reference_support_complete
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    ∀ row ∈ physicalAssertionRejoinReference context,
      morkSupportContains (physicalAssertionRejoinResult context) row = true := by
  intro row member
  let rows := physicalAssertionRejoinMatcherRows (physicalNormalResult context)
  have preListNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have preMorkNodup : MorkSupportNodup (physicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have prePerm := physical_normal_result_perm_reference context inputMorkNodup
    preReferenceMorkNodup
  have directivePresent : compressedAssertionRejoinDirective.atom ∈
      physicalNormalResult context := by
    apply prePerm.mem_iff.mpr
    simp [physicalNormalResultReference, compressedAssertionRejoinDirective]
  have exactMatch := physical_exact_assertion_rejoin_of_reflective
    context.rejoinContext preListNodup preMorkNodup directivePresent
      (physical_normal_result_supplies_exact_rejoin context inputMorkNodup
        preReferenceMorkNodup)
  have removeExact : ∀ candidate ∈ rows,
      instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
            candidate rejoinContextTemplate =
          some context.rejoinContext.contextRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinReturnedControlTemplate =
          some context.rejoinContext.returnedControlRow ∧
        instantiateRuleTemplateAtom?
            compressedAssertionRejoinDirective.rule.input candidate
            rejoinNormalLabelTemplate =
          some context.rejoinContext.normalLabelRow := by
    intro candidate candidateMember
    exact physical_normal_result_rejoin_remove_interface_exact context
      inputMorkNodup preReferenceMorkNodup
        (by simpa [rows] using candidateMember)
  simp only [physicalAssertionRejoinReference, List.mem_append] at member
  rcases member with retained | output
  · have afterControl := List.mem_of_mem_erase retained
    have afterContext := List.mem_of_mem_erase afterControl
    have afterDirective := List.mem_of_mem_erase afterContext
    have referenceMember := List.mem_of_mem_erase afterDirective
    have referenceListNodup :
        (physicalNormalResultReference context).Nodup :=
      List.Nodup.of_map morkSupportKey preReferenceMorkNodup
    have notLabel : row ≠ context.rejoinContext.normalLabelRow := by
      intro equal
      subst row
      exact (((referenceListNodup.erase
        compressedAssertionRejoinDirective.atom).erase
        context.rejoinContext.contextRow).erase
        context.rejoinContext.returnedControlRow).not_mem_erase retained
    have notControl : row ≠ context.rejoinContext.returnedControlRow := by
      intro equal
      subst row
      exact ((referenceListNodup.erase
        compressedAssertionRejoinDirective.atom).erase
        context.rejoinContext.contextRow).not_mem_erase afterControl
    have notContext : row ≠ context.rejoinContext.contextRow := by
      intro equal
      subst row
      exact (referenceListNodup.erase
        compressedAssertionRejoinDirective.atom).not_mem_erase afterContext
    have notDirective : row ≠ compressedAssertionRejoinDirective.atom := by
      intro equal
      subst row
      exact referenceListNodup.not_mem_erase afterDirective
    have keyNe (removed : Atom)
        (removedMember : removed ∈ physicalNormalResultReference context)
        (different : row ≠ removed) :
        morkSupportKey row ≠ morkSupportKey removed := by
      intro keysEqual
      exact different (morkSupportKey_injective_on preReferenceMorkNodup
        referenceMember removedMember keysEqual)
    have livePresent : row ∈ morkEraseSupport (physicalNormalResult context)
        compressedAssertionRejoinDirective.atom :=
      mem_morkEraseSupport_of_mem_of_key_ne
        (prePerm.mem_iff.mpr referenceMember)
        (keyNe compressedAssertionRejoinDirective.atom
          (by simp [physicalNormalResultReference,
            compressedAssertionRejoinDirective,
            compressedAssertionRejoinRule]) notDirective)
    have preserved := mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
      compressedAssertionRejoinDirective.rule.input rows
      (space := morkEraseSupport (physicalNormalResult context)
        compressedAssertionRejoinDirective.atom)
      (sinks := rejoinSinks) (candidate := row) (by
        intro sink sinkMember
        simp only [rejoinSinks, List.mem_cons, List.not_mem_nil, or_false]
          at sinkMember
        rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inr ⟨_, rfl, by
            intro candidate candidateMember removed instantiated
            have removedExact := Option.some.inj
              (instantiated.symm.trans
                (removeExact candidate candidateMember).1)
            subst removed
            exact keyNe context.rejoinContext.contextRow
              (by simp [physicalNormalResultReference, normalToRejoinSlice])
              notContext⟩
        · exact Or.inr ⟨_, rfl, by
            intro candidate candidateMember removed instantiated
            have removedExact := Option.some.inj
              (instantiated.symm.trans
                (removeExact candidate candidateMember).2.1)
            subst removed
            exact keyNe context.rejoinContext.returnedControlRow
              (by simp [physicalNormalResultReference]) notControl⟩
        · exact Or.inr ⟨_, rfl, by
            intro candidate candidateMember removed instantiated
            have removedExact := Option.some.inj
              (instantiated.symm.trans
                (removeExact candidate candidateMember).2.2)
            subst removed
            exact keyNe context.rejoinContext.normalLabelRow
              (by simp [physicalNormalResultReference, normalToRejoinSlice])
              notLabel⟩
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inl ⟨_, rfl⟩) livePresent
    simpa [physicalAssertionRejoinResult, cFireRuleScopedSourceExecFact,
      cApplyRuleScopedTemplate, rows, physicalAssertionRejoinMatcherRows,
      compressedAssertionRejoin_sinks_exact] using
        morkSupportContains_eq_true_of_mem preserved
  · have support := physical_assertion_rejoin_support_present
      context.rejoinContext (physicalNormalResult context) exactMatch
    simp only [RejoinContext.outputRows, List.mem_cons, List.not_mem_nil,
      or_false] at output
    rcases output with rfl | rfl | rfl | rfl | rfl
    · exact support.1
    · exact support.2.1
    · exact support.2.2.1
    · exact support.2.2.2.1
    · exact support.2.2.2.2

/-- Under explicit compact-key uniqueness, the physical rejoin result is a
permutation of the complete canonical successor.  This preserves exact atom
multiplicity while allowing the MORK carrier's internal enumeration order. -/
theorem physical_assertion_rejoin_perm_reference
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (preReferenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (resultReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    (physicalAssertionRejoinResult context).Perm
      (physicalAssertionRejoinReference context) := by
  have preListNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have resultNodup : (physicalAssertionRejoinResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ preListNodup
  have referenceNodup : (physicalAssertionRejoinReference context).Nodup :=
    List.Nodup.of_map morkSupportKey resultReferenceMorkNodup
  apply (List.perm_ext_iff_of_nodup resultNodup referenceNodup).2
  intro row
  constructor
  · exact physical_assertion_rejoin_rows_within_reference context
      inputMorkNodup preReferenceMorkNodup row
  · intro member
    exact mem_of_morkSupportContains_of_reference resultReferenceMorkNodup
      member
      (physical_assertion_rejoin_rows_within_reference context inputMorkNodup
        preReferenceMorkNodup)
      (physical_assertion_rejoin_reference_support_complete context
        inputMorkNodup preReferenceMorkNodup row member)

theorem physicalNormalResult_selects_rejoin
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    selectNextScheduled
        (cSupportedSourceExecFacts (physicalNormalResult context)) =
      some compressedAssertionRejoinDirective := by
  rw [physicalNormalResult_supported_exact context inputMorkNodup
    referenceMorkNodup]
  rfl

theorem physicalNormalResult_ruleScoped_rejoin_step
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (physicalNormalResult context) =
      some (physicalAssertionRejoinResult context) := by
  unfold cRuleScopedSourceWorkQueueStep physicalAssertionRejoinResult
  rw [physicalNormalResult_selects_rejoin context inputMorkNodup
    referenceMorkNodup]

/-- The actual output of the physical normal-result step takes a second,
nonempty physical MORK step, has an exact compact rejoin match, and inhabits
the OSLF-generated native type of that successor. -/
structure PhysicalNormalResultRejoinSegment
    (context : NormalResultContext) : Prop where
  inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context)
  referenceMorkNodup : MorkSupportNodup
    (physicalNormalResultReference context)
  resultReferenceMorkNodup : MorkSupportNodup
    (physicalAssertionRejoinReference context)
  exactPhysicalMatch : PhysicalExactCompressedAssertionRejoin
    context.rejoinContext (physicalNormalResult context)
  concreteStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (physicalNormalResult context) =
    some (physicalAssertionRejoinResult context)
  concreteTrace : Nonempty (CRuleScopedTrace .leaveInert 1
    (physicalNormalResult context) (physicalAssertionRejoinResult context))
  nativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 1
    (physicalNormalResult context) (physicalAssertionRejoinResult context))
  wholeTrace : Nonempty (CRuleScopedTrace .leaveInert 2
    (normalToRejoinSlice context) (physicalAssertionRejoinResult context))
  wholeNativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 2
    (normalToRejoinSlice context) (physicalAssertionRejoinResult context))
  outputSupport :
    morkSupportContains (physicalAssertionRejoinResult context)
          context.rejoinContext.returnedMachineRow = true ∧
      morkSupportContains (physicalAssertionRejoinResult context)
          context.rejoinContext.resultNodeRow = true ∧
      morkSupportContains (physicalAssertionRejoinResult context)
          context.rejoinContext.resultStackRow = true ∧
      morkSupportContains (physicalAssertionRejoinResult context)
          context.rejoinContext.resumeRow = true ∧
      morkSupportContains (physicalAssertionRejoinResult context)
          compressedAssertionResumeRule = true
  resultListNodup : (physicalAssertionRejoinResult context).Nodup
  resultMorkNodup : MorkSupportNodup
    (physicalAssertionRejoinResult context)
  resultPermReference : (physicalAssertionRejoinResult context).Perm
    (physicalAssertionRejoinReference context)

def physical_normal_result_rejoin_segment
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context))
    (resultReferenceMorkNodup : MorkSupportNodup
      (physicalAssertionRejoinReference context)) :
    PhysicalNormalResultRejoinSegment context := by
  have perm := physical_normal_result_perm_reference context inputMorkNodup
    referenceMorkNodup
  have listNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have morkNodup : MorkSupportNodup (physicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have directivePresent : compressedAssertionRejoinDirective.atom ∈
      physicalNormalResult context := by
    apply perm.mem_iff.mpr
    simp [physicalNormalResultReference, compressedAssertionRejoinDirective]
  have exactMatch := physical_exact_assertion_rejoin_of_reflective
    context.rejoinContext listNodup morkNodup directivePresent
      (physical_normal_result_supplies_exact_rejoin context inputMorkNodup
        referenceMorkNodup)
  have moved := physicalNormalResult_ruleScoped_rejoin_step context
    inputMorkNodup referenceMorkNodup
  let trace : CRuleScopedTrace .leaveInert 1
      (physicalNormalResult context) (physicalAssertionRejoinResult context) :=
    .step moved .refl
  have first := normalToRejoinSlice_ruleScoped_steps context
  let wholeTrace : CRuleScopedTrace .leaveInert 2
      (normalToRejoinSlice context) (physicalAssertionRejoinResult context) :=
    .step first (.step moved .refl)
  exact
    { inputMorkNodup := inputMorkNodup
      referenceMorkNodup := referenceMorkNodup
      resultReferenceMorkNodup := resultReferenceMorkNodup
      exactPhysicalMatch := exactMatch
      concreteStep := moved
      concreteTrace := ⟨trace⟩
      nativeTypeTrace := ⟨trace.toNativeTypeTrace⟩
      wholeTrace := ⟨wholeTrace⟩
      wholeNativeTypeTrace := ⟨wholeTrace.toNativeTypeTrace⟩
      outputSupport := physical_assertion_rejoin_support_present
        context.rejoinContext (physicalNormalResult context) exactMatch
      resultListNodup :=
        cFireRuleScopedSourceExecFact_list_nodup _ _ listNodup
      resultMorkNodup :=
        cFireRuleScopedSourceExecFact_mork_nodup _ _ morkNodup
      resultPermReference := physical_assertion_rejoin_perm_reference context
        inputMorkNodup referenceMorkNodup resultReferenceMorkNodup }


#print axioms compressedAssertionRejoinDirective_guards_exact
#print axioms physical_assertion_rejoin_matcher_mem_iff
#print axioms physical_exact_assertion_rejoin_of_reflective
#print axioms physical_assertion_rejoin_factor_origin
#print axioms physical_assertion_rejoin_fixed_head_origin
#print axioms physical_normal_result_rejoin_fixed_head_origin
#print axioms physical_normal_result_rejoin_context_exact
#print axioms physical_normal_result_rejoin_returned_control_exact
#print axioms physical_normal_result_rejoin_returned_stack_exact
#print axioms physical_normal_result_rejoin_normal_stack_successor_exact
#print axioms physical_normal_result_rejoin_node_successor_exact
#print axioms physical_normal_result_rejoin_normal_label_exact
#print axioms physical_normal_result_rejoin_resume_capture_exact
#print axioms rejoin_output_applySubst_exact_of_inputs
#print axioms physical_assertion_rejoin_factor_covered
#print axioms physical_normal_result_rejoin_matcher_interface_exact
#print axioms physical_normal_result_rejoin_remove_interface_exact
#print axioms compressedAssertionRejoinDirective_supportSet
#print axioms physical_assertion_rejoin_support_present
#print axioms physical_assertion_rejoin_live_supported_only_of_exact
#print axioms physical_assertion_rejoin_additions_within_of_interface
#print axioms physical_assertion_rejoin_result_atoms_within_of_interface
#print axioms physical_assertion_rejoin_preserves_input_row_of_frame
#print axioms physical_assertion_rejoin_preserves_runtime_capture
#print axioms physicalNormalResultReference_supported_exact
#print axioms physicalNormalResult_supported_exact
#print axioms physical_assertion_rejoin_consumes_inputs
#print axioms physical_assertion_rejoin_rows_within_reference
#print axioms physical_assertion_rejoin_reference_support_complete
#print axioms physical_assertion_rejoin_perm_reference
#print axioms physicalNormalResult_ruleScoped_rejoin_step
#print axioms physical_normal_result_rejoin_segment

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionRejoin
