import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionResume
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeScannerRuntime
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableInputMonotonicity

/-!
# Physical speculative compressed-assertion resume

The maintained speculative verifier resumes from the runtime inventory selected
by its compiler artifact.  This module instantiates the presentation-relative
physical resume theorem and records the actual one-step MORK/OSLF segment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalSpeculativeResume

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionResume
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalResult
open Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeScannerRuntime
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Minimal compiler-selected physical frame at the assertion-resume seam. -/
def speculativeResumeSpace (context : RejoinContext) : List Atom :=
  resumeMatchSliceFor speculativeScannerRuntimeRuleBundle context

theorem speculativeResumeSpace_nodup (context : RejoinContext) :
    (speculativeResumeSpace context).Nodup := by
  simp [speculativeResumeSpace, resumeMatchSliceFor,
    ScannerRuntimeRuleBundle.captureRows,
    speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
    RejoinContext.resumeRow, RejoinContext.bytes,
    compressedOwnedRuntimeRuleRow, compressedAssertionResumeDirective,
    compressedAssertionResumeRule]

private theorem speculativeScannerRuntimeCaptureRows_shape
    (row : Atom)
    (member : row ∈ speculativeScannerRuntimeRuleBundle.captureRows) :
    ∃ tail,
      row = .expression
        (.symbol "mm-compressed-owned-runtime-rule" :: tail) ∧
      tail.length = 2 := by
  simp only [ScannerRuntimeRuleBundle.captureRows,
    speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  all_goals
    unfold compressedOwnedRuntimeRuleRow
    exact ⟨_, rfl, rfl⟩

private theorem expression_key_not_mem_speculativeScannerRuntimeCaptureRows
    (head : String) (tail : List Atom)
    (arityBound : tail.length + 1 < 64)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ "mm-compressed-owned-runtime-rule") :
    morkSupportKey (.expression (.symbol head :: tail)) ∉
      speculativeScannerRuntimeRuleBundle.captureRows.map morkSupportKey := by
  intro member
  rw [List.mem_map] at member
  obtain ⟨row, rowMember, keyEqual⟩ := member
  obtain ⟨captureTail, rfl, captureTailLength⟩ :=
    speculativeScannerRuntimeCaptureRows_shape row rowMember
  have keyDifferent :
      morkSupportKey (.expression (.symbol head :: tail)) ≠
        morkSupportKey
          (.expression
            (.symbol "mm-compressed-owned-runtime-rule" :: captureTail)) := by
    apply morkSupportKey_expression_symbol_head_ne
    · exact arityBound
    · omega
    · exact headPositive
    · decide
    · exact headBound
    · decide
    · exact different
  exact keyDifferent keyEqual.symm

private theorem assertionResumeDirective_key_ne_resumeRow
    (context : RejoinContext) :
    morkSupportKey compressedAssertionResumeDirective.atom ≠
      morkSupportKey context.resumeRow := by
  unfold compressedAssertionResumeDirective compressedAssertionResumeRule
  unfold RejoinContext.resumeRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

theorem speculativeResumeSpace_mork_nodup (context : RejoinContext) :
    MorkSupportNodup (speculativeResumeSpace context) := by
  unfold MorkSupportNodup
  change
    (morkSupportKey compressedAssertionResumeDirective.atom ::
      morkSupportKey context.resumeRow ::
      speculativeScannerRuntimeRuleBundle.captureRows.map
        morkSupportKey).Nodup
  rw [List.nodup_cons, List.nodup_cons]
  constructor
  · intro member
    rw [List.mem_cons] at member
    rcases member with equal | captureMember
    · exact assertionResumeDirective_key_ne_resumeRow context equal
    · exact
        (expression_key_not_mem_speculativeScannerRuntimeCaptureRows
          "exec" _ (by norm_num) (by decide) (by decide) (by decide))
          captureMember
  constructor
  · unfold RejoinContext.resumeRow
    exact expression_key_not_mem_speculativeScannerRuntimeCaptureRows
      "mm-compressed-assertion-resume" _ (by norm_num) (by decide)
        (by decide) (by decide)
  · exact speculativeScannerRuntimeCaptureRows_mork_nodup

private theorem extract_supported_none_of_expression_head_ne
    (head : String) (tail : List Atom) (different : head ≠ "exec") :
    extractSupportedSourceExecFact
      (.expression (.symbol head :: tail)) = none := by
  simp [extractSupportedSourceExecFact, extractRawExecFact, different]

theorem speculativeResumeSpace_supported_exact (context : RejoinContext) :
    cSupportedSourceExecFacts (speculativeResumeSpace context) =
      [compressedAssertionResumeDirective] := by
  let tail := context.resumeRow ::
    speculativeScannerRuntimeRuleBundle.captureRows
  have tailNone : cSupportedSourceExecFacts tail = [] := by
    unfold cSupportedSourceExecFacts
    rw [List.filterMap_eq_nil_iff]
    intro row member
    dsimp only [tail] at member
    simp only [ScannerRuntimeRuleBundle.captureRows,
      speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
    · unfold RejoinContext.resumeRow
      exact extract_supported_none_of_expression_head_ne _ _ (by decide)
    all_goals
      unfold compressedOwnedRuntimeRuleRow
      exact extract_supported_none_of_expression_head_ne _ _ (by decide)
  change cSupportedSourceExecFacts
    (compressedAssertionResumeDirective.atom :: tail) =
      [compressedAssertionResumeDirective]
  unfold cSupportedSourceExecFacts at tailNone ⊢
  rw [List.filterMap_cons, tailNone]
  change
    (match extractSupportedSourceExecFact compressedAssertionResumeRule with
      | none => []
      | some directive => [directive]) =
      [compressedAssertionResumeDirective]
  rw [extract_compressedAssertionResumeRule_exact]

/-! ## Compiler-selected normal-result boundary -/

/-- Internal assertion-return boundary carrying exactly the scanner inventory
selected by the maintained verifier compiler. -/
def speculativeNormalToRejoinSlice (context : NormalResultContext) : List Atom :=
  normalResultDirective.atom ::
    ([context.bodyBuiltRow, context.rejoinCaptureRow,
      context.rejoinContext.contextRow,
      context.rejoinContext.normalStackSuccessorRow,
      context.rejoinContext.nodeSuccessorRow,
      context.rejoinContext.normalLabelRow,
      context.rejoinContext.resumeCaptureRow] ++
        speculativeScannerRuntimeRuleBundle.captureRows)

def speculativePhysicalNormalResult (context : NormalResultContext) : List Atom :=
  cFireRuleScopedSourceExecFact (speculativeNormalToRejoinSlice context)
    normalResultDirective

private def speculativeNormalToRejoinExtraRows
    (context : NormalResultContext) : List Atom :=
  [context.rejoinContext.contextRow,
   context.rejoinContext.normalStackSuccessorRow,
   context.rejoinContext.nodeSuccessorRow,
   context.rejoinContext.normalLabelRow,
   context.rejoinContext.resumeCaptureRow] ++
    speculativeScannerRuntimeRuleBundle.captureRows

private theorem speculativeNormalToRejoin_read_eq
    (context : NormalResultContext) :
    normalResultDirective.atom ::
        (speculativeNormalToRejoinSlice context).erase
          normalResultDirective.atom =
      context.matchSlice ++ speculativeNormalToRejoinExtraRows context := by
  unfold speculativeNormalToRejoinSlice
  rw [List.erase_cons_head]
  rfl

private theorem speculativeNormalToRejoinExtraRows_never_match
    (context : NormalResultContext) (substitution : Subst) (pattern : Atom)
    (patternMember : pattern ∈ normalResultPatterns) (row : Atom)
    (rowMember : row ∈ speculativeNormalToRejoinExtraRows context) :
    cmatchAtom substitution pattern row = none := by
  simp only [normalResultPatterns, List.mem_cons, List.not_mem_nil,
    or_false] at patternMember
  simp only [speculativeNormalToRejoinExtraRows, List.mem_append] at rowMember
  rcases rowMember with fixed | capture
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases patternMember with rfl | rfl <;>
      rcases fixed with rfl | rfl | rfl | rfl | rfl <;>
      simp [normalResultCursorTemplate, normalResultCaptureTemplate,
        RejoinContext.contextRow, RejoinContext.normalStackSuccessorRow,
        RejoinContext.nodeSuccessorRow, RejoinContext.normalLabelRow,
        RejoinContext.resumeCaptureRow, compressedIndexSuccessorRow,
        compressedOwnedRuntimeRuleRow, cmatchAtom, cmatchAtomList]
  · simp only [ScannerRuntimeRuleBundle.captureRows,
      speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
      List.mem_cons, List.not_mem_nil, or_false] at capture
    rcases patternMember with rfl | rfl <;>
      rcases capture with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;>
      simp [normalResultCursorTemplate, normalResultCaptureTemplate,
        compressedOwnedRuntimeRuleRow, cmatchAtom, cmatchAtomList]

private theorem speculativeNormalToRejoin_matcher_eq_canonical
    (context : NormalResultContext) :
    cmatchInputSpec []
        (normalResultDirective.atom ::
          (speculativeNormalToRejoinSlice context).erase
            normalResultDirective.atom)
        normalResultDirective.rule.input =
      cmatchInputSpec [] context.matchSlice normalResultDirective.rule.input := by
  rw [speculativeNormalToRejoin_read_eq, normalResult_input_exact]
  exact cmatchPattern_append_of_right_never_matches [] context.matchSlice
    (speculativeNormalToRejoinExtraRows context)
    (mkPattern normalResultPatterns)
    (speculativeNormalToRejoinExtraRows_never_match context)

private theorem speculativeNormalToRejoin_matcher_interface_exact
    (context : NormalResultContext) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec []
        (normalResultDirective.atom ::
          (speculativeNormalToRejoinSlice context).erase
            normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst) :
    instantiateTemplateAtom? substitution normalResultCursorTemplate =
        some context.bodyBuiltRow ∧
      instantiateTemplateAtom? substitution normalResultControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateTemplateAtom? substitution normalResultStackTemplate =
        some context.rejoinContext.returnedStackRow ∧
      instantiateTemplateAtom? substitution normalResultReloadTemplate =
        some (normalAssertionReloadAtom context.proofOwner) ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule := by
  rw [speculativeNormalToRejoin_matcher_eq_canonical] at member
  rw [normalResult_input_exact] at member
  have lifted := cmatchInputSpec_compat_mono [] context.matchSlice
    (normalResultDirective.atom ::
      (normalToRejoinSlice context).erase normalResultDirective.atom)
    normalResultPatterns (fun atom atomMember => by
      simp only [NormalResultContext.matchSlice, List.mem_cons,
        List.not_mem_nil, or_false] at atomMember
      rcases atomMember with rfl | rfl | rfl <;>
        simp [normalToRejoinSlice]) member
  exact normalToRejoin_matcher_interface_exact context lifted

private theorem speculative_normalResultDirective_ne_nonexec_expression
    (head : String) (tail : List Atom) (headNe : head ≠ "exec") :
    normalResultDirective.atom ≠
      .expression (.symbol head :: tail) := by
  intro equal
  have decoded := congrArg extractSupportedSourceExecFact equal
  have selfDecoded : extractSupportedSourceExecFact
      normalResultDirective.atom = some normalResultDirective := by
    have directiveAtom :=
      extractSupportedSourceExecFact_atom extract_normalResultRule_exact
    rw [directiveAtom]
    exact extract_normalResultRule_exact
  rw [selfDecoded] at decoded
  simp [extractSupportedSourceExecFact, extractRawExecFact, headNe] at decoded

private theorem speculative_normalResultDirective_decodes :
    extractSupportedSourceExecFact normalResultDirective.atom =
      some normalResultDirective := by
  have directiveAtom :=
    extractSupportedSourceExecFact_atom extract_normalResultRule_exact
  rw [directiveAtom]
  exact extract_normalResultRule_exact

private theorem speculative_nonexec_expression_no_supported
    (head : String) (tail : List Atom) (headNe : head ≠ "exec") :
    extractSupportedSourceExecFact
      (.expression (.symbol head :: tail)) = none := by
  simp [extractSupportedSourceExecFact, extractRawExecFact, headNe]

theorem speculativeNormalToRejoinSlice_nodup
    (context : NormalResultContext) :
    (speculativeNormalToRejoinSlice context).Nodup := by
  simp [speculativeNormalToRejoinSlice,
    ScannerRuntimeRuleBundle.captureRows,
    speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
    NormalResultContext.bodyBuiltRow, NormalResultContext.rejoinCaptureRow,
    RejoinContext.contextRow, RejoinContext.normalStackSuccessorRow,
    RejoinContext.nodeSuccessorRow, RejoinContext.normalLabelRow,
    RejoinContext.resumeCaptureRow, compressedIndexSuccessorRow,
    compressedOwnedRuntimeRuleRow,
    speculative_normalResultDirective_ne_nonexec_expression]

theorem speculativeNormalToRejoinSlice_supported_exact
    (context : NormalResultContext) :
    cSupportedSourceExecFacts (speculativeNormalToRejoinSlice context) =
      [normalResultDirective] := by
  let tail :=
    [context.bodyBuiltRow, context.rejoinCaptureRow,
      context.rejoinContext.contextRow,
      context.rejoinContext.normalStackSuccessorRow,
      context.rejoinContext.nodeSuccessorRow,
      context.rejoinContext.normalLabelRow,
      context.rejoinContext.resumeCaptureRow] ++
        speculativeScannerRuntimeRuleBundle.captureRows
  have tailNone : cSupportedSourceExecFacts tail = [] := by
    unfold cSupportedSourceExecFacts
    rw [List.filterMap_eq_nil_iff]
    intro row member
    dsimp only [tail] at member
    simp only [ScannerRuntimeRuleBundle.captureRows,
      speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with fixed | capture
    · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold NormalResultContext.bodyBuiltRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
      · unfold NormalResultContext.rejoinCaptureRow
        unfold compressedOwnedRuntimeRuleRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
      · unfold RejoinContext.contextRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
      · unfold RejoinContext.normalStackSuccessorRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
      · unfold RejoinContext.nodeSuccessorRow compressedIndexSuccessorRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
      · unfold RejoinContext.normalLabelRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
      · unfold RejoinContext.resumeCaptureRow compressedOwnedRuntimeRuleRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
    · rcases capture with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl
      all_goals
        unfold compressedOwnedRuntimeRuleRow
        exact speculative_nonexec_expression_no_supported _ _ (by decide)
  change cSupportedSourceExecFacts (normalResultDirective.atom :: tail) =
    [normalResultDirective]
  unfold cSupportedSourceExecFacts at tailNone ⊢
  rw [List.filterMap_cons, speculative_normalResultDirective_decodes,
    tailNone]

theorem speculativeNormalToRejoinSlice_selects_normal_result
    (context : NormalResultContext) :
    selectNextScheduled
        (cSupportedSourceExecFacts
          (speculativeNormalToRejoinSlice context)) =
      some normalResultDirective := by
  rw [speculativeNormalToRejoinSlice_supported_exact]
  rfl

theorem speculativeNormalToRejoinSlice_ruleScoped_step
    (context : NormalResultContext) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (speculativeNormalToRejoinSlice context) =
      some (speculativePhysicalNormalResult context) := by
  unfold cRuleScopedSourceWorkQueueStep speculativePhysicalNormalResult
  rw [speculativeNormalToRejoinSlice_selects_normal_result]

private theorem speculative_instantiateRuleTemplateAtom?_of_reflective
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

/-- Every compact-key matcher assignment at the transformed boundary has the
same source-indexed interface. -/
theorem physical_speculative_normal_result_matcher_interface_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    {substitution : Subst}
    (member : substitution ∈ physicalNormalResultMatcherRows
      (speculativeNormalToRejoinSlice context)) :
    instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultCursorTemplate =
        some context.bodyBuiltRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultStackTemplate =
        some context.rejoinContext.returnedStackRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultReloadTemplate =
        some (normalAssertionReloadAtom context.proofOwner) ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule := by
  unfold physicalNormalResultMatcherRows at member
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ := member
  simp only at equal
  subst matchedSubstitution
  rw [List.mem_filter] at filtered
  have ordinaryPair :=
    (physical_normal_result_matcher_mem_iff
      (speculativeNormalToRejoinSlice_nodup context) inputMorkNodup
      (by simp [speculativeNormalToRejoinSlice]) substitution consumed).1
      filtered.1
  have ordinaryMember : substitution ∈
      (cmatchInputSpec []
        (normalResultDirective.atom ::
          (speculativeNormalToRejoinSlice context).erase
            normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst := by
    rw [List.mem_map]
    exact ⟨(substitution, consumed), ordinaryPair, rfl⟩
  obtain ⟨cursor, control, stack, reload, rejoin⟩ :=
    speculativeNormalToRejoin_matcher_interface_exact context ordinaryMember
  exact ⟨speculative_instantiateRuleTemplateAtom?_of_reflective _ cursor,
    speculative_instantiateRuleTemplateAtom?_of_reflective _ control,
    speculative_instantiateRuleTemplateAtom?_of_reflective _ stack,
    speculative_instantiateRuleTemplateAtom?_of_reflective _ reload,
    speculative_instantiateRuleTemplateAtom?_of_reflective _ rejoin⟩

theorem physical_speculative_normal_result_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context)) :
    PhysicalExactNormalResultRejoin context
      (speculativeNormalToRejoinSlice context) := by
  apply physical_exact_normal_result_rejoin_of_reflective context
    (speculativeNormalToRejoinSlice_nodup context) inputMorkNodup
    (by simp [speculativeNormalToRejoinSlice])
  apply exact_normal_result_rejoin_of_live_rows
  · simp [speculativeNormalToRejoinSlice]
  · simp [speculativeNormalToRejoinSlice,
      NormalResultContext.rejoinCaptureRow, compressedOwnedRuntimeRuleRow]

private theorem speculative_expression_key_ne_normal_result_body
    (context : NormalResultContext) (head : String) (tail : List Atom)
    (arityBound : tail.length + 1 < 64)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ "mm-body-built") :
    morkSupportKey (.expression (.symbol head :: tail)) ≠
      morkSupportKey context.bodyBuiltRow := by
  unfold NormalResultContext.bodyBuiltRow
  apply morkSupportKey_expression_symbol_head_ne
  · exact arityBound
  · norm_num
  · exact headPositive
  · decide
  · exact headBound
  · decide
  · exact different

/-- The exact source-indexed rows needed by assertion rejoin survive the
compiler-selected physical normal-result transaction. -/
theorem speculativePhysicalNormalResult_preserves_rejoin_inputs
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context)) :
    context.rejoinContext.contextRow ∈
        speculativePhysicalNormalResult context ∧
      context.rejoinContext.normalStackSuccessorRow ∈
        speculativePhysicalNormalResult context ∧
      context.rejoinContext.nodeSuccessorRow ∈
        speculativePhysicalNormalResult context ∧
      context.rejoinContext.normalLabelRow ∈
        speculativePhysicalNormalResult context ∧
      context.rejoinContext.resumeCaptureRow ∈
        speculativePhysicalNormalResult context := by
  have preserve {candidate : Atom}
      (present : candidate ∈
        (speculativeNormalToRejoinSlice context).erase
          normalResultDirective.atom)
      (different : morkSupportKey candidate ≠
        morkSupportKey context.bodyBuiltRow) :
      candidate ∈ speculativePhysicalNormalResult context := by
    apply physical_normal_result_preserves_row_of_exact_cursor
      (speculativeNormalToRejoinSlice_nodup context) inputMorkNodup
      (by simp [speculativeNormalToRejoinSlice])
    · intro substitution member
      exact (physical_speculative_normal_result_matcher_interface_exact
        context inputMorkNodup member).1
    · exact present
    · exact different
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply preserve
    · simp [speculativeNormalToRejoinSlice]
    · unfold RejoinContext.contextRow
      apply speculative_expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [speculativeNormalToRejoinSlice]
    · unfold RejoinContext.normalStackSuccessorRow
      apply speculative_expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [speculativeNormalToRejoinSlice]
    · unfold RejoinContext.nodeSuccessorRow compressedIndexSuccessorRow
      apply speculative_expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [speculativeNormalToRejoinSlice]
    · unfold RejoinContext.normalLabelRow
      apply speculative_expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · exact physical_normal_result_preserves_runtime_capture
      (speculativeNormalToRejoinSlice_nodup context) inputMorkNodup
      (by simp [speculativeNormalToRejoinSlice]) "assertion-resume"
      compressedAssertionResumeRule
      (by simp [speculativeNormalToRejoinSlice,
        RejoinContext.resumeCaptureRow])

/-- A duplicate-aware nominal envelope for the first transformed physical
successor.  It contains every retained row and every possible exact output;
compact-key uniqueness is stated separately at use sites. -/
def speculativeNormalResultEnvelope (context : NormalResultContext) :
    List Atom :=
  (speculativeNormalToRejoinSlice context).erase normalResultDirective.atom ++
    [context.rejoinContext.returnedControlRow,
     context.rejoinContext.returnedStackRow,
     normalAssertionReloadAtom context.proofOwner,
     compressedAssertionRejoinRule]

private theorem speculativeNormalResultEnvelope_cases
    (context : NormalResultContext) {row : Atom}
    (member : row ∈ speculativeNormalResultEnvelope context) :
    row = context.bodyBuiltRow ∨
      row = context.rejoinCaptureRow ∨
      row = context.rejoinContext.contextRow ∨
      row = context.rejoinContext.normalStackSuccessorRow ∨
      row = context.rejoinContext.nodeSuccessorRow ∨
      row = context.rejoinContext.normalLabelRow ∨
      row = context.rejoinContext.resumeCaptureRow ∨
      row ∈ speculativeScannerRuntimeRuleBundle.captureRows ∨
      row = context.rejoinContext.returnedControlRow ∨
      row = context.rejoinContext.returnedStackRow ∨
      row = normalAssertionReloadAtom context.proofOwner ∨
      row = compressedAssertionRejoinRule := by
  simp only [speculativeNormalResultEnvelope, List.mem_append] at member
  rcases member with live | output
  · have original := List.mem_of_mem_erase live
    change row ∈ normalResultDirective.atom ::
      ([context.bodyBuiltRow, context.rejoinCaptureRow,
        context.rejoinContext.contextRow,
        context.rejoinContext.normalStackSuccessorRow,
        context.rejoinContext.nodeSuccessorRow,
        context.rejoinContext.normalLabelRow,
        context.rejoinContext.resumeCaptureRow] ++
          speculativeScannerRuntimeRuleBundle.captureRows) at original
    rcases List.mem_cons.mp original with directive | original
    · subst row
      exact False.elim
        ((speculativeNormalToRejoinSlice_nodup context).not_mem_erase live)
    rcases List.mem_append.mp original with fixed | capture
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl capture)))))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at output
    rcases output with rfl | rfl | rfl | rfl <;> simp

private theorem speculativeNormalResultEnvelope_fixed_head_unique
    (context : NormalResultContext) {carrier : Atom}
    (member : carrier ∈ speculativeNormalResultEnvelope context) :
    (compressedDynamicRowHead? carrier =
        some "mm-compressed-assertion-context" →
      carrier = context.rejoinContext.contextRow) ∧
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
  rcases speculativeNormalResultEnvelope_cases context member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | capture | rfl | rfl | rfl |
      rfl
  all_goals try
    simp [compressedDynamicRowHead?, NormalResultContext.bodyBuiltRow,
      NormalResultContext.rejoinCaptureRow, RejoinContext.contextRow,
      RejoinContext.normalStackSuccessorRow, RejoinContext.nodeSuccessorRow,
      RejoinContext.normalLabelRow, RejoinContext.resumeCaptureRow,
      RejoinContext.returnedControlRow, RejoinContext.returnedStackRow,
      normalAssertionReloadAtom, compressedAssertionRejoinRule,
      compressedOwnedRuntimeRuleRow, compressedIndexSuccessorRow]
  obtain ⟨tail, rfl, _length⟩ :=
    speculativeScannerRuntimeCaptureRows_shape _ capture
  simp

private theorem speculativeNormalResultEnvelope_resume_capabilities
    (context : NormalResultContext) :
    AssertionResumeCapabilities compressedAssertionResumeRule
      (speculativeNormalResultEnvelope context) := by
  intro carrier member payload captured
  rcases speculativeNormalResultEnvelope_cases context member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | scanner | rfl | rfl | rfl |
      rfl
  · simp [AssertionResumeCapture, NormalResultContext.bodyBuiltRow,
      decodeCompressedExecutableCapture] at captured
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
  · simp only [ScannerRuntimeRuleBundle.captureRows,
      speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
      List.mem_cons, List.not_mem_nil, or_false] at scanner
    rcases scanner with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;>
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

/-- No physical normal-result row can escape the compiler-selected nominal
envelope.  This is the no-invention half of the internal handoff. -/
theorem speculativePhysicalNormalResult_rows_within_envelope
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context)) :
    ∀ row ∈ speculativePhysicalNormalResult context,
      row ∈ speculativeNormalResultEnvelope context := by
  intro row rowMember
  let rows := physicalNormalResultMatcherRows
    (speculativeNormalToRejoinSlice context)
  let live := morkEraseSupport (speculativeNormalToRejoinSlice context)
    normalResultDirective.atom
  have origin : row ∈ live ∨
      RuleScopedAddedAtom normalResultDirective.rule.input rows
        normalResultDirective.rule.tmpl.sinks row := by
    apply mem_cApplyRuleScopedTemplate_of_supportSet
      normalResultDirective.rule.input live rows
      normalResultDirective.rule.tmpl normalResultDirective_supportSet
    simpa [speculativePhysicalNormalResult,
      cFireRuleScopedSourceExecFact, live, rows,
      physicalNormalResultMatcherRows] using rowMember
  rcases origin with prior | added
  · have prior' : row ∈
        (speculativeNormalToRejoinSlice context).erase
          normalResultDirective.atom := by
      dsimp only [live] at prior
      rw [physical_normal_result_live_eq
        (speculativeNormalToRejoinSlice_nodup context) inputMorkNodup
        (by simp [speculativeNormalToRejoinSlice])] at prior
      exact prior
    exact List.mem_append_left _ prior'
  · rcases added with
      ⟨sink, sinkMember, _authored, sinkEq, substitution,
        substitutionMember, instantiated⟩
    have exact := physical_speculative_normal_result_matcher_interface_exact
      context inputMorkNodup (by simpa [rows] using substitutionMember)
    rw [normalResult_sinks_exact] at sinkMember
    simp only [normalResultSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl
    · cases sinkEq
    · cases sinkEq
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.1)
      subst row
      simp [speculativeNormalResultEnvelope]
    · cases sinkEq
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.2.1)
      subst row
      simp [speculativeNormalResultEnvelope]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.1)
      subst row
      simp [speculativeNormalResultEnvelope]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.2)
      subst row
      simp [speculativeNormalResultEnvelope]

private def SupportedExecAtomOnly (expected : SourceExecFact)
    (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate = expected

private theorem no_supported_of_mem_erase_of_supported_exact
    {space : List Atom} {directive : SourceExecFact} {atom : Atom}
    (spaceNodup : space.Nodup)
    (supportedExact : cSupportedSourceExecFacts space = [directive])
    (member : atom ∈ space.erase directive.atom) :
    extractSupportedSourceExecFact atom = none := by
  cases decoded : extractSupportedSourceExecFact atom with
  | none => rfl
  | some candidate =>
      have candidateMember : candidate ∈ cSupportedSourceExecFacts space :=
        List.mem_filterMap.mpr
          ⟨atom, List.mem_of_mem_erase member, decoded⟩
      rw [supportedExact] at candidateMember
      have candidateExact : candidate = directive := by
        simpa using candidateMember
      subst candidate
      have atomExact := extractSupportedSourceExecFact_atom decoded
      rw [← atomExact] at member
      exact False.elim (spaceNodup.not_mem_erase member)

private theorem speculativeNormalResultEnvelope_supportedOnly
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionRejoinDirective)
      (speculativeNormalResultEnvelope context) := by
  intro atom member
  simp only [speculativeNormalResultEnvelope, List.mem_append] at member
  rcases member with live | output
  · intro candidate extracted
    have absent := no_supported_of_mem_erase_of_supported_exact
      (speculativeNormalToRejoinSlice_nodup context)
      (speculativeNormalToRejoinSlice_supported_exact context) live
    rw [absent] at extracted
    contradiction
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at output
    rcases output with rfl | rfl | rfl | rfl
    · intro candidate extracted
      unfold RejoinContext.returnedControlRow at extracted
      rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
        at extracted
      contradiction
    · intro candidate extracted
      unfold RejoinContext.returnedStackRow at extracted
      rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
        at extracted
      contradiction
    · intro candidate extracted
      unfold normalAssertionReloadAtom at extracted
      rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
        at extracted
      contradiction
    · intro candidate extracted
      rw [extract_compressedAssertionRejoinRule_exact] at extracted
      exact (Option.some.inj extracted).symm

private theorem speculative_supportedFacts_nodup_of_space_nodup
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

private theorem speculative_list_eq_singleton_of_nodup_mem_unique
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

theorem speculativeNormalResultEnvelope_supported_exact
    (context : NormalResultContext)
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    cSupportedSourceExecFacts (speculativeNormalResultEnvelope context) =
      [compressedAssertionRejoinDirective] := by
  apply speculative_list_eq_singleton_of_nodup_mem_unique
  · exact speculative_supportedFacts_nodup_of_space_nodup
      (List.Nodup.of_map morkSupportKey envelopeMorkNodup)
  · exact List.mem_filterMap.mpr
      ⟨compressedAssertionRejoinRule,
        (by simp [speculativeNormalResultEnvelope]),
        extract_compressedAssertionRejoinRule_exact⟩
  · intro candidate candidateMember
    rcases List.mem_filterMap.mp candidateMember with
      ⟨atom, atomMember, extracted⟩
    exact speculativeNormalResultEnvelope_supportedOnly context atom
      atomMember candidate extracted

theorem speculativeNormalResultEnvelope_nodup
    (context : NormalResultContext)
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    (speculativeNormalResultEnvelope context).Nodup :=
  List.Nodup.of_map morkSupportKey envelopeMorkNodup

theorem speculativePhysicalNormalResult_outputs_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    context.rejoinContext.returnedControlRow ∈
        speculativePhysicalNormalResult context ∧
      context.rejoinContext.returnedStackRow ∈
        speculativePhysicalNormalResult context ∧
      normalAssertionReloadAtom context.proofOwner ∈
        speculativePhysicalNormalResult context ∧
      compressedAssertionRejoinRule ∈
        speculativePhysicalNormalResult context := by
  have support := physical_normal_result_support_present context
    (speculativeNormalToRejoinSlice context)
    (physical_speculative_normal_result_exact context inputMorkNodup)
  have within := speculativePhysicalNormalResult_rows_within_envelope context
    inputMorkNodup
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mem_of_morkSupportContains_of_reference envelopeMorkNodup
      (by simp [speculativeNormalResultEnvelope]) within support.1
  · exact mem_of_morkSupportContains_of_reference envelopeMorkNodup
      (by simp [speculativeNormalResultEnvelope]) within support.2.1
  · exact mem_of_morkSupportContains_of_reference envelopeMorkNodup
      (by simp [speculativeNormalResultEnvelope]) within support.2.2.1
  · exact mem_of_morkSupportContains_of_reference envelopeMorkNodup
      (by simp [speculativeNormalResultEnvelope]) within support.2.2.2

/-- The actual compiler-selected normal-result successor contains a complete
exact physical assertion-rejoin match. -/
theorem speculativePhysicalNormalResult_exact_rejoin
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    PhysicalExactCompressedAssertionRejoin context.rejoinContext
      (speculativePhysicalNormalResult context) := by
  have listNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have morkNodup : MorkSupportNodup
      (speculativePhysicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have inputs := speculativePhysicalNormalResult_preserves_rejoin_inputs
    context inputMorkNodup
  have outputs := speculativePhysicalNormalResult_outputs_exact context
    inputMorkNodup envelopeMorkNodup
  have live {row : Atom}
      (present : row ∈ speculativePhysicalNormalResult context)
      (different : row ≠ compressedAssertionRejoinDirective.atom) :
      row ∈ (speculativePhysicalNormalResult context).erase
        compressedAssertionRejoinDirective.atom :=
    (List.mem_erase_of_ne different).2 present
  apply physical_exact_assertion_rejoin_of_reflective context.rejoinContext
    listNodup morkNodup outputs.2.2.2
  apply exact_compressed_assertion_rejoin_of_live_rows
  · exact live inputs.1 (by
      simp [RejoinContext.contextRow, compressedAssertionRejoinDirective,
        compressedAssertionRejoinRule])
  · exact live outputs.1 (by
      simp [RejoinContext.returnedControlRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule])
  · exact live outputs.2.1 (by
      simp [RejoinContext.returnedStackRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule])
  · exact live inputs.2.1 (by
      simp [RejoinContext.normalStackSuccessorRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule])
  · exact live inputs.2.2.1 (by
      simp [RejoinContext.nodeSuccessorRow, compressedIndexSuccessorRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule])
  · exact live inputs.2.2.2.1 (by
      simp [RejoinContext.normalLabelRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule])
  · exact live inputs.2.2.2.2 (by
      simp [RejoinContext.resumeCaptureRow, compressedOwnedRuntimeRuleRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule])

private theorem speculativePhysicalNormalResult_fixed_head_exact_of_unique
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    {substitution : Subst} (head : String) (tail : List Atom)
    (headNe : head ≠ "exec")
    (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
      rejoinPatterns)
    (matcherMember : substitution ∈ physicalAssertionRejoinMatcherRows
      (speculativePhysicalNormalResult context))
    (expected : Atom)
    (unique : ∀ carrier ∈ speculativeNormalResultEnvelope context,
      compressedDynamicRowHead? carrier = some head → carrier = expected) :
    applySubst substitution (.expression (.symbol head :: tail)) =
      expected := by
  have listNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have morkNodup : MorkSupportNodup
      (speculativePhysicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have directivePresent :=
    (speculativePhysicalNormalResult_outputs_exact context inputMorkNodup
      envelopeMorkNodup).2.2.2
  obtain ⟨carrier, carrierMember, replay⟩ :=
    physical_assertion_rejoin_fixed_head_origin listNodup morkNodup
      directivePresent head tail headNe factorMember matcherMember
  have envelopeMember := speculativePhysicalNormalResult_rows_within_envelope
    context inputMorkNodup carrier carrierMember
  have carrierHead : compressedDynamicRowHead? carrier = some head := by
    rw [← replay]
    simp [applySubst, applySubst.applySubstList,
      compressedDynamicRowHead?]
  exact replay.trans (unique carrier envelopeMember carrierHead)

/-- Exact source-indexed interface reconstructed from every physical matcher
assignment at the compiler-selected normal-result successor. -/
structure PhysicalSpeculativeRejoinInputsExact
    (context : RejoinContext) (substitution : Subst) : Prop where
  contextRow : applySubst substitution rejoinContextTemplate =
    context.contextRow
  returnedControl : applySubst substitution rejoinReturnedControlTemplate =
    context.returnedControlRow
  returnedStack : applySubst substitution rejoinReturnedStackTemplate =
    context.returnedStackRow
  normalStackSuccessor :
    applySubst substitution rejoinNormalStackSuccessorTemplate =
      context.normalStackSuccessorRow
  nodeSuccessor : applySubst substitution rejoinNodeSuccessorTemplate =
    context.nodeSuccessorRow
  normalLabel : applySubst substitution rejoinNormalLabelTemplate =
    context.normalLabelRow
  resumeCapture : applySubst substitution rejoinResumeCaptureTemplate =
    context.resumeCaptureRow

theorem speculativePhysicalNormalResult_rejoin_inputs_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    {substitution : Subst}
    (matcherMember : substitution ∈ physicalAssertionRejoinMatcherRows
      (speculativePhysicalNormalResult context)) :
    PhysicalSpeculativeRejoinInputsExact context.rejoinContext
      substitution := by
  have fixed (head : String) (tail : List Atom)
      (headNe : head ≠ "exec")
      (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
        rejoinPatterns) (expected : Atom)
      (unique : ∀ carrier ∈ speculativeNormalResultEnvelope context,
        compressedDynamicRowHead? carrier = some head → carrier = expected) :
      applySubst substitution (.expression (.symbol head :: tail)) =
        expected :=
    speculativePhysicalNormalResult_fixed_head_exact_of_unique context
      inputMorkNodup envelopeMorkNodup head tail headNe factorMember
      matcherMember expected unique
  refine
    { contextRow := ?_
      returnedControl := ?_
      returnedStack := ?_
      normalStackSuccessor := ?_
      nodeSuccessor := ?_
      normalLabel := ?_
      resumeCapture := ?_ }
  · exact fixed "mm-compressed-assertion-context"
      [.var "scope-owner", .var "proof-owner", .var "word-position",
       .var "remaining-bytes", rejoinPCTemplate,
       rejoinNextPCTemplate, .var "assertion-label", .var "heap-next",
       .var "node-next"] (by decide)
      (by simp [rejoinPatterns, rejoinContextTemplate])
      context.rejoinContext.contextRow
      (fun carrier member head =>
        (speculativeNormalResultEnvelope_fixed_head_unique context member).1
          head)
  · exact fixed "mm-normal-control"
      [.var "scope-owner", .var "proof-owner", rejoinNextPCTemplate,
       .var "next-stack-position"] (by decide)
      (by simp [rejoinPatterns, rejoinReturnedControlTemplate])
      context.rejoinContext.returnedControlRow
      (fun carrier member head =>
        (speculativeNormalResultEnvelope_fixed_head_unique context
          member).2.1 head)
  · exact fixed "mm-stack-cell"
      [.var "proof-owner", .var "stack-base", .var "result-formula",
       rejoinOccurrenceTemplate] (by decide)
      (by simp [rejoinPatterns, rejoinReturnedStackTemplate])
      context.rejoinContext.returnedStackRow
      (fun carrier member head =>
        (speculativeNormalResultEnvelope_fixed_head_unique context
          member).2.2.1 head)
  · exact fixed "mm-index-successor"
      [.var "proof-owner", .var "stack-base",
       .var "next-stack-position"] (by decide)
      (by simp [rejoinPatterns, rejoinNormalStackSuccessorTemplate])
      context.rejoinContext.normalStackSuccessorRow
      (fun carrier member head =>
        (speculativeNormalResultEnvelope_fixed_head_unique context
          member).2.2.2.1 head)
  · exact fixed "mm-compressed-index-successor"
      [.expression [.symbol "mm-compressed-node-owner",
          .var "proof-owner"],
       .var "node-next", .var "next-node"] (by decide)
      (by simp [rejoinPatterns, rejoinNodeSuccessorTemplate])
      context.rejoinContext.nodeSuccessorRow
      (fun carrier member head =>
        (speculativeNormalResultEnvelope_fixed_head_unique context
          member).2.2.2.2.1 head)
  · exact fixed "mm-linked-row"
      [MM2DataEncoding.stringAtom "normal-proof-label",
       .var "proof-owner", rejoinPCTemplate, rejoinNextPCTemplate,
       .var "assertion-label"] (by decide)
      (by simp [rejoinPatterns, rejoinNormalLabelTemplate])
      context.rejoinContext.normalLabelRow
      (fun carrier member head =>
        (speculativeNormalResultEnvelope_fixed_head_unique context
          member).2.2.2.2.2 head)
  · obtain ⟨carrier, carrierMember, replay⟩ :=
      physical_assertion_rejoin_fixed_head_origin
        (cFireRuleScopedSourceExecFact_list_nodup _ _
          (speculativeNormalToRejoinSlice_nodup context))
        (cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup)
        (speculativePhysicalNormalResult_outputs_exact context
          inputMorkNodup envelopeMorkNodup).2.2.2
        "mm-compressed-owned-runtime-rule"
        [.symbol "assertion-resume",
         .var "compressed-assertion-resume-rule"]
        (by decide) (by simp [rejoinPatterns, rejoinResumeCaptureTemplate])
        matcherMember
    have envelopeMember :=
      speculativePhysicalNormalResult_rows_within_envelope context
        inputMorkNodup carrier carrierMember
    have captured : AssertionResumeCapture carrier
        (applySubst substitution
          (.var "compressed-assertion-resume-rule")) := by
      rw [← replay]
      rfl
    have payloadExact :=
      speculativeNormalResultEnvelope_resume_capabilities context carrier
        envelopeMember
        (applySubst substitution
          (.var "compressed-assertion-resume-rule")) captured
    unfold rejoinResumeCaptureTemplate RejoinContext.resumeCaptureRow
    unfold compressedOwnedRuntimeRuleRow
    simp only [applySubst, applySubst.applySubstList]
    simpa only [applySubst] using congrArg
      (fun payload => Atom.expression
        [Atom.symbol "mm-compressed-owned-runtime-rule",
         Atom.symbol "assertion-resume", payload]) payloadExact

/-- Every physical rejoin matcher assignment produces the same source-indexed
machine, node, stack, resume request, and admitted executable continuation. -/
theorem speculativePhysicalNormalResult_rejoin_matcher_interface_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    {substitution : Subst}
    (matcherMember : substitution ∈ physicalAssertionRejoinMatcherRows
      (speculativePhysicalNormalResult context)) :
    instantiateRuleTemplateAtom? compressedAssertionRejoinDirective.rule.input
          substitution rejoinReturnedMachineTemplate =
        some context.rejoinContext.returnedMachineRow ∧
      instantiateRuleTemplateAtom?
          compressedAssertionRejoinDirective.rule.input substitution
          rejoinResultNodeTemplate =
        some context.rejoinContext.resultNodeRow ∧
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
  have inputs := speculativePhysicalNormalResult_rejoin_inputs_exact context
    inputMorkNodup envelopeMorkNodup matcherMember
  have applied := rejoin_output_applySubst_exact_of_inputs
    context.rejoinContext substitution inputs.contextRow
      inputs.returnedControl inputs.returnedStack inputs.nodeSuccessor
      inputs.resumeCapture
  have listNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have morkNodup : MorkSupportNodup
      (speculativePhysicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have directivePresent :=
    (speculativePhysicalNormalResult_outputs_exact context inputMorkNodup
      envelopeMorkNodup).2.2.2
  have covered (factor : Atom) (member : factor ∈ rejoinPatterns) :
      templateCovered substitution factor = true :=
    physical_assertion_rejoin_factor_covered listNodup morkNodup
      directivePresent factor member matcherMember
  have outputCovered :
      templateCovered substitution rejoinReturnedMachineTemplate = true ∧
      templateCovered substitution rejoinResultNodeTemplate = true ∧
      templateCovered substitution rejoinResultStackTemplate = true ∧
      templateCovered substitution rejoinResumeTemplate = true ∧
      templateCovered substitution
        (.var "compressed-assertion-resume-rule") = true := by
    have contextCovered := covered rejoinContextTemplate
      (by simp [rejoinPatterns])
    have controlCovered := covered rejoinReturnedControlTemplate
      (by simp [rejoinPatterns])
    have stackCovered := covered rejoinReturnedStackTemplate
      (by simp [rejoinPatterns])
    have nodeCovered := covered rejoinNodeSuccessorTemplate
      (by simp [rejoinPatterns])
    have resumeCovered := covered rejoinResumeCaptureTemplate
      (by simp [rejoinPatterns])
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
    simp [instantiateTemplateAtom?, outputCovered.1,
      outputCovered.2.1, outputCovered.2.2.1,
      outputCovered.2.2.2.1, outputCovered.2.2.2.2, applied]
  exact ⟨speculative_instantiateRuleTemplateAtom?_of_reflective _ reflective.1,
    speculative_instantiateRuleTemplateAtom?_of_reflective _ reflective.2.1,
    speculative_instantiateRuleTemplateAtom?_of_reflective _
      reflective.2.2.1,
    speculative_instantiateRuleTemplateAtom?_of_reflective _
      reflective.2.2.2.1,
    speculative_instantiateRuleTemplateAtom?_of_reflective _
      reflective.2.2.2.2⟩

theorem speculativePhysicalNormalResult_supported_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    cSupportedSourceExecFacts (speculativePhysicalNormalResult context) =
      [compressedAssertionRejoinDirective] := by
  have resultNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have outputs := speculativePhysicalNormalResult_outputs_exact context
    inputMorkNodup envelopeMorkNodup
  apply speculative_list_eq_singleton_of_nodup_mem_unique
  · exact speculative_supportedFacts_nodup_of_space_nodup resultNodup
  · exact List.mem_filterMap.mpr
      ⟨compressedAssertionRejoinRule, outputs.2.2.2,
        extract_compressedAssertionRejoinRule_exact⟩
  · intro candidate candidateMember
    rcases List.mem_filterMap.mp candidateMember with
      ⟨atom, atomMember, extracted⟩
    have envelopeMember :=
      speculativePhysicalNormalResult_rows_within_envelope context
        inputMorkNodup atom atomMember
    exact speculativeNormalResultEnvelope_supportedOnly context atom
      envelopeMember candidate extracted

def speculativePhysicalAssertionRejoinResult
    (context : NormalResultContext) : List Atom :=
  cFireRuleScopedSourceExecFact (speculativePhysicalNormalResult context)
    compressedAssertionRejoinDirective

/-- Nominal no-invention envelope for the compiler-selected rejoin result.
It retains the entire pre-state envelope except the scheduled directive and
adds exactly the five source-indexed rejoin products. -/
def speculativeAssertionRejoinEnvelope
    (context : NormalResultContext) : List Atom :=
  (speculativeNormalResultEnvelope context).erase
      compressedAssertionRejoinDirective.atom ++
    context.rejoinContext.outputRows

private theorem speculativeRejoinOutputRows_supportedOnly
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionResumeDirective)
      context.rejoinContext.outputRows := by
  intro atom member
  simp only [RejoinContext.outputRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · intro candidate extracted
    unfold RejoinContext.returnedMachineRow at extracted
    rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
      at extracted
    contradiction
  · intro candidate extracted
    unfold RejoinContext.resultNodeRow at extracted
    rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
      at extracted
    contradiction
  · intro candidate extracted
    unfold RejoinContext.resultStackRow at extracted
    rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
      at extracted
    contradiction
  · intro candidate extracted
    unfold RejoinContext.resumeRow at extracted
    rw [speculative_nonexec_expression_no_supported _ _ (by decide)]
      at extracted
    contradiction
  · intro candidate extracted
    rw [extract_compressedAssertionResumeRule_exact] at extracted
    exact (Option.some.inj extracted).symm

private theorem speculativePhysicalAssertionRejoinResult_supportedOnly
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (preEnvelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionResumeDirective)
      (speculativePhysicalAssertionRejoinResult context) := by
  have listNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have morkNodup : MorkSupportNodup
      (speculativePhysicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have outputs := speculativePhysicalNormalResult_outputs_exact context
    inputMorkNodup preEnvelopeMorkNodup
  have liveWithin := physical_assertion_rejoin_live_supported_only_of_exact
    listNodup morkNodup outputs.2.2.2
    (next := compressedAssertionResumeDirective)
    (speculativePhysicalNormalResult_supported_exact context inputMorkNodup
      preEnvelopeMorkNodup)
  change AtomsWithin
    (SupportedExecAtomOnly compressedAssertionResumeDirective)
    (morkEraseSupport (speculativePhysicalNormalResult context)
      compressedAssertionRejoinDirective.atom) at liveWithin
  have interfaceExact : PhysicalAssertionRejoinMatcherInterfaceExact
      context.rejoinContext (speculativePhysicalNormalResult context) := by
    intro substitution substitutionMember
    exact speculativePhysicalNormalResult_rejoin_matcher_interface_exact context
      inputMorkNodup preEnvelopeMorkNodup substitutionMember
  have resultWithin :=
    physical_assertion_rejoin_result_atoms_within_of_interface
      (context := context.rejoinContext)
      (space := speculativePhysicalNormalResult context)
      (property := SupportedExecAtomOnly compressedAssertionResumeDirective)
      liveWithin
      (speculativeRejoinOutputRows_supportedOnly context) interfaceExact
  simpa only [speculativePhysicalAssertionRejoinResult] using resultWithin

theorem speculativePhysicalAssertionRejoinResult_rows_within_envelope
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (preEnvelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    ∀ row ∈ speculativePhysicalAssertionRejoinResult context,
      row ∈ speculativeAssertionRejoinEnvelope context := by
  intro row rowMember
  let rows := physicalAssertionRejoinMatcherRows
    (speculativePhysicalNormalResult context)
  let live := morkEraseSupport (speculativePhysicalNormalResult context)
    compressedAssertionRejoinDirective.atom
  have preListNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have preMorkNodup : MorkSupportNodup
      (speculativePhysicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have directivePresent :=
    (speculativePhysicalNormalResult_outputs_exact context inputMorkNodup
      preEnvelopeMorkNodup).2.2.2
  have origin : row ∈ live ∨
      RuleScopedAddedAtom compressedAssertionRejoinDirective.rule.input rows
        compressedAssertionRejoinDirective.rule.tmpl.sinks row := by
    apply mem_cApplyRuleScopedTemplate_of_supportSet
      compressedAssertionRejoinDirective.rule.input live rows
      compressedAssertionRejoinDirective.rule.tmpl
      compressedAssertionRejoinDirective_supportSet
    simpa [speculativePhysicalAssertionRejoinResult,
      cFireRuleScopedSourceExecFact, live, rows,
      physicalAssertionRejoinMatcherRows] using rowMember
  rcases origin with prior | added
  · have prior' : row ∈
        (speculativePhysicalNormalResult context).erase
          compressedAssertionRejoinDirective.atom := by
      dsimp only [live] at prior
      rw [physical_assertion_rejoin_live_eq preListNodup preMorkNodup
        directivePresent] at prior
      exact prior
    have preMember : row ∈ speculativePhysicalNormalResult context :=
      List.mem_of_mem_erase prior'
    have envelopeMember :=
      speculativePhysicalNormalResult_rows_within_envelope context
        inputMorkNodup row preMember
    have notDirective : row ≠ compressedAssertionRejoinDirective.atom := by
      intro equal
      subst row
      exact preListNodup.not_mem_erase prior'
    exact List.mem_append_left _
      ((List.mem_erase_of_ne notDirective).2 envelopeMember)
  · rcases added with
      ⟨sink, sinkMember, _authored, sinkEq, substitution,
        substitutionMember, instantiated⟩
    have exact :=
      speculativePhysicalNormalResult_rejoin_matcher_interface_exact context
        inputMorkNodup preEnvelopeMorkNodup
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
      simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.1)
      subst row
      simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.1)
      subst row
      simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.1)
      subst row
      simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.2)
      subst row
      simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]

theorem speculativePhysicalAssertionRejoinResult_outputs_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (preEnvelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    (resultEnvelopeMorkNodup : MorkSupportNodup
      (speculativeAssertionRejoinEnvelope context)) :
    context.rejoinContext.returnedMachineRow ∈
        speculativePhysicalAssertionRejoinResult context ∧
      context.rejoinContext.resultNodeRow ∈
        speculativePhysicalAssertionRejoinResult context ∧
      context.rejoinContext.resultStackRow ∈
        speculativePhysicalAssertionRejoinResult context ∧
      context.rejoinContext.resumeRow ∈
        speculativePhysicalAssertionRejoinResult context ∧
      compressedAssertionResumeRule ∈
        speculativePhysicalAssertionRejoinResult context := by
  have support := physical_assertion_rejoin_support_present
    context.rejoinContext (speculativePhysicalNormalResult context)
    (speculativePhysicalNormalResult_exact_rejoin context inputMorkNodup
      preEnvelopeMorkNodup)
  have within :=
    speculativePhysicalAssertionRejoinResult_rows_within_envelope context
      inputMorkNodup preEnvelopeMorkNodup
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mem_of_morkSupportContains_of_reference resultEnvelopeMorkNodup
      (by simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]) within support.1
  · exact mem_of_morkSupportContains_of_reference resultEnvelopeMorkNodup
      (by simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]) within support.2.1
  · exact mem_of_morkSupportContains_of_reference resultEnvelopeMorkNodup
      (by simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]) within support.2.2.1
  · exact mem_of_morkSupportContains_of_reference resultEnvelopeMorkNodup
      (by simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]) within support.2.2.2.1
  · exact mem_of_morkSupportContains_of_reference resultEnvelopeMorkNodup
      (by simp [speculativeAssertionRejoinEnvelope,
        RejoinContext.outputRows]) within support.2.2.2.2

theorem speculativePhysicalAssertionRejoinResult_supported_exact
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (preEnvelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    (resultEnvelopeMorkNodup : MorkSupportNodup
      (speculativeAssertionRejoinEnvelope context)) :
    cSupportedSourceExecFacts
        (speculativePhysicalAssertionRejoinResult context) =
      [compressedAssertionResumeDirective] := by
  have preListNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have resultListNodup :
      (speculativePhysicalAssertionRejoinResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ preListNodup
  have outputs := speculativePhysicalAssertionRejoinResult_outputs_exact
    context inputMorkNodup preEnvelopeMorkNodup resultEnvelopeMorkNodup
  apply speculative_list_eq_singleton_of_nodup_mem_unique
  · exact speculative_supportedFacts_nodup_of_space_nodup resultListNodup
  · exact List.mem_filterMap.mpr
      ⟨compressedAssertionResumeRule, outputs.2.2.2.2,
        extract_compressedAssertionResumeRule_exact⟩
  · intro candidate candidateMember
    rcases List.mem_filterMap.mp candidateMember with
      ⟨atom, atomMember, extracted⟩
    exact speculativePhysicalAssertionRejoinResult_supportedOnly context
      inputMorkNodup preEnvelopeMorkNodup atom atomMember candidate extracted

theorem speculativePhysicalNormalResult_selects_rejoin
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    selectNextScheduled
        (cSupportedSourceExecFacts
          (speculativePhysicalNormalResult context)) =
      some compressedAssertionRejoinDirective := by
  rw [speculativePhysicalNormalResult_supported_exact context inputMorkNodup
    envelopeMorkNodup]
  rfl

theorem speculativePhysicalNormalResult_ruleScoped_rejoin_step
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (envelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context)) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (speculativePhysicalNormalResult context) =
      some (speculativePhysicalAssertionRejoinResult context) := by
  unfold cRuleScopedSourceWorkQueueStep
    speculativePhysicalAssertionRejoinResult
  rw [speculativePhysicalNormalResult_selects_rejoin context inputMorkNodup
    envelopeMorkNodup]

/-- The complete compiler-selected scanner inventory survives the physical
normal-result transaction.  This is independent of which terminal
continuation the compiler selected. -/
theorem physical_normal_result_preserves_speculative_capture_rows
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space)
    (captureLive : ∀ row ∈
      speculativeScannerRuntimeRuleBundle.captureRows, row ∈ space) :
    ∀ row ∈ speculativeScannerRuntimeRuleBundle.captureRows,
      row ∈ cFireRuleScopedSourceExecFact space normalResultDirective := by
  intro row member
  simp only [ScannerRuntimeRuleBundle.captureRows,
    speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  all_goals
    apply physical_normal_result_preserves_runtime_capture listNodup
      morkNodup directivePresent
    apply captureLive
    simp [ScannerRuntimeRuleBundle.captureRows,
      speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle]

/-- The complete compiler-selected resume inventory survives a physical
assertion rejoin as exact atoms.  The statement quantifies over every
physical matcher assignment through the exact remove-interface receipt. -/
theorem physical_assertion_rejoin_preserves_speculative_capture_rows
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    (captureLive : ∀ row ∈
      speculativeScannerRuntimeRuleBundle.captureRows, row ∈ space) :
    ∀ row ∈ speculativeScannerRuntimeRuleBundle.captureRows,
      row ∈ cFireRuleScopedSourceExecFact space
        compressedAssertionRejoinDirective := by
  intro row member
  simp only [ScannerRuntimeRuleBundle.captureRows,
    speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  all_goals
    apply physical_assertion_rejoin_preserves_runtime_capture listNodup
      morkNodup directivePresent
    apply captureLive
    simp [ScannerRuntimeRuleBundle.captureRows,
      speculativeScannerRuntimeRuleBundle, baseSaveRuntimeRuleBundle]

/-- Compiler-selected captures survive the two actual physical transactions
from a normal result through assertion rejoin.  The exact rejoin-directive
membership remains an explicit upstream output obligation; no reconstructed
intermediate state is substituted for the MORK result. -/
theorem physical_normal_result_then_rejoin_preserves_speculative_capture_rows
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (normalPresent : normalResultDirective.atom ∈ space)
    (rejoinPresent : compressedAssertionRejoinDirective.atom ∈
      cFireRuleScopedSourceExecFact space normalResultDirective)
    (captureLive : ∀ row ∈
      speculativeScannerRuntimeRuleBundle.captureRows, row ∈ space) :
    ∀ row ∈ speculativeScannerRuntimeRuleBundle.captureRows,
      row ∈ cFireRuleScopedSourceExecFact
        (cFireRuleScopedSourceExecFact space normalResultDirective)
        compressedAssertionRejoinDirective := by
  have afterNormalListNodup :
      (cFireRuleScopedSourceExecFact space normalResultDirective).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ listNodup
  have afterNormalMorkNodup : MorkSupportNodup
      (cFireRuleScopedSourceExecFact space normalResultDirective) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ morkNodup
  have afterNormalCapture : ∀ row ∈
      speculativeScannerRuntimeRuleBundle.captureRows,
      row ∈ cFireRuleScopedSourceExecFact space normalResultDirective :=
    physical_normal_result_preserves_speculative_capture_rows listNodup
      morkNodup normalPresent captureLive
  exact physical_assertion_rejoin_preserves_speculative_capture_rows
    afterNormalListNodup afterNormalMorkNodup rejoinPresent afterNormalCapture

/-- The preserved compiler captures are already in the exact live view for
the next physical assertion-resume step: none can be the scheduled resume
directive, because their outer constructors differ. -/
theorem physical_assertion_rejoin_preserves_speculative_capture_rows_live
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedAssertionRejoinDirective.atom ∈ space)
    (captureLive : ∀ row ∈
      speculativeScannerRuntimeRuleBundle.captureRows, row ∈ space) :
    ∀ row ∈ speculativeScannerRuntimeRuleBundle.captureRows,
      row ∈
        (cFireRuleScopedSourceExecFact space
          compressedAssertionRejoinDirective).erase
            compressedAssertionResumeDirective.atom := by
  intro row member
  have notDirective : row ≠ compressedAssertionResumeDirective.atom := by
    obtain ⟨tail, rfl, _tailLength⟩ :=
      speculativeScannerRuntimeCaptureRows_shape row member
    simp [compressedAssertionResumeDirective, compressedAssertionResumeRule]
  exact (List.mem_erase_of_ne notDirective).2
    (physical_assertion_rejoin_preserves_speculative_capture_rows
      listNodup morkNodup directivePresent captureLive row member)

/-- Physical intermediate boundary produced after assertion rejoin.  Its
runtime captures are the compiler-selected speculative inventory; the live
conditions are stated after removing the scheduled resume directive so they
compose directly with rule-scoped MORK matching. -/
structure PhysicalSpeculativeResumeBoundary
    (context : RejoinContext) (space : List Atom) : Prop where
  listNodup : space.Nodup
  morkNodup : MorkSupportNodup space
  directivePresent : compressedAssertionResumeDirective.atom ∈ space
  resumeLive : context.resumeRow ∈
    space.erase compressedAssertionResumeDirective.atom
  captureLive : ∀ row ∈ speculativeScannerRuntimeRuleBundle.captureRows,
    row ∈ space.erase compressedAssertionResumeDirective.atom
  supportedExact : cSupportedSourceExecFacts space =
    [compressedAssertionResumeDirective]

/-- The actual compiler-selected assertion-rejoin result satisfies the exact
physical resume boundary. -/
theorem speculativePhysicalResumeBoundary
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (preEnvelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    (resultEnvelopeMorkNodup : MorkSupportNodup
      (speculativeAssertionRejoinEnvelope context)) :
    PhysicalSpeculativeResumeBoundary context.rejoinContext
      (speculativePhysicalAssertionRejoinResult context) := by
  have preListNodup : (speculativePhysicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (speculativeNormalToRejoinSlice_nodup context)
  have preMorkNodup : MorkSupportNodup
      (speculativePhysicalNormalResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ inputMorkNodup
  have resultListNodup :
      (speculativePhysicalAssertionRejoinResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _ preListNodup
  have resultMorkNodup : MorkSupportNodup
      (speculativePhysicalAssertionRejoinResult context) :=
    cFireRuleScopedSourceExecFact_mork_nodup _ _ preMorkNodup
  have outputs := speculativePhysicalAssertionRejoinResult_outputs_exact
    context inputMorkNodup preEnvelopeMorkNodup resultEnvelopeMorkNodup
  have preCapture : ∀ row ∈
      speculativeScannerRuntimeRuleBundle.captureRows,
      row ∈ speculativePhysicalNormalResult context :=
    physical_normal_result_preserves_speculative_capture_rows
      (speculativeNormalToRejoinSlice_nodup context) inputMorkNodup
      (by simp [speculativeNormalToRejoinSlice])
      (by
        intro row member
        unfold speculativeNormalToRejoinSlice
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact member)
  refine
    { listNodup := resultListNodup
      morkNodup := resultMorkNodup
      directivePresent := outputs.2.2.2.2
      resumeLive := ?_
      captureLive := ?_
      supportedExact :=
        speculativePhysicalAssertionRejoinResult_supported_exact context
          inputMorkNodup preEnvelopeMorkNodup resultEnvelopeMorkNodup }
  · exact (List.mem_erase_of_ne (by
      simp [RejoinContext.resumeRow, compressedAssertionResumeDirective,
        compressedAssertionResumeRule])).2 outputs.2.2.2.1
  · exact physical_assertion_rejoin_preserves_speculative_capture_rows_live
      preListNodup preMorkNodup
      (speculativePhysicalNormalResult_outputs_exact context inputMorkNodup
        preEnvelopeMorkNodup).2.2.2 preCapture

/-- Any physical intermediate boundary carrying the compiler-selected live
inventory has the exact transformed resume match. -/
theorem PhysicalSpeculativeResumeBoundary.exactPhysicalMatch
    {context : RejoinContext} {space : List Atom}
    (boundary : PhysicalSpeculativeResumeBoundary context space) :
    PhysicalExactCompressedAssertionResumeFor
      speculativeScannerRuntimeRuleBundle context space := by
  apply physical_exact_assertion_resume_for_of_live_rows
    speculativeScannerRuntimeRuleBundle context boundary.listNodup
      boundary.morkNodup boundary.directivePresent
  intro row member
  simp only [resumeMatchSliceFor, List.mem_cons] at member
  rcases member with rfl | member
  · exact List.mem_cons_self
  rcases member with rfl | capture
  · exact List.mem_cons_of_mem _ boundary.resumeLive
  · exact List.mem_cons_of_mem _ (boundary.captureLive row capture)

/-- Every admitted transformed resume boundary performs one actual scheduled
MORK step, and that primitive step inhabits the corresponding OSLF-generated
native target. -/
def PhysicalSpeculativeResumeBoundary.scheduledSegment
    {context : RejoinContext} {space : List Atom}
    (boundary : PhysicalSpeculativeResumeBoundary context space) :
    PhysicalAssertionResumeScheduledSegmentFor
      speculativeScannerRuntimeRuleBundle context space :=
  physical_assertion_resume_scheduled_segment_for
    speculativeScannerRuntimeRuleBundle context space boundary.listNodup
      boundary.morkNodup boundary.exactPhysicalMatch boundary.supportedExact

/-- Normal-result publication, assertion rejoin, and transformed scanner
resume form one connected three-transition physical MORK segment. -/
structure PhysicalSpeculativeAssertionTailSegment
    (context : NormalResultContext) : Type where
  resumeBoundary : PhysicalSpeculativeResumeBoundary context.rejoinContext
    (speculativePhysicalAssertionRejoinResult context)
  resumeStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (speculativePhysicalAssertionRejoinResult context) =
    some (physicalAssertionResumeResultFrom
      (speculativePhysicalAssertionRejoinResult context))
  wholeTrace : CRuleScopedTrace .leaveInert 3
    (speculativeNormalToRejoinSlice context)
    (physicalAssertionResumeResultFrom
      (speculativePhysicalAssertionRejoinResult context))
  wholeNativeTypeTrace : RuleScopedNativeTypeTrace .leaveInert 3
    (speculativeNormalToRejoinSlice context)
    (physicalAssertionResumeResultFrom
      (speculativePhysicalAssertionRejoinResult context))

def physical_speculative_assertion_tail_segment
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup
      (speculativeNormalToRejoinSlice context))
    (preEnvelopeMorkNodup : MorkSupportNodup
      (speculativeNormalResultEnvelope context))
    (resultEnvelopeMorkNodup : MorkSupportNodup
      (speculativeAssertionRejoinEnvelope context)) :
    PhysicalSpeculativeAssertionTailSegment context := by
  let boundary := speculativePhysicalResumeBoundary context inputMorkNodup
    preEnvelopeMorkNodup resultEnvelopeMorkNodup
  have first := speculativeNormalToRejoinSlice_ruleScoped_step context
  have second := speculativePhysicalNormalResult_ruleScoped_rejoin_step
    context inputMorkNodup preEnvelopeMorkNodup
  have third := physical_assertion_resume_ruleScoped_step_from
    (speculativePhysicalAssertionRejoinResult context)
    boundary.supportedExact
  let whole : CRuleScopedTrace .leaveInert 3
      (speculativeNormalToRejoinSlice context)
      (physicalAssertionResumeResultFrom
        (speculativePhysicalAssertionRejoinResult context)) :=
    .step first (.step second (.step third .refl))
  exact
    { resumeBoundary := boundary
      resumeStep := third
      wholeTrace := whole
      wholeNativeTypeTrace := whole.toNativeTypeTrace }

theorem speculativeResumeSpace_exact_physical_match
    (context : RejoinContext) :
    PhysicalExactCompressedAssertionResumeFor
      speculativeScannerRuntimeRuleBundle context
      (speculativeResumeSpace context) := by
  apply physical_exact_assertion_resume_for_of_reflective
    speculativeScannerRuntimeRuleBundle context
    (speculativeResumeSpace_nodup context)
    (speculativeResumeSpace_mork_nodup context)
    (by simp [speculativeResumeSpace, resumeMatchSliceFor])
  exact canonical_exact_compressed_assertion_resume_for
    speculativeScannerRuntimeRuleBundle context

/-- The canonical compiler-selected slice is an instance of the reusable
physical intermediate boundary. -/
def canonicalPhysicalSpeculativeResumeBoundary (context : RejoinContext) :
    PhysicalSpeculativeResumeBoundary context
      (speculativeResumeSpace context) := by
  refine
    { listNodup := speculativeResumeSpace_nodup context
      morkNodup := speculativeResumeSpace_mork_nodup context
      directivePresent := by
        simp [speculativeResumeSpace, resumeMatchSliceFor]
      resumeLive := ?_
      captureLive := ?_
      supportedExact := speculativeResumeSpace_supported_exact context }
  · simp [speculativeResumeSpace, resumeMatchSliceFor,
      compressedAssertionResumeDirective, compressedAssertionResumeRule,
      RejoinContext.resumeRow]
  · intro row member
    simp only [speculativeResumeSpace, resumeMatchSliceFor,
      List.erase_cons_head]
    exact List.mem_cons_of_mem _ member

/-- The compiler-selected resume seam executes one actual MORK step and is
classified by the OSLF-generated native target. -/
def physical_speculative_resume_segment (context : RejoinContext) :
    PhysicalAssertionResumeScheduledSegmentFor
      speculativeScannerRuntimeRuleBundle context
      (speculativeResumeSpace context) :=
  (canonicalPhysicalSpeculativeResumeBoundary context).scheduledSegment

/-- Positive transformed control: physical resumption installs the terminal
continuation selected by the speculative compiler. -/
theorem physical_speculative_resume_installs_terminal
    (context : RejoinContext) :
    morkSupportContains
      (physicalAssertionResumeResultFrom (speculativeResumeSpace context))
      compressedSpeculativeTerminalRule = true := by
  exact (physical_speculative_resume_segment context).outputSupport
    compressedSpeculativeTerminalRule
    (speculative_terminal_mem_resume_output context)

#print axioms speculativeResumeSpace_nodup
#print axioms speculativeResumeSpace_mork_nodup
#print axioms speculativeResumeSpace_supported_exact
#print axioms speculativeNormalToRejoinSlice_nodup
#print axioms speculativeNormalToRejoinSlice_supported_exact
#print axioms speculativeNormalToRejoinSlice_selects_normal_result
#print axioms speculativeNormalToRejoinSlice_ruleScoped_step
#print axioms physical_speculative_normal_result_matcher_interface_exact
#print axioms physical_speculative_normal_result_exact
#print axioms speculativePhysicalNormalResult_preserves_rejoin_inputs
#print axioms speculativePhysicalNormalResult_rows_within_envelope
#print axioms speculativeNormalResultEnvelope_supported_exact
#print axioms speculativeNormalResultEnvelope_nodup
#print axioms speculativePhysicalNormalResult_outputs_exact
#print axioms speculativePhysicalNormalResult_exact_rejoin
#print axioms speculativePhysicalNormalResult_rejoin_inputs_exact
#print axioms speculativePhysicalNormalResult_rejoin_matcher_interface_exact
#print axioms speculativePhysicalNormalResult_supported_exact
#print axioms speculativePhysicalAssertionRejoinResult_rows_within_envelope
#print axioms speculativePhysicalAssertionRejoinResult_outputs_exact
#print axioms speculativePhysicalAssertionRejoinResult_supported_exact
#print axioms speculativePhysicalNormalResult_selects_rejoin
#print axioms speculativePhysicalNormalResult_ruleScoped_rejoin_step
#print axioms physical_normal_result_preserves_speculative_capture_rows
#print axioms physical_normal_result_then_rejoin_preserves_speculative_capture_rows
#print axioms physical_assertion_rejoin_preserves_speculative_capture_rows
#print axioms physical_assertion_rejoin_preserves_speculative_capture_rows_live
#print axioms speculativePhysicalResumeBoundary
#print axioms PhysicalSpeculativeResumeBoundary.exactPhysicalMatch
#print axioms PhysicalSpeculativeResumeBoundary.scheduledSegment
#print axioms physical_speculative_assertion_tail_segment
#print axioms speculativeResumeSpace_exact_physical_match
#print axioms canonicalPhysicalSpeculativeResumeBoundary
#print axioms physical_speculative_resume_segment
#print axioms physical_speculative_resume_installs_terminal

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalSpeculativeResume
