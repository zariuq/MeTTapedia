import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinSquare
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd

/-!
# Normal-result to compressed-rejoin boundary

The compressed assertion adapter sends one assertion to the shared normal
machine.  This module proves the return direction: the transformed authored
normal-result rule consumes the exact body result, publishes the corresponding
normal control and stack rows, and restores the captured assertion-rejoin
directive.  The compact rejoin context is constructed from the same source
parameters, so the two stages cannot disagree about occurrences or indices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinSquare
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Exact transformed normal-result rule -/

def normalResultCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-built", .var "proof", .var "pc",
      .expression
        [.symbol "mm-assertion-result-context", .var "scope",
          .var "next-pc", .var "label", .var "result-typecode",
          .var "stack-base", .var "next-top"],
      .var "result-body"]

def normalResultControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "next-pc", .var "next-top"]

def normalResultStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", .var "stack-base",
      .expression
        [.symbol "mm-formula", .var "result-typecode", .var "result-body"],
      .expression
        [.symbol "mm-assertion-occurrence", .var "pc", .var "label"]]

def normalResultReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-normal-dispatch", .var "proof"]

def normalResultCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-owned-runtime-rule", .symbol "assertion-rejoin",
      .var "compressed-assertion-rejoin-rule"]

def normalResultPatterns : List Atom :=
  [normalResultCursorTemplate, normalResultCaptureTemplate]

def normalResultSinks : List Sink :=
  [.remove normalResultCursorTemplate,
   .add normalResultControlTemplate,
   .add normalResultStackTemplate,
   .add normalResultReloadTemplate,
   .add (.var "compressed-assertion-rejoin-rule")]

private theorem normalResultRule_supported :
    (extractSupportedSourceExecFact
      normalAssertionResultCompleteRuleWithCompressedRejoin).isSome = true := by
  decide +kernel

def normalResultDirective : SourceExecFact :=
  (extractSupportedSourceExecFact
    normalAssertionResultCompleteRuleWithCompressedRejoin).get
      (by simpa using normalResultRule_supported)

theorem extract_normalResultRule_exact :
    extractSupportedSourceExecFact
        normalAssertionResultCompleteRuleWithCompressedRejoin =
      some normalResultDirective := by
  unfold normalResultDirective
  exact (Option.some_get (by simpa using normalResultRule_supported)).symm

theorem normalResult_input_exact :
    normalResultDirective.rule.input =
      .compat (mkPattern normalResultPatterns) := by
  decide +kernel

theorem normalResult_sinks_exact :
    normalResultDirective.rule.tmpl.sinks = normalResultSinks := by
  decide +kernel

/-! ## One source-indexed return boundary -/

structure NormalResultContext where
  scopeOwner : Atom
  proofOwner : Atom
  wordPosition : Nat
  remainingBytes : List UInt8
  index : Nat
  heapNext : Nat
  nodeNext : Nat
  stackBase : Nat
  assertionLabel : String
  resultTypecode : String
  resultBody : List Metamath.Verify.Sym

namespace NormalResultContext

def code (_context : NormalResultContext) (value : Nat) : Atom :=
  (CompressedIndexCode.ofNat value).atom

def bytes (context : NormalResultContext) : Atom :=
  listAtom natAtom (context.remainingBytes.map UInt8.toNat)

def pc (context : NormalResultContext) : Atom :=
  .expression
    [.symbol "mm-compressed-assertion-pc", natAtom context.wordPosition,
      context.bytes, context.code context.index]

def nextPC (context : NormalResultContext) : Atom :=
  .expression [.symbol "mm-compressed-assertion-done", context.pc]

def resultFormula (context : NormalResultContext) : Atom :=
  .expression
    [.symbol "mm-formula", stringAtom context.resultTypecode,
      listAtom runtimeSymAtom context.resultBody]

def rejoinContext (context : NormalResultContext) : RejoinContext where
  scopeOwner := context.scopeOwner
  proofOwner := context.proofOwner
  wordPosition := context.wordPosition
  remainingBytes := context.remainingBytes
  index := context.index
  heapNext := context.heapNext
  nodeNext := context.nodeNext
  stackBase := context.stackBase
  assertionLabel := context.assertionLabel
  resultFormula := context.resultFormula

def bodyBuiltRow (context : NormalResultContext) : Atom :=
  .expression
    [.symbol "mm-body-built", context.proofOwner, context.pc,
      .expression
        [.symbol "mm-assertion-result-context", context.scopeOwner,
          context.nextPC, stringAtom context.assertionLabel,
          stringAtom context.resultTypecode, context.code context.stackBase,
          context.code (context.stackBase + 1)],
      listAtom runtimeSymAtom context.resultBody]

def rejoinCaptureRow (_context : NormalResultContext) : Atom :=
  compressedOwnedRuntimeRuleRow "assertion-rejoin"
    compressedAssertionRejoinRule

def matchSlice (context : NormalResultContext) : List Atom :=
  [normalResultDirective.atom, context.bodyBuiltRow,
   context.rejoinCaptureRow]

def rows (context : NormalResultContext) : List Subst :=
  (Conformance.Computable.cmatchInputSpec [] context.matchSlice
    normalResultDirective.rule.input).map Prod.fst

end NormalResultContext

/-! ## Exact symbolic match and publication -/

private def normalResultBodySubst (context : NormalResultContext) : Subst :=
  [("result-body", listAtom runtimeSymAtom context.resultBody),
   ("next-top", context.code (context.stackBase + 1)),
   ("stack-base", context.code context.stackBase),
   ("result-typecode", stringAtom context.resultTypecode),
   ("label", stringAtom context.assertionLabel),
   ("next-pc", context.nextPC), ("scope", context.scopeOwner),
   ("pc", context.pc), ("proof", context.proofOwner)]

private def normalResultFinalSubst (context : NormalResultContext) : Subst :=
  [("compressed-assertion-rejoin-rule", compressedAssertionRejoinRule)] ++
    normalResultBodySubst context

private theorem normalResult_body_match (context : NormalResultContext) :
    Conformance.Computable.cmatchAtom [] normalResultCursorTemplate
      context.bodyBuiltRow = some (normalResultBodySubst context) := by
  cases context
  simp [normalResultBodySubst, NormalResultContext.bodyBuiltRow,
    NormalResultContext.pc, NormalResultContext.nextPC,
    NormalResultContext.bytes, NormalResultContext.code,
    normalResultCursorTemplate, Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList, Subst.lookup]

private theorem normalResult_capture_match (context : NormalResultContext) :
    Conformance.Computable.cmatchAtom (normalResultBodySubst context)
      normalResultCaptureTemplate context.rejoinCaptureRow =
        some (normalResultFinalSubst context) := by
  have fresh :
      (normalResultBodySubst context).lookup
          "compressed-assertion-rejoin-rule" = none := by
    cases context
    rfl
  simp only [normalResultCaptureTemplate,
    NormalResultContext.rejoinCaptureRow, compressedOwnedRuntimeRuleRow,
    Conformance.Computable.cmatchAtom,
    Conformance.Computable.cmatchAtomList]
  simp [fresh, normalResultFinalSubst]

private theorem cmatchPattern_go_cons_of_selected
    {space : List Atom} {pattern : Atom} {patterns : List Atom}
    {substitutionIn substitutionMid substitutionOut : Subst}
    {consumedIn consumedOut : List Atom} {concrete : Atom}
    (present : concrete ∈ space)
    (matched : Conformance.Computable.cmatchAtom substitutionIn pattern
      concrete = some substitutionMid)
    (continued : (substitutionOut, consumedOut) ∈
      Conformance.Computable.cmatchPattern.go space patterns substitutionMid
        (concrete :: consumedIn)) :
    (substitutionOut, consumedOut) ∈
      Conformance.Computable.cmatchPattern.go space (pattern :: patterns)
        substitutionIn consumedIn := by
  simp only [Conformance.Computable.cmatchPattern.go, List.mem_flatMap]
  refine ⟨(substitutionMid, concrete), ?_, continued⟩
  rw [List.mem_filterMap]
  exact ⟨concrete, present, by rw [matched]; rfl⟩

private theorem normalResult_final_subst_in_rows
    (context : NormalResultContext) :
    normalResultFinalSubst context ∈ context.rows := by
  unfold NormalResultContext.rows
  rw [normalResult_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(normalResultFinalSubst context,
    [context.rejoinCaptureRow, context.bodyBuiltRow]), ?_, rfl⟩
  unfold normalResultPatterns
  apply cmatchPattern_go_cons_of_selected (concrete := context.bodyBuiltRow)
  · simp [NormalResultContext.matchSlice]
  · exact normalResult_body_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.rejoinCaptureRow)
  · simp [NormalResultContext.matchSlice]
  · exact normalResult_capture_match context
  simp [Conformance.Computable.cmatchPattern.go]

private theorem normalResult_final_subst_instantiates
    (context : NormalResultContext) :
    instantiateTemplateAtom? (normalResultFinalSubst context)
          normalResultControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateTemplateAtom? (normalResultFinalSubst context)
          normalResultStackTemplate =
        some context.rejoinContext.returnedStackRow ∧
      instantiateTemplateAtom? (normalResultFinalSubst context)
          normalResultReloadTemplate =
        some (normalAssertionReloadAtom context.proofOwner) ∧
      instantiateTemplateAtom? (normalResultFinalSubst context)
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule := by
  cases context
  simp [normalResultFinalSubst, normalResultBodySubst,
    instantiateTemplateAtom?, templateCovered, templatesCovered,
    applySubst, applySubst.applySubstList, Subst.lookup,
    normalResultControlTemplate, normalResultStackTemplate,
    normalResultReloadTemplate, NormalResultContext.rejoinContext,
    NormalResultContext.resultFormula, NormalResultContext.pc,
    NormalResultContext.nextPC, NormalResultContext.bytes,
    NormalResultContext.code, RejoinContext.returnedControlRow,
    RejoinContext.returnedStackRow, RejoinContext.occurrence,
    RejoinContext.pc, RejoinContext.nextPC, RejoinContext.bytes,
    RejoinContext.code, compressedAssertionOccurrenceSurface,
    normalAssertionReloadAtom, CompressedIndexCode.atom,
    compressedIndexCodeAtom, natAtom]

def ExactNormalResultRejoin (context : NormalResultContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom :: space.erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst,
    instantiateTemplateAtom? substitution normalResultControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateTemplateAtom? substitution normalResultStackTemplate =
        some context.rejoinContext.returnedStackRow ∧
      instantiateTemplateAtom? substitution normalResultReloadTemplate =
        some (normalAssertionReloadAtom context.proofOwner) ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule

theorem exact_normal_result_rejoin_of_live_rows
    (context : NormalResultContext) (space : List Atom)
    (bodyBuilt : context.bodyBuiltRow ∈
      space.erase normalResultDirective.atom)
    (capture : context.rejoinCaptureRow ∈
      space.erase normalResultDirective.atom) :
    ExactNormalResultRejoin context space := by
  refine ⟨normalResultFinalSubst context, ?_,
    normalResult_final_subst_instantiates context⟩
  rw [normalResult_input_exact]
  simp only [Conformance.Computable.cmatchInputSpec,
    Conformance.Computable.cmatchPattern, mkPattern, List.mem_map]
  refine ⟨(normalResultFinalSubst context,
    [context.rejoinCaptureRow, context.bodyBuiltRow]), ?_, rfl⟩
  unfold normalResultPatterns
  apply cmatchPattern_go_cons_of_selected (concrete := context.bodyBuiltRow)
  · exact List.mem_cons_of_mem _ bodyBuilt
  · exact normalResult_body_match context
  apply cmatchPattern_go_cons_of_selected
    (concrete := context.rejoinCaptureRow)
  · exact List.mem_cons_of_mem _ capture
  · exact normalResult_capture_match context
  simp [Conformance.Computable.cmatchPattern.go]

theorem canonical_exact_normal_result_rejoin
    (context : NormalResultContext) :
    ExactNormalResultRejoin context context.matchSlice := by
  refine ⟨normalResultFinalSubst context, ?_,
    normalResult_final_subst_instantiates context⟩
  change normalResultFinalSubst context ∈ context.rows
  exact normalResult_final_subst_in_rows context

private theorem normalResultSinks_control_split :
    normalResultSinks =
      [.remove normalResultCursorTemplate] ++
      .add normalResultControlTemplate ::
        [.add normalResultStackTemplate, .add normalResultReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem normalResultSinks_stack_split :
    normalResultSinks =
      [.remove normalResultCursorTemplate, .add normalResultControlTemplate] ++
      .add normalResultStackTemplate ::
        [.add normalResultReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem normalResultSinks_reload_split :
    normalResultSinks =
      [.remove normalResultCursorTemplate, .add normalResultControlTemplate,
       .add normalResultStackTemplate] ++
      .add normalResultReloadTemplate ::
        [.add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

theorem normal_result_fire_publishes_rejoin_boundary
    (context : NormalResultContext) (space : List Atom)
    (matched : ExactNormalResultRejoin context space) :
    context.rejoinContext.returnedControlRow ∈
        cFireReflectiveSourceExecFact space normalResultDirective ∧
      context.rejoinContext.returnedStackRow ∈
        cFireReflectiveSourceExecFact space normalResultDirective ∧
      normalAssertionReloadAtom context.proofOwner ∈
        cFireReflectiveSourceExecFact space normalResultDirective ∧
      compressedAssertionRejoinRule ∈
        cFireReflectiveSourceExecFact space normalResultDirective := by
  rcases matched with
    ⟨substitution, rowMember, control, stack, reload, rejoin⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [normalResult_sinks_exact]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [normalResultSinks_control_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember control (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [normalResultSinks_stack_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember stack (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl <;> exact ⟨_, rfl⟩)
  · rw [normalResultSinks_reload_split]
    exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row _ _ _ _ _ _
      substitution rowMember reload (by
        intro sink sinkMember
        simp only [List.mem_singleton] at sinkMember
        subst sink
        exact ⟨_, rfl⟩)
  · exact mem_cApplyReflectiveSinkBatch_append_add_of_row _ _
      [.remove normalResultCursorTemplate, .add normalResultControlTemplate,
       .add normalResultStackTemplate, .add normalResultReloadTemplate]
      (.var "compressed-assertion-rejoin-rule")
      compressedAssertionRejoinRule substitution rowMember rejoin

private theorem normalResultSinks_preserve_expression_head
    (rows : List Subst) (candidateHead : String) (candidateTail : List Atom)
    (notBody : "mm-body-built" ≠ candidateHead) :
    ∀ sink ∈ normalResultSinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ rows,
            instantiateTemplateAtom? substitution authored ≠
              some (.expression (.symbol candidateHead :: candidateTail)) := by
  intro sink member
  simp only [normalResultSinks, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨normalResultCursorTemplate, rfl,
      fun substitution _ => by
        unfold normalResultCursorTemplate
        apply instantiateTemplateAtom?_expression_symbol_head_ne
        exact notBody⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem normal_result_fire_preserves_expression_head
    (space : List Atom) (candidateHead : String) (candidateTail : List Atom)
    (notBody : "mm-body-built" ≠ candidateHead)
    (present : .expression (.symbol candidateHead :: candidateTail) ∈
      space.erase normalResultDirective.atom) :
    .expression (.symbol candidateHead :: candidateTail) ∈
      cFireReflectiveSourceExecFact space normalResultDirective := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [normalResult_sinks_exact]
  exact mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    ((Conformance.Computable.cmatchInputSpec []
      (normalResultDirective.atom :: space.erase normalResultDirective.atom)
      normalResultDirective.rule.input).map Prod.fst)
    (normalResultSinks_preserve_expression_head _ candidateHead candidateTail
      notBody) present

/-! ## Threaded normal-result to rejoin match -/

def normalToRejoinSlice (context : NormalResultContext) : List Atom :=
  normalResultDirective.atom ::
    ([context.bodyBuiltRow, context.rejoinCaptureRow,
      context.rejoinContext.contextRow,
      context.rejoinContext.normalStackSuccessorRow,
      context.rejoinContext.nodeSuccessorRow,
      context.rejoinContext.normalLabelRow,
      context.rejoinContext.resumeCaptureRow] ++
        compressedScannerRuleCaptureRows)

def normalToRejoinAfter (context : NormalResultContext) : List Atom :=
  cFireReflectiveSourceExecFact (normalToRejoinSlice context)
    normalResultDirective

def normalToRejoinExtraRows (context : NormalResultContext) : List Atom :=
  [context.rejoinContext.contextRow,
   context.rejoinContext.normalStackSuccessorRow,
   context.rejoinContext.nodeSuccessorRow,
   context.rejoinContext.normalLabelRow,
   context.rejoinContext.resumeCaptureRow] ++
    compressedScannerRuleCaptureRows

private theorem normalToRejoin_read_eq (context : NormalResultContext) :
    normalResultDirective.atom ::
        (normalToRejoinSlice context).erase normalResultDirective.atom =
      context.matchSlice ++ normalToRejoinExtraRows context := by
  unfold normalToRejoinSlice
  rw [List.erase_cons_head]
  rfl

private theorem normalToRejoinExtraRows_never_match
    (context : NormalResultContext) (substitution : Subst) (pattern : Atom)
    (patternMember : pattern ∈ normalResultPatterns) (row : Atom)
    (rowMember : row ∈ normalToRejoinExtraRows context) :
    Conformance.Computable.cmatchAtom substitution pattern row = none := by
  simp only [normalResultPatterns, List.mem_cons, List.not_mem_nil,
    or_false] at patternMember
  simp only [normalToRejoinExtraRows, List.mem_append] at rowMember
  rcases rowMember with fixed | capture
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases patternMember with rfl | rfl <;>
      rcases fixed with rfl | rfl | rfl | rfl | rfl <;>
      simp [normalResultCursorTemplate, normalResultCaptureTemplate,
        RejoinContext.contextRow, RejoinContext.normalStackSuccessorRow,
        RejoinContext.nodeSuccessorRow, RejoinContext.normalLabelRow,
        RejoinContext.resumeCaptureRow, compressedIndexSuccessorRow,
        compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList]
  · simp only [compressedScannerRuleCaptureRows, List.mem_cons,
      List.not_mem_nil, or_false] at capture
    rcases patternMember with rfl | rfl <;>
      rcases capture with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;>
      simp [normalResultCursorTemplate, normalResultCaptureTemplate,
        compressedOwnedRuntimeRuleRow, Conformance.Computable.cmatchAtom,
        Conformance.Computable.cmatchAtomList]

private theorem normalToRejoin_matcher_eq_canonical
    (context : NormalResultContext) :
    Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input =
      Conformance.Computable.cmatchInputSpec [] context.matchSlice
        normalResultDirective.rule.input := by
  rw [normalToRejoin_read_eq, normalResult_input_exact]
  exact Conformance.Computable.cmatchPattern_append_of_right_never_matches
    [] context.matchSlice (normalToRejoinExtraRows context)
      (mkPattern normalResultPatterns)
      (normalToRejoinExtraRows_never_match context)

private theorem canonical_normal_result_rows_exact
    (context : NormalResultContext) :
    context.rows = [normalResultFinalSubst context] := by
  cases context
  rfl

private theorem normalToRejoin_rows_exact
    (context : NormalResultContext) :
    (Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst =
      [normalResultFinalSubst context] := by
  rw [normalToRejoin_matcher_eq_canonical]
  exact canonical_normal_result_rows_exact context

/-- Every matcher row at the threaded normal-result boundary consumes and
publishes the same source-indexed interface.  This is the representation-
neutral inversion theorem used by physical MORK execution; it exposes the
consequence of the private singleton calculation without exposing its
implementation substitution. -/
theorem normalToRejoin_matcher_interface_exact
    (context : NormalResultContext) {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
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
  rw [normalToRejoin_rows_exact] at member
  simp only [List.mem_singleton] at member
  subst substitution
  have outputs := normalResult_final_subst_instantiates context
  refine ⟨?_, outputs⟩
  cases context
  simp [normalResultFinalSubst, normalResultBodySubst,
    instantiateTemplateAtom?, templateCovered, templatesCovered,
    applySubst, applySubst.applySubstList, Subst.lookup,
    normalResultCursorTemplate, NormalResultContext.bodyBuiltRow,
    NormalResultContext.pc, NormalResultContext.nextPC,
    NormalResultContext.bytes, NormalResultContext.code,
    CompressedIndexCode.atom, compressedIndexCodeAtom, natAtom]

private theorem normalResult_template_supportSet :
    ReflectiveSupportSetTemplate normalResultDirective.rule.tmpl := by
  unfold ReflectiveSupportSetTemplate
  rw [normalResult_sinks_exact]
  intro sink member
  simp only [normalResultSinks, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [ReflectiveSupportSetSink]

private theorem normalToRejoin_live_exact (context : NormalResultContext) :
    (normalToRejoinSlice context).erase normalResultDirective.atom =
      [context.bodyBuiltRow, context.rejoinCaptureRow,
       context.rejoinContext.contextRow,
       context.rejoinContext.normalStackSuccessorRow,
       context.rejoinContext.nodeSuccessorRow,
       context.rejoinContext.normalLabelRow,
       context.rejoinContext.resumeCaptureRow] ++
        compressedScannerRuleCaptureRows := by
  unfold normalToRejoinSlice
  rw [List.erase_cons_head]

private theorem normalResultDirective_ne_nonexec_expression
    (head : String) (tail : List Atom) (headNe : head ≠ "exec") :
    normalResultDirective.atom ≠
      .expression (.symbol head :: tail) := by
  intro equal
  have decoded := congrArg extractSupportedSourceExecFact equal
  change extractSupportedSourceExecFact
      normalAssertionResultCompleteRuleWithCompressedRejoin = _ at decoded
  rw [extract_normalResultRule_exact] at decoded
  simp [extractSupportedSourceExecFact, extractRawExecFact, headNe] at decoded

/-- The source-indexed three-stage frame has no duplicate atoms.  This makes
consumption of one scheduled directive exact: no second copy can remain live
after the firing. -/
theorem normalToRejoinSlice_nodup (context : NormalResultContext) :
    (normalToRejoinSlice context).Nodup := by
  simp [normalToRejoinSlice, NormalResultContext.bodyBuiltRow,
    NormalResultContext.rejoinCaptureRow, RejoinContext.contextRow,
    RejoinContext.normalStackSuccessorRow, RejoinContext.nodeSuccessorRow,
    RejoinContext.normalLabelRow, RejoinContext.resumeCaptureRow,
    compressedIndexSuccessorRow, compressedScannerRuleCaptureRows,
    compressedOwnedRuntimeRuleRow,
    normalResultDirective_ne_nonexec_expression]

/-- Add/remove execution preserves duplicate freedom across the transformed
normal-result step. -/
theorem normalToRejoinAfter_nodup (context : NormalResultContext) :
    (normalToRejoinAfter context).Nodup := by
  exact cFireReflectiveSourceExecFact_nodup _ _
    normalResult_template_supportSet (normalToRejoinSlice_nodup context)

private theorem normalToRejoin_live_resume_capabilities
    (context : NormalResultContext) :
    AssertionResumeCapabilities compressedAssertionResumeRule
      ((normalToRejoinSlice context).erase normalResultDirective.atom) := by
  rw [normalToRejoin_live_exact]
  intro carrier member payload captured
  simp only [List.mem_append] at member
  rcases member with fixed | scanner
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [AssertionResumeCapture, NormalResultContext.bodyBuiltRow,
        decodeCompressedExecutableCapture] at captured
    · simp [AssertionResumeCapture, NormalResultContext.rejoinCaptureRow,
        compressedOwnedRuntimeRuleRow,
        decodeCompressedExecutableCapture] at captured
    · simp [AssertionResumeCapture, RejoinContext.contextRow,
        decodeCompressedExecutableCapture] at captured
    · simp [AssertionResumeCapture, RejoinContext.normalStackSuccessorRow,
        decodeCompressedExecutableCapture] at captured
    · simp [AssertionResumeCapture, RejoinContext.nodeSuccessorRow,
        compressedIndexSuccessorRow,
        decodeCompressedExecutableCapture] at captured
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

private theorem normalResult_added_resume_capabilities
    (context : NormalResultContext) :
    ReflectiveAddedAtomsWithin
      (fun carrier => ∀ payload,
        AssertionResumeCapture carrier payload →
          payload = compressedAssertionResumeRule)
      ((Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst)
      normalResultDirective.rule.tmpl := by
  rw [normalToRejoin_rows_exact]
  intro atom added payload captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq, substitution,
      substitutionMember, instantiated⟩
  simp only [List.mem_singleton] at substitutionMember
  subst substitution
  rw [normalResult_sinks_exact] at sinkMember
  simp only [normalResultSinks, List.mem_cons, List.not_mem_nil,
    or_false] at sinkMember
  obtain ⟨control, stack, reload, rejoin⟩ :=
    normalResult_final_subst_instantiates context
  rcases sinkMember with rfl | rfl | rfl | rfl | rfl
  · cases sinkEq
  · cases sinkEq
    rw [control] at instantiated
    injection instantiated with atomEq
    subst atom
    simp [AssertionResumeCapture, RejoinContext.returnedControlRow,
      decodeCompressedExecutableCapture] at captured
  · cases sinkEq
    rw [stack] at instantiated
    injection instantiated with atomEq
    subst atom
    simp [AssertionResumeCapture, RejoinContext.returnedStackRow,
      decodeCompressedExecutableCapture] at captured
  · cases sinkEq
    rw [reload] at instantiated
    injection instantiated with atomEq
    subst atom
    simp [AssertionResumeCapture, normalAssertionReloadAtom,
      decodeCompressedExecutableCapture] at captured
  · cases sinkEq
    rw [rejoin] at instantiated
    injection instantiated with atomEq
    subst atom
    simp [AssertionResumeCapture, compressedAssertionRejoinRule,
      decodeCompressedExecutableCapture] at captured

/-- The normal-result firing preserves the exact source-owned assertion-resume
capability.  In particular, the later rejoin matcher cannot obtain a resume
rule from an unrelated capture family. -/
theorem normalToRejoinAfter_resume_capabilities
    (context : NormalResultContext) :
    AssertionResumeCapabilities compressedAssertionResumeRule
      (normalToRejoinAfter context) := by
  change AtomsWithin
    (fun carrier => ∀ payload,
      AssertionResumeCapture carrier payload →
        payload = compressedAssertionResumeRule)
    (cApplyReflectiveTemplate
      ((normalToRejoinSlice context).erase normalResultDirective.atom)
      ((Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst)
      normalResultDirective.rule.tmpl)
  exact cApplyReflectiveTemplate_atomsWithin _ _ _ _
    normalResult_template_supportSet
    (normalToRejoin_live_resume_capabilities context)
    (normalResult_added_resume_capabilities context)

private def SupportedExecAtomOnly (expected : SourceExecFact)
    (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate = expected

private theorem nonexec_expression_supportedOnly
    (expected : SourceExecFact) (head : String) (tail : List Atom)
    (headNe : head ≠ "exec") :
    SupportedExecAtomOnly expected
      (.expression (.symbol head :: tail)) := by
  intro candidate extracted
  simp [extractSupportedSourceExecFact, extractRawExecFact, headNe] at extracted

private theorem normalToRejoin_live_supportedOnly
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionRejoinDirective)
      ((normalToRejoinSlice context).erase normalResultDirective.atom) := by
  rw [normalToRejoin_live_exact]
  intro atom member
  simp only [List.mem_append] at member
  rcases member with fixed | capture
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · unfold NormalResultContext.bodyBuiltRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold NormalResultContext.rejoinCaptureRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold RejoinContext.contextRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold RejoinContext.normalStackSuccessorRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold RejoinContext.nodeSuccessorRow compressedIndexSuccessorRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold RejoinContext.normalLabelRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
    · unfold RejoinContext.resumeCaptureRow compressedOwnedRuntimeRuleRow
      exact nonexec_expression_supportedOnly _ _ _ (by decide)
  · simp only [compressedScannerRuleCaptureRows, List.mem_cons,
      List.not_mem_nil, or_false] at capture
    rcases capture with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;>
      unfold compressedOwnedRuntimeRuleRow <;>
      exact nonexec_expression_supportedOnly _ _ _ (by decide)

private theorem normalResult_added_supportedOnly
    (context : NormalResultContext) :
    ReflectiveAddedAtomsWithin
      (SupportedExecAtomOnly compressedAssertionRejoinDirective)
      ((Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst)
      normalResultDirective.rule.tmpl := by
  rw [normalToRejoin_rows_exact]
  intro atom added
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq, substitution,
      substitutionMember, instantiated⟩
  simp only [List.mem_singleton] at substitutionMember
  subst substitution
  rw [normalResult_sinks_exact] at sinkMember
  simp only [normalResultSinks, List.mem_cons, List.not_mem_nil,
    or_false] at sinkMember
  obtain ⟨control, stack, reload, rejoin⟩ :=
    normalResult_final_subst_instantiates context
  rcases sinkMember with rfl | rfl | rfl | rfl | rfl
  · cases sinkEq
  · cases sinkEq
    rw [control] at instantiated
    injection instantiated with atomEq
    subst atom
    unfold RejoinContext.returnedControlRow
    exact nonexec_expression_supportedOnly _ _ _ (by decide)
  · cases sinkEq
    rw [stack] at instantiated
    injection instantiated with atomEq
    subst atom
    unfold RejoinContext.returnedStackRow
    exact nonexec_expression_supportedOnly _ _ _ (by decide)
  · cases sinkEq
    rw [reload] at instantiated
    injection instantiated with atomEq
    subst atom
    unfold normalAssertionReloadAtom
    exact nonexec_expression_supportedOnly _ _ _ (by decide)
  · cases sinkEq
    rw [rejoin] at instantiated
    injection instantiated with atomEq
    subst atom
    intro candidate extracted
    rw [extract_compressedAssertionRejoinRule_exact] at extracted
    exact (Option.some.inj extracted).symm

/-- No executable directive other than the reconstructed assertion-rejoin
directive can occur after the normal-result firing.  This is the scheduler
fact needed for the second stage, proved without normalizing the full carrier. -/
theorem normalToRejoinAfter_supportedOnly
    (context : NormalResultContext) :
    AtomsWithin (SupportedExecAtomOnly compressedAssertionRejoinDirective)
      (normalToRejoinAfter context) := by
  change AtomsWithin (SupportedExecAtomOnly compressedAssertionRejoinDirective)
    (cApplyReflectiveTemplate
      ((normalToRejoinSlice context).erase normalResultDirective.atom)
      ((Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst)
      normalResultDirective.rule.tmpl)
  exact cApplyReflectiveTemplate_atomsWithin _ _ _ _
    normalResult_template_supportSet
    (normalToRejoin_live_supportedOnly context)
    (normalResult_added_supportedOnly context)

theorem normalToRejoinAfter_supported_unique
    (context : NormalResultContext) :
    ∀ candidate ∈ cSupportedSourceExecFacts (normalToRejoinAfter context),
      candidate = compressedAssertionRejoinDirective := by
  intro candidate member
  rcases List.mem_filterMap.mp member with
    ⟨atom, atomMember, extracted⟩
  exact normalToRejoinAfter_supportedOnly context atom atomMember candidate
    extracted

private theorem normalToRejoin_live_mem
    (context : NormalResultContext) {row : Atom}
    (member : row ∈
      [context.bodyBuiltRow, context.rejoinCaptureRow,
       context.rejoinContext.contextRow,
       context.rejoinContext.normalStackSuccessorRow,
       context.rejoinContext.nodeSuccessorRow,
       context.rejoinContext.normalLabelRow,
       context.rejoinContext.resumeCaptureRow]) :
    row ∈ (normalToRejoinSlice context).erase normalResultDirective.atom := by
  rw [normalToRejoin_live_exact]
  exact List.mem_append_left _ member

private theorem rejoin_live_of_ne
    {space : List Atom} {row : Atom}
    (notRejoin : row ≠ compressedAssertionRejoinDirective.atom)
    (member : row ∈ space) :
    row ∈ space.erase compressedAssertionRejoinDirective.atom :=
  (List.mem_erase_of_ne notRejoin).2 member

private theorem expression_head_ne_rejoin
    (candidateHead : String) (candidateTail : List Atom)
    (notExec : candidateHead ≠ "exec") :
    .expression (.symbol candidateHead :: candidateTail) ≠
      compressedAssertionRejoinDirective.atom := by
  unfold compressedAssertionRejoinDirective compressedAssertionRejoinRule
  simp [notExec]

theorem normal_result_fire_supplies_exact_compressed_rejoin
    (context : NormalResultContext) :
    ExactCompressedAssertionRejoin context.rejoinContext
      (normalToRejoinAfter context) := by
  have exactNormal : ExactNormalResultRejoin context
      (normalToRejoinSlice context) :=
    exact_normal_result_rejoin_of_live_rows context
      (normalToRejoinSlice context)
      (normalToRejoin_live_mem context (by simp))
      (normalToRejoin_live_mem context (by simp))
  have published := normal_result_fire_publishes_rejoin_boundary context
    (normalToRejoinSlice context) exactNormal
  have contextRow : context.rejoinContext.contextRow ∈
      normalToRejoinAfter context := by
    apply normal_result_fire_preserves_expression_head
      (normalToRejoinSlice context) "mm-compressed-assertion-context"
      [context.scopeOwner, context.proofOwner, natAtom context.wordPosition,
       context.bytes, context.pc, context.nextPC,
       stringAtom context.assertionLabel, context.code context.heapNext,
       context.code context.nodeNext]
      (by decide)
    change context.rejoinContext.contextRow ∈
      (normalToRejoinSlice context).erase normalResultDirective.atom
    exact normalToRejoin_live_mem context (by simp)
  have normalSuccessor : context.rejoinContext.normalStackSuccessorRow ∈
      normalToRejoinAfter context := by
    apply normal_result_fire_preserves_expression_head
      (normalToRejoinSlice context) "mm-index-successor"
      [context.proofOwner, context.code context.stackBase,
       context.code (context.stackBase + 1)]
      (by decide)
    change context.rejoinContext.normalStackSuccessorRow ∈
      (normalToRejoinSlice context).erase normalResultDirective.atom
    exact normalToRejoin_live_mem context (by simp)
  have nodeSuccessor : context.rejoinContext.nodeSuccessorRow ∈
      normalToRejoinAfter context := by
    apply normal_result_fire_preserves_expression_head
      (normalToRejoinSlice context) "mm-compressed-index-successor"
      [.expression [.symbol "mm-compressed-node-owner", context.proofOwner],
       context.code context.nodeNext, context.code (context.nodeNext + 1)]
      (by decide)
    change context.rejoinContext.nodeSuccessorRow ∈
      (normalToRejoinSlice context).erase normalResultDirective.atom
    exact normalToRejoin_live_mem context (by simp)
  have normalLabel : context.rejoinContext.normalLabelRow ∈
      normalToRejoinAfter context := by
    apply normal_result_fire_preserves_expression_head
      (normalToRejoinSlice context) "mm-linked-row"
      [stringAtom "normal-proof-label", context.proofOwner, context.pc,
       context.nextPC, stringAtom context.assertionLabel]
      (by decide)
    change context.rejoinContext.normalLabelRow ∈
      (normalToRejoinSlice context).erase normalResultDirective.atom
    exact normalToRejoin_live_mem context (by simp)
  have resumeCapture : context.rejoinContext.resumeCaptureRow ∈
      normalToRejoinAfter context := by
    apply normal_result_fire_preserves_expression_head
      (normalToRejoinSlice context) "mm-compressed-owned-runtime-rule"
      [.symbol "assertion-resume", compressedAssertionResumeRule]
      (by decide)
    change context.rejoinContext.resumeCaptureRow ∈
      (normalToRejoinSlice context).erase normalResultDirective.atom
    exact normalToRejoin_live_mem context (by simp)
  apply exact_compressed_assertion_rejoin_of_live_rows
  · apply rejoin_live_of_ne _ contextRow
    unfold RejoinContext.contextRow
    exact expression_head_ne_rejoin _ _ (by decide)
  · apply rejoin_live_of_ne _ published.1
    unfold RejoinContext.returnedControlRow
    exact expression_head_ne_rejoin _ _ (by decide)
  · apply rejoin_live_of_ne _ published.2.1
    unfold RejoinContext.returnedStackRow
    exact expression_head_ne_rejoin _ _ (by decide)
  · apply rejoin_live_of_ne _ normalSuccessor
    unfold RejoinContext.normalStackSuccessorRow
    exact expression_head_ne_rejoin _ _ (by decide)
  · apply rejoin_live_of_ne _ nodeSuccessor
    unfold RejoinContext.nodeSuccessorRow compressedIndexSuccessorRow
    exact expression_head_ne_rejoin _ _ (by decide)
  · apply rejoin_live_of_ne _ normalLabel
    unfold RejoinContext.normalLabelRow
    exact expression_head_ne_rejoin _ _ (by decide)
  · apply rejoin_live_of_ne _ resumeCapture
    unfold RejoinContext.resumeCaptureRow compressedOwnedRuntimeRuleRow
    exact expression_head_ne_rejoin _ _ (by decide)

theorem compressed_rejoin_supported_after_normal_result
    (context : NormalResultContext) :
    compressedAssertionRejoinDirective ∈
      cSupportedSourceExecFacts (normalToRejoinAfter context) := by
  have exactNormal : ExactNormalResultRejoin context
      (normalToRejoinSlice context) :=
    exact_normal_result_rejoin_of_live_rows context
      (normalToRejoinSlice context)
      (normalToRejoin_live_mem context (by simp))
      (normalToRejoin_live_mem context (by simp))
  have published := normal_result_fire_publishes_rejoin_boundary context
    (normalToRejoinSlice context) exactNormal
  exact List.mem_filterMap.mpr
    ⟨compressedAssertionRejoinRule, published.2.2.2,
      extract_compressedAssertionRejoinRule_exact⟩

theorem returned_stack_live_after_normal_result
    (context : NormalResultContext) :
    context.rejoinContext.returnedStackRow ∈
      (normalToRejoinAfter context).erase
        compressedAssertionRejoinDirective.atom := by
  have exactNormal : ExactNormalResultRejoin context
      (normalToRejoinSlice context) :=
    exact_normal_result_rejoin_of_live_rows context
      (normalToRejoinSlice context)
      (normalToRejoin_live_mem context (by simp))
      (normalToRejoin_live_mem context (by simp))
  have published := normal_result_fire_publishes_rejoin_boundary context
    (normalToRejoinSlice context) exactNormal
  apply rejoin_live_of_ne _ published.2.1
  unfold RejoinContext.returnedStackRow
  exact expression_head_ne_rejoin _ _ (by decide)

/-- The second, now fully reconstructed rejoin transition publishes the exact
compact successor interface.  This statement threads the actual output of the
normal-result directive into the actual input of the rejoin directive; it does
not rebuild an independent fixture between the two stages. -/
theorem normal_result_then_rejoin_publishes_compact_boundary
    (context : NormalResultContext) :
    ∀ row ∈ context.rejoinContext.outputRows,
      row ∈ cFireReflectiveSourceExecFact
        (normalToRejoinAfter context) compressedAssertionRejoinDirective :=
  compressed_assertion_rejoin_fire_adds_output_rows _ _
    (normal_result_fire_supplies_exact_compressed_rejoin context)

theorem canonical_normal_result_fire_publishes_rejoin_boundary
    (context : NormalResultContext) :
    context.rejoinContext.returnedControlRow ∈
        cFireReflectiveSourceExecFact context.matchSlice normalResultDirective ∧
      context.rejoinContext.returnedStackRow ∈
        cFireReflectiveSourceExecFact context.matchSlice normalResultDirective ∧
      normalAssertionReloadAtom context.proofOwner ∈
        cFireReflectiveSourceExecFact context.matchSlice normalResultDirective ∧
      compressedAssertionRejoinRule ∈
        cFireReflectiveSourceExecFact context.matchSlice normalResultDirective :=
  normal_result_fire_publishes_rejoin_boundary context context.matchSlice
    (canonical_exact_normal_result_rejoin context)

section AxiomAudit

#print axioms extract_normalResultRule_exact
#print axioms normalResult_input_exact
#print axioms normalResult_sinks_exact
#print axioms normalToRejoin_matcher_interface_exact
#print axioms exact_normal_result_rejoin_of_live_rows
#print axioms canonical_exact_normal_result_rejoin
#print axioms normal_result_fire_publishes_rejoin_boundary
#print axioms normal_result_fire_preserves_expression_head
#print axioms normalToRejoinSlice_nodup
#print axioms normalToRejoinAfter_nodup
#print axioms normalToRejoinAfter_resume_capabilities
#print axioms normalToRejoinAfter_supportedOnly
#print axioms normalToRejoinAfter_supported_unique
#print axioms normal_result_fire_supplies_exact_compressed_rejoin
#print axioms compressed_rejoin_supported_after_normal_result
#print axioms returned_stack_live_after_normal_result
#print axioms normal_result_then_rejoin_publishes_compact_boundary
#print axioms canonical_normal_result_fire_publishes_rejoin_boundary

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
