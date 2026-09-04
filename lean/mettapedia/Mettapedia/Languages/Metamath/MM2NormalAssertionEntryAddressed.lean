import Mettapedia.Languages.Metamath.MM2NormalAddressSegment

/-!
# Address-parametric normal assertion entry

The normal assertion-entry rules do not inspect the representation of proof
or stack addresses.  This module instantiates those authored rules at an
arbitrary `NormalAddressSegment`, preserving the ordinary and compressed
address disciplines without duplicating the verifier semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem stagedAdd_contains_of_row
    (rows : List Subst) (substitution : Subst) (template candidate : Atom)
    (rowMember : substitution ∈ rows)
    (instantiates : instantiateTemplateAtom? substitution template =
      some candidate) :
    candidate ∈ rows.foldl
      (stageReflectiveSupportSink (.add template)) [] := by
  have stagePreserves : ∀ (remaining : List Subst) (staged : List Atom),
      candidate ∈ staged →
      candidate ∈ remaining.foldl
        (stageReflectiveSupportSink (.add template)) staged := by
    intro remaining
    induction remaining with
    | nil =>
        intro staged member
        exact member
    | cons head tail induction =>
        intro staged member
        apply induction
        simp only [stageReflectiveSupportSink, Sink.atom]
        split
        · exact member
        · simp only [insertSupport]
          split
          · exact member
          · exact List.mem_append_left _ member
  suffices containsOfRow : ∀ (remaining : List Subst) (staged : List Atom),
      substitution ∈ remaining →
      candidate ∈ remaining.foldl
        (stageReflectiveSupportSink (.add template)) staged by
    exact containsOfRow rows [] rowMember
  intro remaining
  induction remaining with
  | nil =>
      intro staged member
      simp at member
  | cons head tail induction =>
      intro staged member
      simp only [List.mem_cons] at member
      simp only [List.foldl_cons]
      rcases member with rfl | member
      · apply stagePreserves tail
          (stageReflectiveSupportSink (.add template) staged substitution)
        simp only [stageReflectiveSupportSink, Sink.atom]
        rw [instantiates]
        by_cases present : candidate ∈ staged
        · simp [insertSupport, present]
        · simp [insertSupport, present]
      · exact induction
          (stageReflectiveSupportSink (.add template) staged head) member

def normalAssertionPopRowAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String)
    (hypothesisCursor stackCursor : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-pop", scopeOwner, proofOwner,
      segment.currentProof, segment.nextProof, stringAtom assertionLabel,
      natAtom hypothesisCursor, segment.stackAddress stackCursor]

def normalAssertionBindRowAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase : Nat) :
    Atom :=
  .expression
    [.symbol "mm-assertion-bind", scopeOwner, proofOwner,
      segment.currentProof, segment.nextProof, stringAtom assertionLabel,
      natAtom nextHypothesisPosition, natAtom hypothesisEnd,
      segment.stackAddress nextStackPosition,
      segment.stackAddress stackBase]

def normalAssertionHypothesisSuccessorRowAt (scopeOwner : Atom)
    (assertionLabel : String) (previousHypothesis hypothesisCursor : Nat) :
    Atom :=
  .expression
    [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
      stringAtom assertionLabel, natAtom previousHypothesis,
      natAtom hypothesisCursor]

def normalAssertionStackSuccessorRowAt (proofOwner : Atom)
    (segment : NormalAddressSegment) (previousStack stackCursor : Nat) : Atom :=
  .expression
    [.symbol "mm-index-successor", proofOwner,
      segment.stackAddress previousStack, segment.stackAddress stackCursor]

def normalAssertionStartPhaseAtomsAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) : List Atom :=
  [normalAssertionStartRule,
   .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner,
      segment.currentProof, segment.stackAddress stackTop],
   segment.linkedLabelRow proofOwner assertion.label,
   assertionHeaderRow scopeOwner assertionPosition assertion]

def normalAssertionStartPhaseSpaceAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) : Space :=
  (normalAssertionStartPhaseAtomsAt scopeOwner proofOwner segment stackTop
    assertionPosition assertion).toFinset

private theorem normalAssertionStartPhaseAtomsAt_nodup
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackTop assertionPosition : Nat) (assertion : SourceAssertion) :
    (normalAssertionStartPhaseAtomsAt scopeOwner proofOwner segment stackTop
      assertionPosition assertion).Nodup := by
  cases assertion
  all_goals
    simp [normalAssertionStartPhaseAtomsAt, normalAssertionStartRule,
      NormalAddressSegment.linkedLabelRow, assertionHeaderRow]

private theorem normalAssertionStartPhaseAtomsAt_supported
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackTop assertionPosition : Nat) (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
        (normalAssertionStartPhaseAtomsAt scopeOwner proofOwner segment stackTop
          assertionPosition assertion) =
      [normalAssertionStartDirective] := by
  cases assertion
  all_goals rfl

theorem normalAssertionStartPhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackTop assertionPosition : Nat) (assertion : SourceAssertion) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionStartPhaseSpaceAt scopeOwner proofOwner segment
            stackTop assertionPosition assertion)) =
      some normalAssertionStartDirective := by
  let atoms := normalAssertionStartPhaseAtomsAt scopeOwner proofOwner segment
    stackTop assertionPosition assertion
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionStartDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionStartDirective
    (normalAssertionStartPhaseAtomsAt_nodup scopeOwner proofOwner segment
      stackTop assertionPosition assertion)
    (normalAssertionStartPhaseAtomsAt_supported scopeOwner proofOwner segment
      stackTop assertionPosition assertion)

private def normalAssertionStartSubstitutionAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackTop assertionPosition : Nat) (assertion : SourceAssertion) : Subst :=
  [("hyp-end", natAtom assertion.hypotheses.length),
   ("assertion-position", natAtom assertionPosition),
   ("label", stringAtom assertion.label),
   ("next-pc", segment.nextProof),
   ("top", segment.stackAddress stackTop),
   ("pc", segment.currentProof),
   ("proof", proofOwner), ("scope", scopeOwner)]

private def normalAssertionStartPatternsAt : List Atom :=
  [.expression
      [.symbol "mm-normal-control", .var "scope", .var "proof",
        .var "pc", .var "top"],
   .expression
      [.symbol "mm-linked-row", stringAtom "normal-proof-label",
        .var "proof", .var "pc", .var "next-pc", .var "label"],
   .expression
      [.symbol "mm-assertion-header", .var "scope",
        .var "assertion-position", .var "label", .var "hyp-end"]]

private def normalAssertionStartPopTemplateAt : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "hyp-end", .var "top"]

private theorem normalAssertionStartMatchRowAt_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackTop assertionPosition : Nat) (assertion : SourceAssertion) :
    normalAssertionStartSubstitutionAt scopeOwner proofOwner segment stackTop
        assertionPosition assertion ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionStartPhaseSpaceAt scopeOwner proofOwner segment
            stackTop assertionPosition assertion)
          normalAssertionStartRule)
        normalAssertionStartDirective.rule.input).map Prod.fst := by
  let control : Atom :=
    .expression
      [.symbol "mm-normal-control", scopeOwner, proofOwner,
        segment.currentProof, segment.stackAddress stackTop]
  let proofRow := segment.linkedLabelRow proofOwner assertion.label
  let header := assertionHeaderRow scopeOwner assertionPosition assertion
  let read := readCopyAtom
    (normalAssertionStartPhaseSpaceAt scopeOwner proofOwner segment stackTop
      assertionPosition assertion) normalAssertionStartRule
  let afterControl : Subst :=
    [("top", segment.stackAddress stackTop),
     ("pc", segment.currentProof), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let afterProof : Subst :=
    [("label", stringAtom assertion.label),
     ("next-pc", segment.nextProof),
     ("top", segment.stackAddress stackTop),
     ("pc", segment.currentProof), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let finalRow := normalAssertionStartSubstitutionAt scopeOwner proofOwner
    segment stackTop assertionPosition assertion
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionStartPhaseSpaceAt scopeOwner proofOwner
        segment stackTop assertionPosition assertion) : atom ∈ read := by
    by_cases equal : atom = normalAssertionStartRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have controlMem : control ∈ read := by
    apply readMember
    simp [control, normalAssertionStartPhaseSpaceAt,
      normalAssertionStartPhaseAtomsAt]
  have proofRowMem : proofRow ∈ read := by
    apply readMember
    simp [proofRow, normalAssertionStartPhaseSpaceAt,
      normalAssertionStartPhaseAtomsAt]
  have headerMem : header ∈ read := by
    apply readMember
    simp [header, normalAssertionStartPhaseSpaceAt,
      normalAssertionStartPhaseAtomsAt]
  have matchControl :
      matchAtom [] (normalAssertionStartPatternsAt[0]'(by decide)) control =
        some afterControl := by
    simp [normalAssertionStartPatternsAt, control, afterControl, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchProof :
      matchAtom afterControl
          (normalAssertionStartPatternsAt[1]'(by decide)) proofRow =
        some afterProof := by
    have matchTag :
        matchAtom afterControl (stringAtom "normal-proof-label")
            (stringAtom "normal-proof-label") = some afterControl := by
      exact groundAtom_matchAtom_self afterControl
        (stringAtom "normal-proof-label") (by simp)
    simp [normalAssertionStartPatternsAt, afterControl, afterProof, proofRow,
      NormalAddressSegment.linkedLabelRow, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchTag]
  have matchHeader :
      matchAtom afterProof
          (normalAssertionStartPatternsAt[2]'(by decide)) header =
        some finalRow := by
    cases assertion
    simp [normalAssertionStartPatternsAt, afterProof, finalRow,
      normalAssertionStartSubstitutionAt, header, assertionHeaderRow,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {control, proofRow, header}), ?_, rfl⟩
  have inputExact : normalAssertionStartDirective.rule.input =
      .compat (mkPattern normalAssertionStartPatternsAt) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, normalAssertionStartPatternsAt, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterControl, control),
    matchOneInSpace_mem [] _ read control controlMem afterControl
      matchControl, ?_⟩
  refine ⟨(afterProof, proofRow),
    matchOneInSpace_mem afterControl _ read proofRow proofRowMem afterProof
      matchProof, ?_⟩
  refine ⟨(finalRow, header),
    matchOneInSpace_mem afterProof _ read header headerMem finalRow
      matchHeader, ?_⟩
  simp [finalRow, control, proofRow, header]

theorem normalAssertionStartPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackTop assertionPosition : Nat) (assertion : SourceAssertion) :
    let source := normalAssertionStartPhaseSpaceAt scopeOwner proofOwner
      segment stackTop assertionPosition assertion
    let target := fireReflectiveSourceExecFact source
      normalAssertionStartDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionPopRowAt scopeOwner proofOwner segment assertion.label
        assertion.hypotheses.length stackTop ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionStartPhaseAt_selects_directive scopeOwner proofOwner
          segment stackTop assertionPosition assertion))
  · let source := normalAssertionStartPhaseSpaceAt scopeOwner proofOwner
      segment stackTop assertionPosition assertion
    let rows := (matchInputSpec []
      (readCopyAtom source normalAssertionStartDirective.atom)
      normalAssertionStartDirective.rule.input).map Prod.fst
    let substitution := normalAssertionStartSubstitutionAt scopeOwner
      proofOwner segment stackTop assertionPosition assertion
    have rowMember : substitution ∈ rows := by
      simpa [source, rows, substitution, normalAssertionStartDirective] using
        normalAssertionStartMatchRowAt_mem scopeOwner proofOwner segment
          stackTop assertionPosition assertion
    have instantiates :
        instantiateTemplateAtom? substitution
            normalAssertionStartPopTemplateAt =
          some (normalAssertionPopRowAt scopeOwner proofOwner segment
            assertion.label assertion.hypotheses.length stackTop) := by
      cases assertion
      all_goals rfl
    have staged := stagedAdd_contains_of_row rows substitution
      normalAssertionStartPopTemplateAt
      (normalAssertionPopRowAt scopeOwner proofOwner segment assertion.label
        assertion.hypotheses.length stackTop) rowMember instantiates
    have sinksExact : normalAssertionStartDirective.rule.tmpl.sinks =
        [.remove
          (.expression
            [.symbol "mm-normal-control", .var "scope", .var "proof",
              .var "pc", .var "top"]),
         .add normalAssertionStartPopTemplateAt] := by
      rfl
    simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sinksExact, reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

/-! ## Backward stack-suffix walk -/

private def normalAssertionPopLocationAt : Atom :=
  .expression [.symbol "02", .symbol "mm-normal-assertion-pop"]

private def normalAssertionPopPatternsAt : List Atom :=
  [.expression
      [.symbol "exec", normalAssertionPopLocationAt,
        .var "self-input", .var "self-output"],
   .expression
      [.symbol "mm-assertion-pop", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label",
        .var "hyp-cursor", .var "stack-cursor"],
   .expression
      [.symbol "mm-assertion-hypothesis-successor", .var "scope",
        .var "label", .var "previous-hyp", .var "hyp-cursor"],
   .expression
      [.symbol "mm-index-successor", .var "proof",
        .var "previous-stack", .var "stack-cursor"]]

private def normalAssertionPopInputAt : Atom :=
  .expression (.symbol "," :: normalAssertionPopPatternsAt)

private def normalAssertionPopSelfTemplateAt : Atom :=
  .expression
    [.symbol "exec", normalAssertionPopLocationAt,
      .var "self-input", .var "self-output"]

private def normalAssertionPopCurrentTemplateAt : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "hyp-cursor", .var "stack-cursor"]

private def normalAssertionPopPreviousTemplateAt : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "previous-hyp", .var "previous-stack"]

private def normalAssertionPopOutputAt : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", normalAssertionPopSelfTemplateAt],
      .expression [.symbol "-", normalAssertionPopCurrentTemplateAt],
      .expression [.symbol "+", normalAssertionPopPreviousTemplateAt]]

def normalAssertionPopPhaseAtomsAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    List Atom :=
  [normalAssertionPopRule,
   normalAssertionPopRowAt scopeOwner proofOwner segment assertionLabel
     hypothesisCursor stackCursor,
   normalAssertionHypothesisSuccessorRowAt scopeOwner assertionLabel
     previousHypothesis hypothesisCursor,
   normalAssertionStackSuccessorRowAt proofOwner segment previousStack
     stackCursor]

def normalAssertionPopPhaseSpaceAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    Space :=
  (normalAssertionPopPhaseAtomsAt scopeOwner proofOwner segment assertionLabel
    previousHypothesis hypothesisCursor previousStack stackCursor).toFinset

private theorem normalAssertionPopPhaseAtomsAt_nodup
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    (normalAssertionPopPhaseAtomsAt scopeOwner proofOwner segment
      assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor).Nodup := by
  simp [normalAssertionPopPhaseAtomsAt, normalAssertionPopRule,
    normalAssertionPopRowAt, normalAssertionHypothesisSuccessorRowAt,
    normalAssertionStackSuccessorRowAt]

private theorem normalAssertionPopPhaseAtomsAt_supported
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    cSupportedSourceExecFacts
        (normalAssertionPopPhaseAtomsAt scopeOwner proofOwner segment
          assertionLabel previousHypothesis hypothesisCursor previousStack
          stackCursor) =
      [normalAssertionPopDirective] := by
  rfl

theorem normalAssertionPopPhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionPopPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel previousHypothesis hypothesisCursor previousStack
            stackCursor)) =
      some normalAssertionPopDirective := by
  let atoms := normalAssertionPopPhaseAtomsAt scopeOwner proofOwner segment
    assertionLabel previousHypothesis hypothesisCursor previousStack
    stackCursor
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionPopDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionPopDirective
    (normalAssertionPopPhaseAtomsAt_nodup scopeOwner proofOwner segment
      assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor)
    (normalAssertionPopPhaseAtomsAt_supported scopeOwner proofOwner segment
      assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor)

private def normalAssertionPopSubstitutionAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    Subst :=
  [("previous-stack", segment.stackAddress previousStack),
   ("previous-hyp", natAtom previousHypothesis),
   ("stack-cursor", segment.stackAddress stackCursor),
   ("hyp-cursor", natAtom hypothesisCursor),
   ("label", stringAtom assertionLabel),
   ("next-pc", segment.nextProof),
   ("pc", segment.currentProof), ("proof", proofOwner),
   ("scope", scopeOwner), ("self-output", normalAssertionPopOutputAt),
   ("self-input", normalAssertionPopInputAt)]

private theorem normalAssertionPopMatchRowAt_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    normalAssertionPopSubstitutionAt scopeOwner proofOwner segment
        assertionLabel previousHypothesis hypothesisCursor previousStack
        stackCursor ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionPopPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel previousHypothesis hypothesisCursor previousStack
            stackCursor)
          normalAssertionPopRule)
        normalAssertionPopDirective.rule.input).map Prod.fst := by
  let current := normalAssertionPopRowAt scopeOwner proofOwner segment
    assertionLabel hypothesisCursor stackCursor
  let hypothesisSuccessor := normalAssertionHypothesisSuccessorRowAt
    scopeOwner assertionLabel previousHypothesis hypothesisCursor
  let stackSuccessor := normalAssertionStackSuccessorRowAt proofOwner segment
    previousStack stackCursor
  let read := readCopyAtom
    (normalAssertionPopPhaseSpaceAt scopeOwner proofOwner segment
      assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor) normalAssertionPopRule
  let afterSelf : Subst :=
    [("self-output", normalAssertionPopOutputAt),
     ("self-input", normalAssertionPopInputAt)]
  let afterCurrent : Subst :=
    [("stack-cursor", segment.stackAddress stackCursor),
     ("hyp-cursor", natAtom hypothesisCursor),
     ("label", stringAtom assertionLabel),
     ("next-pc", segment.nextProof),
     ("pc", segment.currentProof), ("proof", proofOwner),
     ("scope", scopeOwner), ("self-output", normalAssertionPopOutputAt),
     ("self-input", normalAssertionPopInputAt)]
  let afterHypothesis : Subst :=
    ("previous-hyp", natAtom previousHypothesis) :: afterCurrent
  let finalRow := normalAssertionPopSubstitutionAt scopeOwner proofOwner
    segment assertionLabel previousHypothesis hypothesisCursor previousStack
    stackCursor
  have ruleExact : normalAssertionPopRule =
      .expression
        [.symbol "exec", normalAssertionPopLocationAt,
          normalAssertionPopInputAt, normalAssertionPopOutputAt] := by
    rfl
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionPopPhaseSpaceAt scopeOwner proofOwner
        segment assertionLabel previousHypothesis hypothesisCursor previousStack
        stackCursor) : atom ∈ read := by
    by_cases equal : atom = normalAssertionPopRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : normalAssertionPopRule ∈ read := by
    apply readMember
    simp [normalAssertionPopPhaseSpaceAt, normalAssertionPopPhaseAtomsAt]
  have currentMem : current ∈ read := by
    apply readMember
    simp [current, normalAssertionPopPhaseSpaceAt,
      normalAssertionPopPhaseAtomsAt]
  have hypothesisSuccessorMem : hypothesisSuccessor ∈ read := by
    apply readMember
    simp [hypothesisSuccessor, normalAssertionPopPhaseSpaceAt,
      normalAssertionPopPhaseAtomsAt]
  have stackSuccessorMem : stackSuccessor ∈ read := by
    apply readMember
    simp [stackSuccessor, normalAssertionPopPhaseSpaceAt,
      normalAssertionPopPhaseAtomsAt]
  have matchLocation :
      matchAtom [] normalAssertionPopLocationAt normalAssertionPopLocationAt =
        some [] := by
    simp [normalAssertionPopLocationAt, matchAtom, matchAtom.matchAtomList]
  have matchSelf :
      matchAtom [] normalAssertionPopSelfTemplateAt normalAssertionPopRule =
        some afterSelf := by
    rw [ruleExact]
    simp [normalAssertionPopSelfTemplateAt, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchLocation]
  have matchCurrent :
      matchAtom afterSelf normalAssertionPopCurrentTemplateAt current =
        some afterCurrent := by
    simp [normalAssertionPopCurrentTemplateAt, current,
      normalAssertionPopRowAt, afterSelf, afterCurrent, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesisSuccessor :
      matchAtom afterCurrent (normalAssertionPopPatternsAt[2]'(by decide))
          hypothesisSuccessor = some afterHypothesis := by
    simp [normalAssertionPopPatternsAt, afterCurrent, afterHypothesis,
      hypothesisSuccessor, normalAssertionHypothesisSuccessorRowAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStackSuccessor :
      matchAtom afterHypothesis (normalAssertionPopPatternsAt[3]'(by decide))
          stackSuccessor = some finalRow := by
    simp [normalAssertionPopPatternsAt, afterHypothesis, afterCurrent, finalRow,
      normalAssertionPopSubstitutionAt, stackSuccessor,
      normalAssertionStackSuccessorRowAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {normalAssertionPopRule, current, hypothesisSuccessor, stackSuccessor}),
    ?_, rfl⟩
  have inputExact : normalAssertionPopDirective.rule.input =
      .compat (mkPattern normalAssertionPopPatternsAt) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, normalAssertionPopPatternsAt, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalAssertionPopRule),
    matchOneInSpace_mem [] _ read normalAssertionPopRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterCurrent, current),
    matchOneInSpace_mem afterSelf _ read current currentMem afterCurrent
      matchCurrent, ?_⟩
  refine ⟨(afterHypothesis, hypothesisSuccessor),
    matchOneInSpace_mem afterCurrent _ read hypothesisSuccessor
      hypothesisSuccessorMem afterHypothesis matchHypothesisSuccessor, ?_⟩
  refine ⟨(finalRow, stackSuccessor),
    matchOneInSpace_mem afterHypothesis _ read stackSuccessor
      stackSuccessorMem finalRow matchStackSuccessor, ?_⟩
  simp [finalRow, current, hypothesisSuccessor, stackSuccessor]

theorem normalAssertionPopPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    let source := normalAssertionPopPhaseSpaceAt scopeOwner proofOwner segment
      assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor
    let target := fireReflectiveSourceExecFact source
      normalAssertionPopDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionPopRowAt scopeOwner proofOwner segment assertionLabel
        previousHypothesis previousStack ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionPopPhaseAt_selects_directive scopeOwner proofOwner
          segment assertionLabel previousHypothesis hypothesisCursor
          previousStack stackCursor))
  · let source := normalAssertionPopPhaseSpaceAt scopeOwner proofOwner
      segment assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor
    let rows := (matchInputSpec []
      (readCopyAtom source normalAssertionPopDirective.atom)
      normalAssertionPopDirective.rule.input).map Prod.fst
    let substitution := normalAssertionPopSubstitutionAt scopeOwner proofOwner
      segment assertionLabel previousHypothesis hypothesisCursor previousStack
      stackCursor
    have rowMember : substitution ∈ rows := by
      simpa [source, rows, substitution, normalAssertionPopDirective] using
        normalAssertionPopMatchRowAt_mem scopeOwner proofOwner segment
          assertionLabel previousHypothesis hypothesisCursor previousStack
          stackCursor
    have instantiates :
        instantiateTemplateAtom? substitution
            normalAssertionPopPreviousTemplateAt =
          some (normalAssertionPopRowAt scopeOwner proofOwner segment
            assertionLabel previousHypothesis previousStack) := by
      rfl
    have staged := stagedAdd_contains_of_row rows substitution
      normalAssertionPopPreviousTemplateAt
      (normalAssertionPopRowAt scopeOwner proofOwner segment assertionLabel
        previousHypothesis previousStack) rowMember instantiates
    have sinksExact : normalAssertionPopDirective.rule.tmpl.sinks =
        [.add normalAssertionPopSelfTemplateAt,
         .remove normalAssertionPopCurrentTemplateAt,
         .add normalAssertionPopPreviousTemplateAt] := by
      rfl
    simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sinksExact, reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

/-! ## Bind-fold initialization -/

private def normalAssertionBeginPatternsAt : List Atom :=
  [.expression
      [.symbol "mm-assertion-pop", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label", natAtom 0,
        .var "stack-base"],
   .expression
      [.symbol "mm-assertion-header", .var "scope",
        .var "assertion-position", .var "label", .var "hyp-end"]]

private def normalAssertionBeginBindTemplateAt : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label", natAtom 0,
      .var "hyp-end", .var "stack-base", .var "stack-base"]

def normalAssertionBeginPhaseAtomsAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) : List Atom :=
  [normalAssertionBeginRule,
   normalAssertionPopRowAt scopeOwner proofOwner segment assertion.label 0
     stackBase,
   assertionHeaderRow scopeOwner assertionPosition assertion]

def normalAssertionBeginPhaseSpaceAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) : Space :=
  (normalAssertionBeginPhaseAtomsAt scopeOwner proofOwner segment stackBase
    assertionPosition assertion).toFinset

private theorem normalAssertionBeginPhaseAtomsAt_nodup
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) :
    (normalAssertionBeginPhaseAtomsAt scopeOwner proofOwner segment stackBase
      assertionPosition assertion).Nodup := by
  cases assertion
  all_goals
    simp [normalAssertionBeginPhaseAtomsAt, normalAssertionBeginRule,
      normalAssertionPopRowAt, assertionHeaderRow]

private theorem normalAssertionBeginPhaseAtomsAt_supported
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
        (normalAssertionBeginPhaseAtomsAt scopeOwner proofOwner segment
          stackBase assertionPosition assertion) =
      [normalAssertionBeginDirective] := by
  cases assertion
  all_goals rfl

theorem normalAssertionBeginPhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner segment
            stackBase assertionPosition assertion)) =
      some normalAssertionBeginDirective := by
  let atoms := normalAssertionBeginPhaseAtomsAt scopeOwner proofOwner segment
    stackBase assertionPosition assertion
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionBeginDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionBeginDirective
    (normalAssertionBeginPhaseAtomsAt_nodup scopeOwner proofOwner segment
      stackBase assertionPosition assertion)
    (normalAssertionBeginPhaseAtomsAt_supported scopeOwner proofOwner segment
      stackBase assertionPosition assertion)

private def normalAssertionBeginSubstitutionAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) : Subst :=
  [("hyp-end", natAtom assertion.hypotheses.length),
   ("assertion-position", natAtom assertionPosition),
   ("stack-base", segment.stackAddress stackBase),
   ("label", stringAtom assertion.label),
   ("next-pc", segment.nextProof),
   ("pc", segment.currentProof), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalAssertionBeginMatchRowAt_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) :
    normalAssertionBeginSubstitutionAt scopeOwner proofOwner segment stackBase
        assertionPosition assertion ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner segment
            stackBase assertionPosition assertion)
          normalAssertionBeginRule)
        normalAssertionBeginDirective.rule.input).map Prod.fst := by
  let pop := normalAssertionPopRowAt scopeOwner proofOwner segment
    assertion.label 0 stackBase
  let header := assertionHeaderRow scopeOwner assertionPosition assertion
  let read := readCopyAtom
    (normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner segment stackBase
      assertionPosition assertion) normalAssertionBeginRule
  let afterPop : Subst :=
    [("stack-base", segment.stackAddress stackBase),
     ("label", stringAtom assertion.label),
     ("next-pc", segment.nextProof),
     ("pc", segment.currentProof), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let finalRow := normalAssertionBeginSubstitutionAt scopeOwner proofOwner
    segment stackBase assertionPosition assertion
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner
        segment stackBase assertionPosition assertion) : atom ∈ read := by
    by_cases equal : atom = normalAssertionBeginRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have popMem : pop ∈ read := by
    apply readMember
    simp [pop, normalAssertionBeginPhaseSpaceAt,
      normalAssertionBeginPhaseAtomsAt]
  have headerMem : header ∈ read := by
    apply readMember
    simp [header, normalAssertionBeginPhaseSpaceAt,
      normalAssertionBeginPhaseAtomsAt]
  have matchNatZero :
      matchAtom
          [("label", stringAtom assertion.label),
           ("next-pc", segment.nextProof),
           ("pc", segment.currentProof), ("proof", proofOwner),
           ("scope", scopeOwner)]
          (natAtom 0) (natAtom 0) =
        some
          [("label", stringAtom assertion.label),
           ("next-pc", segment.nextProof),
           ("pc", segment.currentProof), ("proof", proofOwner),
           ("scope", scopeOwner)] := by
    exact groundAtom_matchAtom_self _ (natAtom 0) (isGroundAtom_natAtom 0)
  have matchPop :
      matchAtom [] (normalAssertionBeginPatternsAt[0]'(by decide)) pop =
        some afterPop := by
    simp [normalAssertionBeginPatternsAt, pop, normalAssertionPopRowAt,
      afterPop, matchAtom, matchAtom.matchAtomList, Subst.lookup,
      matchNatZero]
  have matchHeader :
      matchAtom afterPop (normalAssertionBeginPatternsAt[1]'(by decide))
          header = some finalRow := by
    cases assertion
    simp [normalAssertionBeginPatternsAt, afterPop, finalRow,
      normalAssertionBeginSubstitutionAt, header, assertionHeaderRow,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {pop, header}), ?_, rfl⟩
  have inputExact : normalAssertionBeginDirective.rule.input =
      .compat (mkPattern normalAssertionBeginPatternsAt) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, normalAssertionBeginPatternsAt, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterPop, pop),
    matchOneInSpace_mem [] _ read pop popMem afterPop matchPop, ?_⟩
  refine ⟨(finalRow, header),
    matchOneInSpace_mem afterPop _ read header headerMem finalRow matchHeader,
    ?_⟩
  simp [finalRow, pop, header]

theorem normalAssertionBeginPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) :
    let source := normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner
      segment stackBase assertionPosition assertion
    let target := fireReflectiveSourceExecFact source
      normalAssertionBeginDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionBindRowAt scopeOwner proofOwner segment assertion.label 0
        assertion.hypotheses.length stackBase stackBase ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionBeginPhaseAt_selects_directive scopeOwner proofOwner
          segment stackBase assertionPosition assertion))
  · let source := normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner
      segment stackBase assertionPosition assertion
    let rows := (matchInputSpec []
      (readCopyAtom source normalAssertionBeginDirective.atom)
      normalAssertionBeginDirective.rule.input).map Prod.fst
    let substitution := normalAssertionBeginSubstitutionAt scopeOwner
      proofOwner segment stackBase assertionPosition assertion
    have rowMember : substitution ∈ rows := by
      simpa [source, rows, substitution, normalAssertionBeginDirective] using
        normalAssertionBeginMatchRowAt_mem scopeOwner proofOwner segment
          stackBase assertionPosition assertion
    have instantiates :
        instantiateTemplateAtom? substitution
            normalAssertionBeginBindTemplateAt =
          some (normalAssertionBindRowAt scopeOwner proofOwner segment
            assertion.label 0 assertion.hypotheses.length stackBase
            stackBase) := by
      cases assertion
      all_goals rfl
    have staged := stagedAdd_contains_of_row rows substitution
      normalAssertionBeginBindTemplateAt
      (normalAssertionBindRowAt scopeOwner proofOwner segment assertion.label
        0 assertion.hypotheses.length stackBase stackBase)
      rowMember instantiates
    have sinksExact : normalAssertionBeginDirective.rule.tmpl.sinks =
        [.remove
          (.expression
            [.symbol "mm-assertion-pop", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label", natAtom 0,
              .var "stack-base"]),
         .add normalAssertionBeginBindTemplateAt] := by
      rfl
    simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sinksExact, reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

/-! ## Exact finite entry trace -/

inductive AddressedAssertionPopTrace (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String) :
    Nat → Nat → Nat → Prop
  | nil (stackBase : Nat) :
      AddressedAssertionPopTrace scopeOwner proofOwner segment assertionLabel
        0 stackBase stackBase
  | succ (previousHypothesis previousStack stackBase : Nat)
      (nativeStep :
        let source := normalAssertionPopPhaseSpaceAt scopeOwner proofOwner
          segment assertionLabel previousHypothesis (previousHypothesis + 1)
          previousStack (previousStack + 1)
        let target := fireReflectiveSourceExecFact source
          normalAssertionPopDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalAssertionPopRowAt scopeOwner proofOwner segment assertionLabel
            previousHypothesis previousStack ∈ target)
      (tail : AddressedAssertionPopTrace scopeOwner proofOwner segment
        assertionLabel previousHypothesis previousStack stackBase) :
      AddressedAssertionPopTrace scopeOwner proofOwner segment assertionLabel
        (previousHypothesis + 1) (previousStack + 1) stackBase

theorem addressedAssertionPopTrace_exact
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisCount stackBase : Nat) :
    AddressedAssertionPopTrace scopeOwner proofOwner segment assertionLabel
      hypothesisCount (stackBase + hypothesisCount) stackBase := by
  induction hypothesisCount with
  | zero => exact .nil stackBase
  | succ previousHypothesis inductionHypothesis =>
      have nativeStep := normalAssertionPopPhaseAt_inhabits_target_native_type
        scopeOwner proofOwner segment assertionLabel previousHypothesis
        (previousHypothesis + 1) (stackBase + previousHypothesis)
        (stackBase + previousHypothesis + 1)
      exact AddressedAssertionPopTrace.succ
        (scopeOwner := scopeOwner) (proofOwner := proofOwner)
        (segment := segment) (assertionLabel := assertionLabel)
        previousHypothesis (stackBase + previousHypothesis) stackBase
        nativeStep inductionHypothesis

structure AddressedAssertionEntryTrace (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) : Prop where
  start :
    let source := normalAssertionStartPhaseSpaceAt scopeOwner proofOwner
      segment (stackBase + assertion.hypotheses.length) assertionPosition
      assertion
    let target := fireReflectiveSourceExecFact source
      normalAssertionStartDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionPopRowAt scopeOwner proofOwner segment assertion.label
        assertion.hypotheses.length
        (stackBase + assertion.hypotheses.length) ∈ target
  pop : AddressedAssertionPopTrace scopeOwner proofOwner segment
    assertion.label assertion.hypotheses.length
    (stackBase + assertion.hypotheses.length) stackBase
  begin :
    let source := normalAssertionBeginPhaseSpaceAt scopeOwner proofOwner
      segment stackBase assertionPosition assertion
    let target := fireReflectiveSourceExecFact source
      normalAssertionBeginDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionBindRowAt scopeOwner proofOwner segment assertion.label 0
        assertion.hypotheses.length stackBase stackBase ∈ target

theorem addressedAssertionEntryTrace_exact
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (stackBase assertionPosition : Nat) (assertion : SourceAssertion) :
    AddressedAssertionEntryTrace scopeOwner proofOwner segment stackBase
      assertionPosition assertion :=
  { start := normalAssertionStartPhaseAt_inhabits_target_native_type
      scopeOwner proofOwner segment
      (stackBase + assertion.hypotheses.length) assertionPosition assertion
    pop := addressedAssertionPopTrace_exact scopeOwner proofOwner segment
      assertion.label assertion.hypotheses.length stackBase
    begin := normalAssertionBeginPhaseAt_inhabits_target_native_type
      scopeOwner proofOwner segment stackBase assertionPosition assertion }

section AxiomAudit

#print axioms normalAssertionStartPhaseAt_selects_directive
#print axioms normalAssertionStartPhaseAt_inhabits_target_native_type
#print axioms normalAssertionPopPhaseAt_inhabits_target_native_type
#print axioms normalAssertionBeginPhaseAt_inhabits_target_native_type
#print axioms addressedAssertionPopTrace_exact
#print axioms addressedAssertionEntryTrace_exact

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
