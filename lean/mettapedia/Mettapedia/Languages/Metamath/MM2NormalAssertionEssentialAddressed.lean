import Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed
import Mettapedia.Languages.Metamath.MM2NormalBodyMatchAddressed

/-!
# Address-parametric essential-hypothesis execution

One essential hypothesis starts the authored body matcher at the exact proof
address and completes back into the same assertion fold.  The source formula
comparison is supplied by `BodySubstitution`; the target trace does not invent
or retain a separate semantic witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalAssertionEssentialAddressed

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
open Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2NormalBodyMatchAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def normalAssertionEssentialContinuationRowAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-assertion-essential-complete", scopeOwner, proofOwner,
      segment.currentProof, segment.nextProof, stringAtom assertionLabel,
      natAtom nextHypothesisPosition, natAtom hypothesisEnd,
      segment.stackAddress nextStackPosition,
      segment.stackAddress stackBase, natAtom hypothesisPosition,
      childOccurrence]

def normalAssertionEssentialMatchRowAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom)
    (sourceBody actualBody : List Metamath.Verify.Sym) : Atom :=
  normalBodyMatchRowAt proofOwner segment.currentProof sourceBody actualBody
    (normalAssertionEssentialContinuationRowAt scopeOwner proofOwner segment
      assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
      stackBase hypothesisPosition childOccurrence)

@[simp] theorem normalAssertionEssentialContinuationRowAt_ordinary_exact
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    normalAssertionEssentialContinuationRowAt scopeOwner proofOwner
        (ordinarySuccessorSegment proofPosition) assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition (natAtom childOccurrence) =
      normalAssertionEssentialContinuationAtom scopeOwner proofOwner
        proofPosition (proofPosition + 1) assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition childOccurrence := by
  rfl

private def essentialPatterns : List Atom :=
  [.expression
      [.symbol "mm-assertion-bind", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label", .var "hyp-position",
        .var "hyp-end", .var "stack-position", .var "stack-base"],
   .expression
      [.symbol "mm-assertion-hypothesis", .var "scope", .var "label",
        .var "hyp-position",
        .expression
          [.symbol "mm-essential", .var "hyp-label",
            .expression
              [.symbol "mm-formula", .var "typecode",
                .var "source-body"]]],
   .expression
      [.symbol "mm-assertion-hypothesis-successor", .var "scope",
        .var "label", .var "hyp-position", .var "next-hyp-position"],
   .expression
      [.symbol "mm-index-successor", .var "proof",
        .var "stack-position", .var "next-stack-position"],
   .expression
      [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
        .expression
          [.symbol "mm-formula", .var "typecode", .var "actual-body"],
        .var "child-occurrence"]]

private def essentialMatchTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-body", .var "actual-body",
      .expression
        [.symbol "mm-assertion-essential-complete",
          .var "scope", .var "proof", .var "pc", .var "next-pc",
          .var "label", .var "next-hyp-position", .var "hyp-end",
          .var "next-stack-position", .var "stack-base",
          .var "hyp-position", .var "child-occurrence"]]

private theorem essential_input_exact :
    normalAssertionEssentialDirective.rule.input =
      .compat (mkPattern essentialPatterns) := by
  rfl

private theorem essential_sinks_exact :
    normalAssertionEssentialDirective.rule.tmpl.sinks =
      [.remove (essentialPatterns[0]'(by decide)),
        .remove (essentialPatterns[4]'(by decide)),
        .add essentialMatchTemplate] := by
  rfl

def normalAssertionEssentialPhaseAtomsAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Atom) : List Atom :=
  [normalAssertionEssentialRule,
   normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
      hypothesisPosition hypothesisEnd stackPosition stackBase,
   .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-essential", stringAtom hypothesisLabel,
            formulaAtom ⟨typecode, sourceBody⟩]],
   normalAssertionHypothesisSuccessorRowAt scopeOwner assertionLabel
      hypothesisPosition nextHypothesisPosition,
   normalAssertionStackSuccessorRowAt proofOwner segment stackPosition
      nextStackPosition,
   normalStackRowAt proofOwner (segment.stackAddress stackPosition)
      ⟨typecode, actualBody⟩ childOccurrence]

def normalAssertionEssentialPhaseSpaceAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Atom) : Space :=
  (normalAssertionEssentialPhaseAtomsAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    sourceBody actualBody childOccurrence).toFinset

@[simp] theorem normalAssertionEssentialPhaseAtomsAt_ordinary_exact
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    normalAssertionEssentialPhaseAtomsAt scopeOwner proofOwner
        (ordinarySuccessorSegment proofPosition) assertionLabel
        hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
        nextStackPosition stackBase hypothesisLabel typecode sourceBody
        actualBody (natAtom childOccurrence) =
      normalAssertionEssentialPhaseAtoms scopeOwner proofOwner proofPosition
        (proofPosition + 1) assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode sourceBody actualBody
        childOccurrence := by
  rfl

theorem normalAssertionEssentialPhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionEssentialPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel hypothesisPosition nextHypothesisPosition
            hypothesisEnd stackPosition nextStackPosition stackBase
            hypothesisLabel typecode sourceBody actualBody
            childOccurrence)) =
      some normalAssertionEssentialDirective := by
  let atoms := normalAssertionEssentialPhaseAtomsAt scopeOwner proofOwner
    segment assertionLabel hypothesisPosition nextHypothesisPosition
    hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
    typecode sourceBody actualBody childOccurrence
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionEssentialDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionEssentialDirective
    (by simp [atoms, normalAssertionEssentialPhaseAtomsAt,
      normalAssertionEssentialRule, normalAssertionBindRowAt,
      normalAssertionHypothesisSuccessorRowAt,
      normalAssertionStackSuccessorRowAt, normalStackRowAt])
    (by rfl)

private def essentialSubstitutionAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Atom) : Subst :=
  [("child-occurrence", childOccurrence),
   ("actual-body", listAtom runtimeSymAtom actualBody),
   ("next-stack-position", segment.stackAddress nextStackPosition),
   ("next-hyp-position", natAtom nextHypothesisPosition),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("typecode", stringAtom typecode),
   ("hyp-label", stringAtom hypothesisLabel),
   ("stack-base", segment.stackAddress stackBase),
   ("stack-position", segment.stackAddress stackPosition),
   ("hyp-end", natAtom hypothesisEnd),
   ("hyp-position", natAtom hypothesisPosition),
   ("label", stringAtom assertionLabel),
   ("next-pc", segment.nextProof), ("pc", segment.currentProof),
   ("proof", proofOwner), ("scope", scopeOwner)]

private theorem essentialMatchRowAt_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Atom) :
    essentialSubstitutionAt scopeOwner proofOwner segment assertionLabel
        hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
        nextStackPosition stackBase hypothesisLabel typecode sourceBody
        actualBody childOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionEssentialPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel hypothesisPosition nextHypothesisPosition
            hypothesisEnd stackPosition nextStackPosition stackBase
            hypothesisLabel typecode sourceBody actualBody childOccurrence)
          normalAssertionEssentialRule)
        normalAssertionEssentialDirective.rule.input).map Prod.fst := by
  let bind := normalAssertionBindRowAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition hypothesisEnd stackPosition stackBase
  let hypothesisRow : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-essential", stringAtom hypothesisLabel,
            formulaAtom ⟨typecode, sourceBody⟩]]
  let hypothesisSuccessor := normalAssertionHypothesisSuccessorRowAt
    scopeOwner assertionLabel hypothesisPosition nextHypothesisPosition
  let stackSuccessor := normalAssertionStackSuccessorRowAt proofOwner segment
    stackPosition nextStackPosition
  let stack := normalStackRowAt proofOwner
    (segment.stackAddress stackPosition) ⟨typecode, actualBody⟩
    childOccurrence
  let phase := normalAssertionEssentialPhaseSpaceAt scopeOwner proofOwner
    segment assertionLabel hypothesisPosition nextHypothesisPosition
    hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
    typecode sourceBody actualBody childOccurrence
  let read := readCopyAtom phase normalAssertionEssentialRule
  let afterBind : Subst :=
    [("stack-base", segment.stackAddress stackBase),
     ("stack-position", segment.stackAddress stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", segment.nextProof), ("pc", segment.currentProof),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let afterHypothesis : Subst :=
    [("source-body", listAtom runtimeSymAtom sourceBody),
     ("typecode", stringAtom typecode),
     ("hyp-label", stringAtom hypothesisLabel),
     ("stack-base", segment.stackAddress stackBase),
     ("stack-position", segment.stackAddress stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", segment.nextProof), ("pc", segment.currentProof),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let afterHypothesisSuccessor : Subst :=
    ("next-hyp-position", natAtom nextHypothesisPosition) :: afterHypothesis
  let afterStackSuccessor : Subst :=
    ("next-stack-position", segment.stackAddress nextStackPosition) ::
      afterHypothesisSuccessor
  let finalRow := essentialSubstitutionAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    sourceBody actualBody childOccurrence
  have readMember (atom : Atom) (member : atom ∈ phase) : atom ∈ read := by
    by_cases equal : atom = normalAssertionEssentialRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨equal, member⟩)
  have bindMem : bind ∈ read := by
    apply readMember
    simp [phase, bind, normalAssertionEssentialPhaseSpaceAt,
      normalAssertionEssentialPhaseAtomsAt]
  have hypothesisRowMem : hypothesisRow ∈ read := by
    apply readMember
    simp [phase, hypothesisRow, normalAssertionEssentialPhaseSpaceAt,
      normalAssertionEssentialPhaseAtomsAt, formulaAtom]
  have hypothesisSuccessorMem : hypothesisSuccessor ∈ read := by
    apply readMember
    simp [phase, hypothesisSuccessor, normalAssertionEssentialPhaseSpaceAt,
      normalAssertionEssentialPhaseAtomsAt]
  have stackSuccessorMem : stackSuccessor ∈ read := by
    apply readMember
    simp [phase, stackSuccessor, normalAssertionEssentialPhaseSpaceAt,
      normalAssertionEssentialPhaseAtomsAt]
  have stackMem : stack ∈ read := by
    apply readMember
    simp [phase, stack, normalAssertionEssentialPhaseSpaceAt,
      normalAssertionEssentialPhaseAtomsAt]
  have matchBind :
      matchAtom [] (essentialPatterns[0]'(by decide)) bind =
        some afterBind := by
    simp [essentialPatterns, bind, normalAssertionBindRowAt, afterBind,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesis :
      matchAtom afterBind (essentialPatterns[1]'(by decide)) hypothesisRow =
        some afterHypothesis := by
    simp [essentialPatterns, afterBind, afterHypothesis, hypothesisRow,
      formulaAtom, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesisSuccessor :
      matchAtom afterHypothesis (essentialPatterns[2]'(by decide))
          hypothesisSuccessor = some afterHypothesisSuccessor := by
    simp [essentialPatterns, afterHypothesis, afterHypothesisSuccessor,
      hypothesisSuccessor, normalAssertionHypothesisSuccessorRowAt,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchStackSuccessor :
      matchAtom afterHypothesisSuccessor (essentialPatterns[3]'(by decide))
          stackSuccessor = some afterStackSuccessor := by
    simp [essentialPatterns, afterHypothesisSuccessor, afterStackSuccessor,
      afterHypothesis, stackSuccessor, normalAssertionStackSuccessorRowAt,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchStack :
      matchAtom afterStackSuccessor (essentialPatterns[4]'(by decide)) stack =
        some finalRow := by
    simp [essentialPatterns, afterStackSuccessor,
      afterHypothesisSuccessor, afterHypothesis, finalRow,
      essentialSubstitutionAt, stack, normalStackRowAt, formulaAtom,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {bind, hypothesisRow, hypothesisSuccessor, stackSuccessor, stack}), ?_,
    rfl⟩
  rw [essential_input_exact]
  simp only [matchInputSpec, essentialPatterns, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterBind, bind),
    matchOneInSpace_mem [] _ read bind bindMem afterBind matchBind, ?_⟩
  refine ⟨(afterHypothesis, hypothesisRow),
    matchOneInSpace_mem afterBind _ read hypothesisRow hypothesisRowMem
      afterHypothesis matchHypothesis, ?_⟩
  refine ⟨(afterHypothesisSuccessor, hypothesisSuccessor),
    matchOneInSpace_mem afterHypothesis _ read hypothesisSuccessor
      hypothesisSuccessorMem afterHypothesisSuccessor
      matchHypothesisSuccessor, ?_⟩
  refine ⟨(afterStackSuccessor, stackSuccessor),
    matchOneInSpace_mem afterHypothesisSuccessor _ read stackSuccessor
      stackSuccessorMem afterStackSuccessor matchStackSuccessor, ?_⟩
  refine ⟨(finalRow, stack),
    matchOneInSpace_mem afterStackSuccessor _ read stack stackMem finalRow
      matchStack, ?_⟩
  simp [finalRow, bind, hypothesisRow, hypothesisSuccessor, stackSuccessor,
    stack]

theorem normalAssertionEssentialPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Atom) :
    let source := normalAssertionEssentialPhaseSpaceAt scopeOwner proofOwner
      segment assertionLabel hypothesisPosition nextHypothesisPosition
      hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
      typecode sourceBody actualBody childOccurrence
    let targetSpace := fireReflectiveSourceExecFact source
      normalAssertionEssentialDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType targetSpace).pred ∧
      normalAssertionEssentialMatchRowAt scopeOwner proofOwner segment
        assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
        stackBase hypothesisPosition childOccurrence sourceBody actualBody ∈
          targetSpace := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionEssentialPhaseAt_selects_directive scopeOwner
          proofOwner segment assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode sourceBody
          actualBody childOccurrence))
  · let rows := (matchInputSpec []
      (readCopyAtom
        (normalAssertionEssentialPhaseSpaceAt scopeOwner proofOwner segment
          assertionLabel hypothesisPosition nextHypothesisPosition
          hypothesisEnd stackPosition nextStackPosition stackBase
          hypothesisLabel typecode sourceBody actualBody childOccurrence)
        normalAssertionEssentialDirective.atom)
      normalAssertionEssentialDirective.rule.input).map Prod.fst
    let substitution := essentialSubstitutionAt scopeOwner proofOwner segment
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase hypothesisLabel typecode
      sourceBody actualBody childOccurrence
    have rowMember : substitution ∈ rows := by
      simpa [rows, substitution, normalAssertionEssentialDirective] using
        essentialMatchRowAt_mem scopeOwner proofOwner segment assertionLabel
          hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode sourceBody
          actualBody childOccurrence
    have instantiates :
        instantiateTemplateAtom? substitution essentialMatchTemplate =
          some (normalAssertionEssentialMatchRowAt scopeOwner proofOwner
            segment assertionLabel nextHypothesisPosition hypothesisEnd
            nextStackPosition stackBase hypothesisPosition childOccurrence
            sourceBody actualBody) := by
      rfl
    have staged := addressedStageAdd_contains_of_row rows substitution
      essentialMatchTemplate
      (normalAssertionEssentialMatchRowAt scopeOwner proofOwner segment
        assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
        stackBase hypothesisPosition childOccurrence sourceBody actualBody)
      rowMember instantiates
    simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      essential_sinks_exact, reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

/-! ## Essential completion -/

private def essentialCompletePattern : Atom :=
  .expression
    [.symbol "mm-assertion-essential-complete", .var "scope",
      .var "proof", .var "pc", .var "next-pc", .var "label",
      .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base",
      .var "hyp-position", .var "child-occurrence"]

private def essentialCompleteNextBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base"]

private def essentialCompleteChildTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-child", .var "proof", .var "pc",
      .var "hyp-position", .var "child-occurrence"]

private def essentialCompleteReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-normal-dispatch", .var "proof"]

private theorem essentialComplete_input_exact :
    normalAssertionEssentialCompleteDirective.rule.input =
      .compat (mkPattern [essentialCompletePattern]) := by
  rfl

private theorem essentialComplete_sinks_exact :
    normalAssertionEssentialCompleteDirective.rule.tmpl.sinks =
      [.remove essentialCompletePattern, .add essentialCompleteNextBindTemplate,
        .add essentialCompleteChildTemplate,
        .add essentialCompleteReloadTemplate] := by
  rfl

def normalAssertionEssentialCompletePhaseSpaceAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom) : Space :=
  [normalAssertionEssentialCompleteRule,
   normalAssertionEssentialContinuationRowAt scopeOwner proofOwner segment
     assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
     stackBase hypothesisPosition childOccurrence].toFinset

private def essentialCompleteSubstitutionAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom) : Subst :=
  [("child-occurrence", childOccurrence),
   ("hyp-position", natAtom hypothesisPosition),
   ("stack-base", segment.stackAddress stackBase),
   ("next-stack-position", segment.stackAddress nextStackPosition),
   ("hyp-end", natAtom hypothesisEnd),
   ("next-hyp-position", natAtom nextHypothesisPosition),
   ("label", stringAtom assertionLabel),
   ("next-pc", segment.nextProof), ("pc", segment.currentProof),
   ("proof", proofOwner), ("scope", scopeOwner)]

theorem normalAssertionEssentialCompletePhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionEssentialCompletePhaseSpaceAt scopeOwner proofOwner
            segment assertionLabel nextHypothesisPosition hypothesisEnd
            nextStackPosition stackBase hypothesisPosition
            childOccurrence)) =
      some normalAssertionEssentialCompleteDirective := by
  let atoms :=
    [normalAssertionEssentialCompleteRule,
     normalAssertionEssentialContinuationRowAt scopeOwner proofOwner segment
       assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
       stackBase hypothesisPosition childOccurrence]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionEssentialCompleteDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionEssentialCompleteDirective
    (by simp [atoms, normalAssertionEssentialCompleteRule,
      normalAssertionEssentialContinuationRowAt])
    (by rfl)

private theorem essentialCompleteRowAt_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom) :
    essentialCompleteSubstitutionAt scopeOwner proofOwner segment
        assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
        stackBase hypothesisPosition childOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionEssentialCompletePhaseSpaceAt scopeOwner proofOwner
            segment assertionLabel nextHypothesisPosition hypothesisEnd
            nextStackPosition stackBase hypothesisPosition childOccurrence)
          normalAssertionEssentialCompleteRule)
        normalAssertionEssentialCompleteDirective.rule.input).map Prod.fst := by
  let continuation := normalAssertionEssentialContinuationRowAt scopeOwner
    proofOwner segment assertionLabel nextHypothesisPosition hypothesisEnd
    nextStackPosition stackBase hypothesisPosition childOccurrence
  let substitution := essentialCompleteSubstitutionAt scopeOwner proofOwner
    segment assertionLabel nextHypothesisPosition hypothesisEnd
    nextStackPosition stackBase hypothesisPosition childOccurrence
  let read := readCopyAtom
    (normalAssertionEssentialCompletePhaseSpaceAt scopeOwner proofOwner
      segment assertionLabel nextHypothesisPosition hypothesisEnd
      nextStackPosition stackBase hypothesisPosition childOccurrence)
    normalAssertionEssentialCompleteRule
  have continuationMem : continuation ∈ read := by
    simp [read, readCopyAtom, consumeAtom, continuation,
      normalAssertionEssentialContinuationRowAt,
      normalAssertionEssentialCompletePhaseSpaceAt,
      normalAssertionEssentialCompleteRule]
  have matchContinuation :
      matchAtom [] essentialCompletePattern continuation =
        some substitution := by
    simp [essentialCompletePattern, continuation,
      normalAssertionEssentialContinuationRowAt, substitution,
      essentialCompleteSubstitutionAt, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {continuation}), ?_, rfl⟩
  rw [essentialComplete_input_exact]
  simp only [matchInputSpec, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(substitution, continuation),
    matchOneInSpace_mem [] _ read continuation continuationMem substitution
      matchContinuation, ?_⟩
  simp [substitution, continuation]

theorem normalAssertionEssentialCompletePhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition : Nat)
    (childOccurrence : Atom) :
    let source := normalAssertionEssentialCompletePhaseSpaceAt scopeOwner
      proofOwner segment assertionLabel nextHypothesisPosition hypothesisEnd
      nextStackPosition stackBase hypothesisPosition childOccurrence
    let targetSpace := fireReflectiveSourceExecFact source
      normalAssertionEssentialCompleteDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType targetSpace).pred ∧
      normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
            nextHypothesisPosition hypothesisEnd nextStackPosition stackBase ∈
          targetSpace ∧
        normalAssertionChildRowAt proofOwner segment.currentProof
              hypothesisPosition childOccurrence ∈ targetSpace ∧
          .expression
              [.symbol "mm-reload-normal-dispatch", proofOwner] ∈
            targetSpace := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionEssentialCompletePhaseAt_selects_directive scopeOwner
          proofOwner segment assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase hypothesisPosition
          childOccurrence))
  · let rows := (matchInputSpec []
      (readCopyAtom
        (normalAssertionEssentialCompletePhaseSpaceAt scopeOwner proofOwner
          segment assertionLabel nextHypothesisPosition hypothesisEnd
          nextStackPosition stackBase hypothesisPosition childOccurrence)
        normalAssertionEssentialCompleteDirective.atom)
      normalAssertionEssentialCompleteDirective.rule.input).map Prod.fst
    let substitution := essentialCompleteSubstitutionAt scopeOwner proofOwner
      segment assertionLabel nextHypothesisPosition hypothesisEnd
      nextStackPosition stackBase hypothesisPosition childOccurrence
    have rowMember : substitution ∈ rows := by
      simpa [rows, substitution, normalAssertionEssentialCompleteDirective]
        using essentialCompleteRowAt_mem scopeOwner proofOwner segment
          assertionLabel nextHypothesisPosition hypothesisEnd
          nextStackPosition stackBase hypothesisPosition childOccurrence
    have nextInstantiates :
        instantiateTemplateAtom? substitution
            essentialCompleteNextBindTemplate =
          some (normalAssertionBindRowAt scopeOwner proofOwner segment
            assertionLabel nextHypothesisPosition hypothesisEnd
            nextStackPosition stackBase) := by
      rfl
    have childInstantiates :
        instantiateTemplateAtom? substitution essentialCompleteChildTemplate =
          some (normalAssertionChildRowAt proofOwner segment.currentProof
            hypothesisPosition childOccurrence) := by
      rfl
    have reloadInstantiates :
        instantiateTemplateAtom? substitution essentialCompleteReloadTemplate =
          some (.expression
            [.symbol "mm-reload-normal-dispatch", proofOwner]) := by
      rfl
    have nextStaged := addressedStageAdd_contains_of_row rows substitution
      essentialCompleteNextBindTemplate
      (normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase)
      rowMember nextInstantiates
    have childStaged := addressedStageAdd_contains_of_row rows substitution
      essentialCompleteChildTemplate
      (normalAssertionChildRowAt proofOwner segment.currentProof
        hypothesisPosition childOccurrence) rowMember childInstantiates
    have reloadStaged := addressedStageAdd_contains_of_row rows substitution
      essentialCompleteReloadTemplate
      (.expression [.symbol "mm-reload-normal-dispatch", proofOwner])
      rowMember reloadInstantiates
    constructor
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        essentialComplete_sinks_exact, reflectiveSupportSinkProvider]
      exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_right _ (List.mem_toFinset.mpr nextStaged)))
    · constructor
      · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
          essentialComplete_sinks_exact, reflectiveSupportSinkProvider]
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ (List.mem_toFinset.mpr childStaged))
      · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
          essentialComplete_sinks_exact, reflectiveSupportSinkProvider]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

def AddressedEssentialHypothesisTrace
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel : String) (formula actual : ConstantHeadedFormula)
    (childOccurrence : Atom) (substitution : FiniteSubstitution) : Prop :=
  let continuation := normalAssertionEssentialContinuationRowAt scopeOwner
    proofOwner segment assertionLabel nextHypothesisPosition hypothesisEnd
    nextStackPosition stackBase hypothesisPosition childOccurrence
  let startPhase := normalAssertionEssentialPhaseSpaceAt scopeOwner proofOwner
    segment assertionLabel hypothesisPosition nextHypothesisPosition
    hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
    formula.typecode formula.body actual.body childOccurrence
  let startTarget := fireReflectiveSourceExecFact startPhase
    normalAssertionEssentialDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies startPhase
      (reflectiveSourceExecExactTargetNativeType startTarget).pred ∧
    normalAssertionEssentialMatchRowAt scopeOwner proofOwner segment
          assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
          stackBase hypothesisPosition childOccurrence formula.body
          actual.body ∈ startTarget ∧
      AddressedBodyMatchTrace proofOwner segment.currentProof continuation
          substitution formula.body actual.body ∧
        let completePhase := normalAssertionEssentialCompletePhaseSpaceAt
          scopeOwner proofOwner segment assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase hypothesisPosition
          childOccurrence
        let completeTarget := fireReflectiveSourceExecFact completePhase
          normalAssertionEssentialCompleteDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies
            completePhase
            (reflectiveSourceExecExactTargetNativeType completeTarget).pred ∧
          normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
                nextHypothesisPosition hypothesisEnd nextStackPosition
                stackBase ∈ completeTarget ∧
            normalAssertionChildRowAt proofOwner segment.currentProof
                  hypothesisPosition childOccurrence ∈ completeTarget ∧
              .expression
                  [.symbol "mm-reload-normal-dispatch", proofOwner] ∈
                completeTarget

theorem addressedEssentialHypothesisTrace_of_semantics
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel : String) (formula actual : ConstantHeadedFormula)
    (childOccurrence : Atom) (substitution : FiniteSubstitution)
    (typecodeEqual : actual.typecode = formula.typecode)
    (semantics : FormulaSubstitutionSemantics substitution formula actual) :
    AddressedEssentialHypothesisTrace scopeOwner proofOwner segment
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase hypothesisLabel formula actual
      childOccurrence substitution := by
  rcases formula with ⟨formulaTypecode, formulaBody⟩
  rcases actual with ⟨actualTypecode, actualBody⟩
  change actualTypecode = formulaTypecode at typecodeEqual
  subst actualTypecode
  dsimp only [AddressedEssentialHypothesisTrace]
  have start := normalAssertionEssentialPhaseAt_inhabits_target_native_type
    scopeOwner proofOwner segment assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel formulaTypecode formulaBody actualBody
    childOccurrence
  refine ⟨start.1, start.2, ?_, ?_⟩
  · exact addressedBodyMatchTrace_of_bodySubstitution proofOwner
      segment.currentProof
      (normalAssertionEssentialContinuationRowAt scopeOwner proofOwner segment
        assertionLabel nextHypothesisPosition hypothesisEnd nextStackPosition
        stackBase hypothesisPosition childOccurrence)
      semantics.2
  · exact normalAssertionEssentialCompletePhaseAt_inhabits_target_native_type
      scopeOwner proofOwner segment assertionLabel nextHypothesisPosition
      hypothesisEnd nextStackPosition stackBase hypothesisPosition
      childOccurrence

/-- An essential actual with a different typecode cannot satisfy the shared
typecode binding installed by the authored essential-hypothesis pattern. -/
theorem addressedEssential_wrong_typecode_stack_match_rejected
    (proofOwner stackAddress occurrence : Atom) (expected actual : String)
    (body : List Metamath.Verify.Sym) (different : actual ≠ expected) :
    matchAtom [("typecode", stringAtom expected)]
        (.expression
          [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
            .expression
              [.symbol "mm-formula", .var "typecode", .var "body"],
            .var "child-occurrence"])
        (normalStackRowAt proofOwner stackAddress ⟨actual, body⟩ occurrence) =
      none := by
  exact addressedFloating_wrong_typecode_stack_match_rejected proofOwner
    stackAddress occurrence expected actual body different

section AxiomAudit

#print axioms normalAssertionEssentialPhaseAt_inhabits_target_native_type
#print axioms normalAssertionEssentialCompletePhaseAt_inhabits_target_native_type
#print axioms addressedEssentialHypothesisTrace_of_semantics
#print axioms addressedEssential_wrong_typecode_stack_match_rejected

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalAssertionEssentialAddressed
