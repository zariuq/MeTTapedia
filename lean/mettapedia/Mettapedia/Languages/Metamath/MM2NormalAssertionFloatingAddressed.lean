import Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
import Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed

/-!
# Address-parametric floating-hypothesis execution

The floating-hypothesis directive treats proof, stack, and child-occurrence
addresses as opaque atoms.  This module instantiates that authored directive
through `NormalAddressSegment`, while retaining ordinary natural-number
hypothesis positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def normalAssertionChildRowAt (proofOwner proofAddress : Atom)
    (hypothesisPosition : Nat) (childOccurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-assertion-child", proofOwner, proofAddress,
      natAtom hypothesisPosition, childOccurrence]

def normalStackRowAt (proofOwner stackAddress : Atom)
    (formula : ConstantHeadedFormula) (occurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, stackAddress,
      formulaAtom formula, occurrence]

@[simp] theorem normalAssertionChildRowAt_nat_exact
    (proofOwner : Atom) (proofPosition hypothesisPosition childOccurrence : Nat) :
    normalAssertionChildRowAt proofOwner (natAtom proofPosition)
        hypothesisPosition (natAtom childOccurrence) =
      normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
        childOccurrence := by
  rfl

private def addressedFloatingLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-normal-assertion-floating"]

private def addressedFloatingPatterns : List Atom :=
  [.expression
      [.symbol "exec", addressedFloatingLocation,
        .var "self-input", .var "self-output"],
   .expression
      [.symbol "mm-assertion-bind", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label", .var "hyp-position",
        .var "hyp-end", .var "stack-position", .var "stack-base"],
   .expression
      [.symbol "mm-assertion-hypothesis", .var "scope", .var "label",
        .var "hyp-position",
        .expression
          [.symbol "mm-floating", .var "hyp-label", .var "typecode",
            .var "variable-name"]],
   .expression
      [.symbol "mm-assertion-hypothesis-successor", .var "scope",
        .var "label", .var "hyp-position", .var "next-hyp-position"],
   .expression
      [.symbol "mm-index-successor", .var "proof",
        .var "stack-position", .var "next-stack-position"],
   .expression
      [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
        .expression
          [.symbol "mm-formula", .var "typecode", .var "body"],
        .var "child-occurrence"]]

private def addressedFloatingInput : Atom :=
  .expression (.symbol "," :: addressedFloatingPatterns)

private def addressedFloatingSelfTemplate : Atom :=
  addressedFloatingPatterns[0]'(by decide)

private def addressedFloatingBindTemplate : Atom :=
  addressedFloatingPatterns[1]'(by decide)

private def addressedFloatingStackTemplate : Atom :=
  addressedFloatingPatterns[5]'(by decide)

private def addressedFloatingNextBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base"]

private def addressedFloatingSubstitutionTemplate : Atom :=
  .expression
    [.symbol "mm-substitution", .var "proof", .var "pc",
      .var "variable-name", .var "body"]

private def addressedFloatingChildTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-child", .var "proof", .var "pc",
      .var "hyp-position", .var "child-occurrence"]

private def addressedFloatingSinks : List Sink :=
  [.add addressedFloatingSelfTemplate,
   .remove addressedFloatingBindTemplate,
   .remove addressedFloatingStackTemplate,
   .add addressedFloatingNextBindTemplate,
   .add addressedFloatingSubstitutionTemplate,
   .add addressedFloatingChildTemplate]

private def addressedFloatingOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "+", addressedFloatingSelfTemplate],
      .expression [.symbol "-", addressedFloatingBindTemplate],
      .expression [.symbol "-", addressedFloatingStackTemplate],
      .expression [.symbol "+", addressedFloatingNextBindTemplate],
      .expression [.symbol "+", addressedFloatingSubstitutionTemplate],
      .expression [.symbol "+", addressedFloatingChildTemplate]]

private theorem addressedFloating_rule_exact :
    normalAssertionFloatingRule =
      .expression
        [.symbol "exec", addressedFloatingLocation, addressedFloatingInput,
          addressedFloatingOutput] := by
  rfl

private theorem addressedFloating_input_exact :
    normalAssertionFloatingDirective.rule.input =
      .compat (mkPattern addressedFloatingPatterns) := by
  rfl

private theorem addressedFloating_sinks_exact :
    normalAssertionFloatingDirective.rule.tmpl.sinks =
      addressedFloatingSinks := by
  rfl

def normalAssertionFloatingPhaseAtomsAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    List Atom :=
  [normalAssertionFloatingRule,
   normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
      hypothesisPosition hypothesisEnd stackPosition stackBase,
   .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-floating", stringAtom hypothesisLabel,
            stringAtom typecode, stringAtom variableName]],
   normalAssertionHypothesisSuccessorRowAt scopeOwner assertionLabel
      hypothesisPosition nextHypothesisPosition,
   normalAssertionStackSuccessorRowAt proofOwner segment stackPosition
      nextStackPosition,
   normalStackRowAt proofOwner (segment.stackAddress stackPosition)
      ⟨typecode, actualBody⟩ childOccurrence]

def normalAssertionFloatingPhaseSpaceAt (scopeOwner proofOwner : Atom)
    (segment : NormalAddressSegment) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) : Space :=
  (normalAssertionFloatingPhaseAtomsAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    variableName actualBody childOccurrence).toFinset

@[simp] theorem normalAssertionFloatingPhaseAtomsAt_ordinary_exact
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    normalAssertionFloatingPhaseAtomsAt scopeOwner proofOwner
        (ordinarySuccessorSegment proofPosition)
        assertionLabel hypothesisPosition nextHypothesisPosition
        hypothesisEnd stackPosition nextStackPosition stackBase
        hypothesisLabel typecode variableName actualBody
        (natAtom childOccurrence) =
      normalAssertionFloatingPhaseAtoms scopeOwner proofOwner proofPosition
        (proofPosition + 1) assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode variableName actualBody
        childOccurrence := by
  rfl

private theorem normalAssertionFloatingPhaseAtomsAt_nodup
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    (normalAssertionFloatingPhaseAtomsAt scopeOwner proofOwner segment
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase hypothesisLabel typecode
      variableName actualBody childOccurrence).Nodup := by
  simp [normalAssertionFloatingPhaseAtomsAt, normalAssertionFloatingRule,
    normalAssertionBindRowAt, normalAssertionHypothesisSuccessorRowAt,
    normalAssertionStackSuccessorRowAt, normalStackRowAt]

private theorem normalAssertionFloatingPhaseAtomsAt_supported
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    cSupportedSourceExecFacts
        (normalAssertionFloatingPhaseAtomsAt scopeOwner proofOwner segment
          assertionLabel hypothesisPosition nextHypothesisPosition
          hypothesisEnd stackPosition nextStackPosition stackBase
          hypothesisLabel typecode variableName actualBody childOccurrence) =
      [normalAssertionFloatingDirective] := by
  rfl

theorem normalAssertionFloatingPhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel hypothesisPosition nextHypothesisPosition
            hypothesisEnd stackPosition nextStackPosition stackBase
            hypothesisLabel typecode variableName actualBody
            childOccurrence)) =
      some normalAssertionFloatingDirective := by
  let atoms := normalAssertionFloatingPhaseAtomsAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    variableName actualBody childOccurrence
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionFloatingDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionFloatingDirective
    (normalAssertionFloatingPhaseAtomsAt_nodup scopeOwner proofOwner segment
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase hypothesisLabel typecode
      variableName actualBody childOccurrence)
    (normalAssertionFloatingPhaseAtomsAt_supported scopeOwner proofOwner segment
      assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
      stackPosition nextStackPosition stackBase hypothesisLabel typecode
      variableName actualBody childOccurrence)

private def addressedFloatingSubstitution
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) : Subst :=
  [("child-occurrence", childOccurrence),
   ("body", listAtom runtimeSymAtom actualBody),
   ("next-stack-position", segment.stackAddress nextStackPosition),
   ("next-hyp-position", natAtom nextHypothesisPosition),
   ("variable-name", stringAtom variableName),
   ("typecode", stringAtom typecode),
   ("hyp-label", stringAtom hypothesisLabel),
   ("stack-base", segment.stackAddress stackBase),
   ("stack-position", segment.stackAddress stackPosition),
   ("hyp-end", natAtom hypothesisEnd),
   ("hyp-position", natAtom hypothesisPosition),
   ("label", stringAtom assertionLabel),
   ("next-pc", segment.nextProof), ("pc", segment.currentProof),
   ("proof", proofOwner), ("scope", scopeOwner),
   ("self-output", addressedFloatingOutput),
   ("self-input", addressedFloatingInput)]

private theorem addressedFloatingMatchRow_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    addressedFloatingSubstitution scopeOwner proofOwner segment assertionLabel
        hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
        nextStackPosition stackBase hypothesisLabel typecode variableName
        actualBody childOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel hypothesisPosition nextHypothesisPosition
            hypothesisEnd stackPosition nextStackPosition stackBase
            hypothesisLabel typecode variableName actualBody childOccurrence)
          normalAssertionFloatingRule)
        normalAssertionFloatingDirective.rule.input).map Prod.fst := by
  let bind := normalAssertionBindRowAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition hypothesisEnd stackPosition stackBase
  let hypothesisRow : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-floating", stringAtom hypothesisLabel,
            stringAtom typecode, stringAtom variableName]]
  let hypothesisSuccessor := normalAssertionHypothesisSuccessorRowAt scopeOwner
    assertionLabel hypothesisPosition nextHypothesisPosition
  let stackSuccessor := normalAssertionStackSuccessorRowAt proofOwner segment
    stackPosition nextStackPosition
  let stack := normalStackRowAt proofOwner
    (segment.stackAddress stackPosition) ⟨typecode, actualBody⟩ childOccurrence
  let space := normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    variableName actualBody childOccurrence
  let read : Space := readCopyAtom space normalAssertionFloatingRule
  let afterSelf : Subst :=
    [("self-output", addressedFloatingOutput),
     ("self-input", addressedFloatingInput)]
  let afterBind : Subst :=
    [("stack-base", segment.stackAddress stackBase),
     ("stack-position", segment.stackAddress stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", segment.nextProof), ("pc", segment.currentProof),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", addressedFloatingOutput),
     ("self-input", addressedFloatingInput)]
  let afterHypothesis : Subst :=
    [("variable-name", stringAtom variableName),
     ("typecode", stringAtom typecode),
     ("hyp-label", stringAtom hypothesisLabel),
     ("stack-base", segment.stackAddress stackBase),
     ("stack-position", segment.stackAddress stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", segment.nextProof), ("pc", segment.currentProof),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", addressedFloatingOutput),
     ("self-input", addressedFloatingInput)]
  let afterHypothesisSuccessor : Subst :=
    ("next-hyp-position", natAtom nextHypothesisPosition) :: afterHypothesis
  let afterStackSuccessor : Subst :=
    ("next-stack-position", segment.stackAddress nextStackPosition) ::
      afterHypothesisSuccessor
  let finalRow := addressedFloatingSubstitution scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    variableName actualBody childOccurrence
  have readMember (atom : Atom) (member : atom ∈ space) : atom ∈ read := by
    by_cases equal : atom = normalAssertionFloatingRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : normalAssertionFloatingRule ∈ read := by
    apply readMember
    simp [space, normalAssertionFloatingPhaseSpaceAt,
      normalAssertionFloatingPhaseAtomsAt]
  have bindMem : bind ∈ read := by
    apply readMember
    simp [space, bind, normalAssertionFloatingPhaseSpaceAt,
      normalAssertionFloatingPhaseAtomsAt]
  have hypothesisRowMem : hypothesisRow ∈ read := by
    apply readMember
    simp [space, hypothesisRow, normalAssertionFloatingPhaseSpaceAt,
      normalAssertionFloatingPhaseAtomsAt]
  have hypothesisSuccessorMem : hypothesisSuccessor ∈ read := by
    apply readMember
    simp [space, hypothesisSuccessor, normalAssertionFloatingPhaseSpaceAt,
      normalAssertionFloatingPhaseAtomsAt]
  have stackSuccessorMem : stackSuccessor ∈ read := by
    apply readMember
    simp [space, stackSuccessor, normalAssertionFloatingPhaseSpaceAt,
      normalAssertionFloatingPhaseAtomsAt]
  have stackMem : stack ∈ read := by
    apply readMember
    simp [space, stack, normalAssertionFloatingPhaseSpaceAt,
      normalAssertionFloatingPhaseAtomsAt]
  have matchSelf :
      matchAtom [] addressedFloatingSelfTemplate
          normalAssertionFloatingRule = some afterSelf := by
    simp [addressedFloatingSelfTemplate, addressedFloatingPatterns,
      addressedFloating_rule_exact, addressedFloatingInput,
      addressedFloatingOutput, addressedFloatingLocation, afterSelf,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchBind :
      matchAtom afterSelf addressedFloatingBindTemplate bind =
        some afterBind := by
    simp [addressedFloatingBindTemplate, addressedFloatingPatterns, afterSelf,
      afterBind, bind, normalAssertionBindRowAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesis :
      matchAtom afterBind (addressedFloatingPatterns[2]'(by decide))
          hypothesisRow = some afterHypothesis := by
    simp [addressedFloatingPatterns, afterBind, afterHypothesis, hypothesisRow,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesisSuccessor :
      matchAtom afterHypothesis (addressedFloatingPatterns[3]'(by decide))
          hypothesisSuccessor = some afterHypothesisSuccessor := by
    simp [addressedFloatingPatterns, afterHypothesis,
      afterHypothesisSuccessor, hypothesisSuccessor,
      normalAssertionHypothesisSuccessorRowAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStackSuccessor :
      matchAtom afterHypothesisSuccessor
          (addressedFloatingPatterns[4]'(by decide)) stackSuccessor =
        some afterStackSuccessor := by
    simp [addressedFloatingPatterns, afterHypothesisSuccessor,
      afterStackSuccessor, afterHypothesis, stackSuccessor,
      normalAssertionStackSuccessorRowAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStack :
      matchAtom afterStackSuccessor
          (addressedFloatingPatterns[5]'(by decide)) stack =
        some finalRow := by
    simp [addressedFloatingPatterns, afterStackSuccessor,
      afterHypothesisSuccessor, afterHypothesis, finalRow,
      addressedFloatingSubstitution, stack, normalStackRowAt, formulaAtom,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {normalAssertionFloatingRule, bind, hypothesisRow,
      hypothesisSuccessor, stackSuccessor, stack}), ?_, rfl⟩
  rw [addressedFloating_input_exact]
  simp only [matchInputSpec, addressedFloatingPatterns, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalAssertionFloatingRule),
    matchOneInSpace_mem [] _ read normalAssertionFloatingRule selfMem
      afterSelf matchSelf, ?_⟩
  refine ⟨(afterBind, bind),
    matchOneInSpace_mem afterSelf _ read bind bindMem afterBind matchBind, ?_⟩
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

theorem normalAssertionFloatingDirectiveAt_fires_evidence
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    let target := fireReflectiveSourceExecFact
      (normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner segment
        assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
        stackPosition nextStackPosition stackBase hypothesisLabel typecode
        variableName actualBody childOccurrence)
      normalAssertionFloatingDirective
    normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase ∈
        target ∧
      normalAssertionSubstitutionRowAt proofOwner segment.currentProof
            variableName actualBody ∈ target ∧
        normalAssertionChildRowAt proofOwner segment.currentProof
            hypothesisPosition childOccurrence ∈ target := by
  dsimp only
  let space := normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner segment
    assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
    stackPosition nextStackPosition stackBase hypothesisLabel typecode
    variableName actualBody childOccurrence
  let rows := (matchInputSpec []
    (readCopyAtom space normalAssertionFloatingDirective.atom)
    normalAssertionFloatingDirective.rule.input).map Prod.fst
  let substitution := addressedFloatingSubstitution scopeOwner proofOwner
    segment assertionLabel hypothesisPosition nextHypothesisPosition
    hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
    typecode variableName actualBody childOccurrence
  have rowMember : substitution ∈ rows := by
    simpa [space, rows, substitution, normalAssertionFloatingDirective] using
      addressedFloatingMatchRow_mem scopeOwner proofOwner segment
        assertionLabel hypothesisPosition nextHypothesisPosition hypothesisEnd
        stackPosition nextStackPosition stackBase hypothesisLabel typecode
        variableName actualBody childOccurrence
  have nextBindInstantiates :
      instantiateTemplateAtom? substitution addressedFloatingNextBindTemplate =
        some (normalAssertionBindRowAt scopeOwner proofOwner segment
          assertionLabel nextHypothesisPosition hypothesisEnd
          nextStackPosition stackBase) := by
    rfl
  have substitutionInstantiates :
      instantiateTemplateAtom? substitution
          addressedFloatingSubstitutionTemplate =
        some (normalAssertionSubstitutionRowAt proofOwner segment.currentProof
          variableName actualBody) := by
    rfl
  have childInstantiates :
      instantiateTemplateAtom? substitution addressedFloatingChildTemplate =
        some (normalAssertionChildRowAt proofOwner segment.currentProof
          hypothesisPosition childOccurrence) := by
    rfl
  have nextBindStaged := addressedStageAdd_contains_of_row rows substitution
    addressedFloatingNextBindTemplate
    (normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase)
    rowMember nextBindInstantiates
  have substitutionStaged := addressedStageAdd_contains_of_row rows
    substitution addressedFloatingSubstitutionTemplate
    (normalAssertionSubstitutionRowAt proofOwner segment.currentProof
      variableName actualBody) rowMember substitutionInstantiates
  have childStaged := addressedStageAdd_contains_of_row rows substitution
    addressedFloatingChildTemplate
    (normalAssertionChildRowAt proofOwner segment.currentProof
      hypothesisPosition childOccurrence) rowMember childInstantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch]
  rw [addressedFloating_sinks_exact]
  simp only [addressedFloatingSinks, reflectiveSupportSinkProvider]
  constructor
  · exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr nextBindStaged)))
  · constructor
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (List.mem_toFinset.mpr substitutionStaged))
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr childStaged)

theorem normalAssertionFloatingPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Atom) :
    let source := normalAssertionFloatingPhaseSpaceAt scopeOwner proofOwner
      segment assertionLabel hypothesisPosition nextHypothesisPosition
      hypothesisEnd stackPosition nextStackPosition stackBase hypothesisLabel
      typecode variableName actualBody childOccurrence
    let target := fireReflectiveSourceExecFact source
      normalAssertionFloatingDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
            nextHypothesisPosition hypothesisEnd nextStackPosition stackBase ∈
          target ∧
        normalAssertionSubstitutionRowAt proofOwner segment.currentProof
              variableName actualBody ∈ target ∧
          normalAssertionChildRowAt proofOwner segment.currentProof
              hypothesisPosition childOccurrence ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionFloatingPhaseAt_selects_directive scopeOwner proofOwner
          segment assertionLabel hypothesisPosition nextHypothesisPosition
          hypothesisEnd stackPosition nextStackPosition stackBase
          hypothesisLabel typecode variableName actualBody childOccurrence))
  · exact normalAssertionFloatingDirectiveAt_fires_evidence scopeOwner
      proofOwner segment assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence

/-- A floating actual with a different typecode cannot supply the shared
typecode binding required by the authored floating-hypothesis pattern. -/
theorem addressedFloating_wrong_typecode_stack_match_rejected
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
  have atomDifferent : stringAtom actual ≠ stringAtom expected := by
    intro equal
    exact different (stringAtom_injective equal)
  simp [normalStackRowAt, formulaAtom, matchAtom, matchAtom.matchAtomList,
    Subst.lookup, atomDifferent]

section AxiomAudit

#print axioms normalAssertionFloatingPhaseAt_selects_directive
#print axioms normalAssertionFloatingPhaseAtomsAt_ordinary_exact
#print axioms normalAssertionFloatingDirectiveAt_fires_evidence
#print axioms normalAssertionFloatingPhaseAt_inhabits_target_native_type
#print axioms addressedFloating_wrong_typecode_stack_match_rejected

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalAssertionFloatingAddressed
