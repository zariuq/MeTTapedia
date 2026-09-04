import Mettapedia.Languages.Metamath.MM2NormalAddressSegment

/-!
# Address-parametric normal assertion body construction

The authored normal body-construction directives bind their proof counter as
an arbitrary atom.  This module exposes that representation-polymorphic
boundary and proves it against the actual reflective MM2 step relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Result-body construction cursor at an arbitrary proof address. -/
def normalBodyBuildRowAt (proofOwner proofAddress : Atom)
    (sourceBody reversedBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-body-build", proofOwner, proofAddress,
      listAtom runtimeSymAtom sourceBody,
      listAtom runtimeSymAtom reversedBody, context]

/-- Variable-body prefix cursor at an arbitrary proof address. -/
def normalBodyBuildPrefixRowAt (proofOwner proofAddress : Atom)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", proofOwner, proofAddress,
      listAtom runtimeSymAtom replacementBody,
      listAtom runtimeSymAtom sourceTail,
      listAtom runtimeSymAtom reversedBody, context]

/-- Result-reversal cursor at an arbitrary proof address. -/
def normalBodyReverseRowAt (proofOwner proofAddress : Atom)
    (reversedTail resultBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-body-reverse", proofOwner, proofAddress,
      listAtom runtimeSymAtom reversedTail,
      listAtom runtimeSymAtom resultBody, context]

/-- Completed result body at an arbitrary proof address. -/
def normalBodyBuiltRowAt (proofOwner proofAddress context : Atom)
    (resultBody : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-body-built", proofOwner, proofAddress, context,
      listAtom runtimeSymAtom resultBody]

/-- Body-machine reload request at an arbitrary proof address. -/
def normalBodyBuildReloadRowAt (proofOwner proofAddress : Atom) : Atom :=
  .expression
    [.symbol "mm-reload-body-build", proofOwner, proofAddress]

@[simp] theorem normalBodyBuildRowAt_nat_exact
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceBody reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildRowAt proofOwner (natAtom proofPosition) sourceBody
        reversedBody context =
      normalBodyBuildAtom proofOwner proofPosition sourceBody reversedBody
        context := by
  rfl

@[simp] theorem normalBodyBuiltRowAt_nat_exact
    (proofOwner context : Atom) (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    normalBodyBuiltRowAt proofOwner (natAtom proofPosition) context resultBody =
      normalBodyBuiltAtom proofOwner proofPosition context resultBody := by
  rfl

@[simp] theorem normalBodyBuiltRowAt_segment_exact
    (segment : NormalAddressSegment) (scopeOwner proofOwner : Atom)
    (assertionLabel resultTypecode : String) (stackBase : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    normalBodyBuiltRowAt proofOwner segment.currentProof
        (segment.resultContext scopeOwner assertionLabel resultTypecode
          stackBase) resultBody =
      segment.bodyBuiltRow proofOwner scopeOwner assertionLabel resultTypecode
        stackBase resultBody := by
  rfl

theorem addressedStageAdd_contains_of_row
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
      intro staged rowMember
      simp at rowMember
  | cons head tail induction =>
      intro staged rowMember
      simp only [List.mem_cons] at rowMember
      simp only [List.foldl_cons]
      rcases rowMember with rfl | rowMember
      · apply stagePreserves tail
          (stageReflectiveSupportSink (.add template) staged substitution)
        simp only [stageReflectiveSupportSink, Sink.atom]
        rw [instantiates]
        by_cases present : candidate ∈ staged
        · simp [insertSupport, present]
        · simp [insertSupport, present]
      · exact induction
          (stageReflectiveSupportSink (.add template) staged head) rowMember

private theorem onePatternRow_mem
    (space : Space) (directive : SourceExecFact)
    (cursor pattern : Atom) (substitution : Subst)
    (cursorMem : cursor ∈ readCopyAtom space directive.atom)
    (inputExact : directive.rule.input = .compat (mkPattern [pattern]))
    (matchExact : matchAtom [] pattern cursor = some substitution) :
    substitution ∈
      (matchInputSpec [] (readCopyAtom space directive.atom)
        directive.rule.input).map Prod.fst := by
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  rw [inputExact]
  simp only [matchInputSpec, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ _ cursor cursorMem substitution matchExact, ?_⟩
  simp

private theorem fire_remove_add_add_contains
    (space : Space) (directive : SourceExecFact)
    (removed firstTemplate secondTemplate firstResult secondResult : Atom)
    (substitution : Subst)
    (sinksExact : directive.rule.tmpl.sinks =
      [.remove removed, .add firstTemplate, .add secondTemplate])
    (rowMember : substitution ∈
      (matchInputSpec [] (readCopyAtom space directive.atom)
        directive.rule.input).map Prod.fst)
    (firstInstantiates : instantiateTemplateAtom? substitution firstTemplate =
      some firstResult)
    (secondInstantiates :
      instantiateTemplateAtom? substitution secondTemplate =
        some secondResult) :
    firstResult ∈ fireReflectiveSourceExecFact space directive ∧
      secondResult ∈ fireReflectiveSourceExecFact space directive := by
  let rows := (matchInputSpec [] (readCopyAtom space directive.atom)
    directive.rule.input).map Prod.fst
  have firstStaged := addressedStageAdd_contains_of_row rows substitution
    firstTemplate firstResult rowMember firstInstantiates
  have secondStaged := addressedStageAdd_contains_of_row rows substitution
    secondTemplate secondResult rowMember secondInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sinksExact, reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr firstStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      sinksExact, reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr secondStaged)

private theorem fire_remove_add_contains
    (space : Space) (directive : SourceExecFact)
    (removed template result : Atom) (substitution : Subst)
    (sinksExact : directive.rule.tmpl.sinks =
      [.remove removed, .add template])
    (rowMember : substitution ∈
      (matchInputSpec [] (readCopyAtom space directive.atom)
        directive.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution template =
      some result) :
    result ∈ fireReflectiveSourceExecFact space directive := by
  let rows := (matchInputSpec [] (readCopyAtom space directive.atom)
    directive.rule.input).map Prod.fst
  have staged := addressedStageAdd_contains_of_row rows substitution template result
    rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    sinksExact, reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

private def normalBodyBuildConstCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "source-tail"],
      .var "reversed-body", .var "context"]

private def normalBodyBuildConstTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .var "source-tail",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "reversed-body"],
      .var "context"]

private def normalBodyBuildReloadTemplateAt : Atom :=
  .expression
    [.symbol "mm-reload-body-build", .var "proof", .var "pc"]

def normalBodyBuildConstPhaseSpaceAt
    (proofOwner proofAddress context : Atom) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyBuildConstRule,
   normalBodyBuildRowAt proofOwner proofAddress
     (.const constantName :: sourceTail) reversedBody context].toFinset

theorem normalBodyBuildConstPhaseAt_selects_directive
    (proofOwner proofAddress context : Atom) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress context
            constantName sourceTail reversedBody)) =
      some normalBodyBuildConstDirective := by
  let atoms :=
    [normalBodyBuildConstRule,
     normalBodyBuildRowAt proofOwner proofAddress
       (.const constantName :: sourceTail) reversedBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildConstDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildConstDirective
    (by simp [atoms, normalBodyBuildConstRule, normalBodyBuildRowAt])
    (by rfl)

private def normalBodyBuildConstSubstitutionAt
    (proofOwner proofAddress context : Atom) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("constant-name", stringAtom constantName),
   ("pc", proofAddress), ("proof", proofOwner)]

private theorem normalBodyBuildConstMatchRowAt_mem
    (proofOwner proofAddress context : Atom) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildConstSubstitutionAt proofOwner proofAddress context
        constantName sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress context
            constantName sourceTail reversedBody)
          normalBodyBuildConstRule)
        normalBodyBuildConstDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildRowAt proofOwner proofAddress
    (.const constantName :: sourceTail) reversedBody context
  let substitution := normalBodyBuildConstSubstitutionAt proofOwner
    proofAddress context constantName sourceTail reversedBody
  let read := readCopyAtom
    (normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress context
      constantName sourceTail reversedBody)
    normalBodyBuildConstRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalBodyBuildRowAt,
      normalBodyBuildConstPhaseSpaceAt, normalBodyBuildConstRule,
      runtimeSymAtom, listAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildConstCursorPatternAt cursor =
        some substitution := by
    simp [normalBodyBuildConstCursorPatternAt, cursor, normalBodyBuildRowAt,
      substitution, normalBodyBuildConstSubstitutionAt, runtimeSymAtom,
      listAtom, consTag, constTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  have inputExact : normalBodyBuildConstDirective.rule.input =
      .compat (mkPattern [normalBodyBuildConstCursorPatternAt]) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution ?_, ?_⟩
  · simpa [normalBodyBuildConstCursorPatternAt] using matchCursor
  · simp [substitution, cursor]

theorem normalBodyBuildConstDirectiveAt_fires_tail
    (proofOwner proofAddress context : Atom) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress context
        constantName sourceTail reversedBody)
      normalBodyBuildConstDirective
    normalBodyBuildRowAt proofOwner proofAddress sourceTail
          (.const constantName :: reversedBody) context ∈ result ∧
      normalBodyBuildReloadRowAt proofOwner proofAddress ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress context
        constantName sourceTail reversedBody)
      normalBodyBuildConstDirective.atom)
    normalBodyBuildConstDirective.rule.input).map Prod.fst
  let substitution := normalBodyBuildConstSubstitutionAt proofOwner
    proofAddress context constantName sourceTail reversedBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyBuildConstDirective] using
      normalBodyBuildConstMatchRowAt_mem proofOwner proofAddress context
        constantName sourceTail reversedBody
  have tailInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildConstTailTemplateAt =
        some (normalBodyBuildRowAt proofOwner proofAddress sourceTail
          (.const constantName :: reversedBody) context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadTemplateAt =
        some (normalBodyBuildReloadRowAt proofOwner proofAddress) := by
    rfl
  have tailStaged := addressedStageAdd_contains_of_row rows substitution
    normalBodyBuildConstTailTemplateAt
    (normalBodyBuildRowAt proofOwner proofAddress sourceTail
      (.const constantName :: reversedBody) context)
    rowMember tailInstantiates
  have reloadStaged := addressedStageAdd_contains_of_row rows substitution
    normalBodyBuildReloadTemplateAt
    (normalBodyBuildReloadRowAt proofOwner proofAddress)
    rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildConstDirective]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildConstDirective]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyBuildConstPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress
      context constantName sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildConstDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildRowAt proofOwner proofAddress sourceTail
            (.const constantName :: reversedBody) context ∈ target ∧
        normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildConstPhaseAt_selects_directive proofOwner proofAddress
          context constantName sourceTail reversedBody))
  · exact normalBodyBuildConstDirectiveAt_fires_tail proofOwner proofAddress
      context constantName sourceTail reversedBody

/-! ## Addressed substitution rows and variable construction -/

/-- Substitution evidence indexed by the exact proof address consumed by the
body machine. -/
def normalAssertionSubstitutionRowAt (proofOwner proofAddress : Atom)
    (variableName : String) (body : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-substitution", proofOwner, proofAddress,
      stringAtom variableName, listAtom runtimeSymAtom body]

structure AddressedSubstitutionPayload where
  proofOwner : Atom
  proofAddress : Atom
  variableName : String
  body : List Metamath.Verify.Sym
deriving DecidableEq

def decodeAddressedSubstitutionRow : Atom → Option AddressedSubstitutionPayload
  | .expression
      [.symbol tag, proofOwner, proofAddress, encodedVariable, encodedBody] =>
      if tag = "mm-substitution" then do
        let variableName ← decodeStringAtom encodedVariable
        let body ← decodeListAtom decodeRuntimeSymAtom encodedBody
        pure ⟨proofOwner, proofAddress, variableName, body⟩
      else
        none
  | _ => none

@[simp] theorem decodeAddressedSubstitutionRow_encode
    (proofOwner proofAddress : Atom) (variableName : String)
    (body : List Metamath.Verify.Sym) :
    decodeAddressedSubstitutionRow
        (normalAssertionSubstitutionRowAt proofOwner proofAddress variableName
          body) =
      some ⟨proofOwner, proofAddress, variableName, body⟩ := by
  simp [decodeAddressedSubstitutionRow, normalAssertionSubstitutionRowAt]

theorem normalAssertionSubstitutionRowAt_injective_payload
    (proofOwner proofAddress : Atom) :
    Function.Injective
      (fun pair : String × List Metamath.Verify.Sym =>
        normalAssertionSubstitutionRowAt proofOwner proofAddress pair.1
          pair.2) := by
  intro left right equal
  have decoded := congrArg decodeAddressedSubstitutionRow equal
  have components : left.1 = right.1 ∧ left.2 = right.2 := by
    simpa using decoded
  exact Prod.ext components.1 components.2

def normalSubstitutionRowsAt (proofOwner proofAddress : Atom)
    (substitution : FiniteSubstitution) : List Atom :=
  substitution.map fun binding =>
    normalAssertionSubstitutionRowAt proofOwner proofAddress
      binding.variableName binding.replacement.body

theorem normalAssertionSubstitutionRowAt_mem_iff
    (proofOwner proofAddress : Atom) (substitution : FiniteSubstitution)
    (variableName : String) (body : List Metamath.Verify.Sym) :
    normalAssertionSubstitutionRowAt proofOwner proofAddress variableName body ∈
        normalSubstitutionRowsAt proofOwner proofAddress substitution ↔
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution variableName replacement ∧
          replacement.body = body := by
  constructor
  · intro member
    rw [normalSubstitutionRowsAt, List.mem_map] at member
    rcases member with ⟨binding, bindingMember, encodedEqual⟩
    rcases binding with ⟨bindingVariable, bindingReplacement⟩
    have payloadEqual :
        (bindingVariable, bindingReplacement.body) = (variableName, body) :=
      normalAssertionSubstitutionRowAt_injective_payload proofOwner
        proofAddress encodedEqual
    have variableEqual := congrArg Prod.fst payloadEqual
    have bodyEqual := congrArg Prod.snd payloadEqual
    change bindingVariable = variableName at variableEqual
    change bindingReplacement.body = body at bodyEqual
    subst variableName
    subst body
    refine ⟨bindingReplacement, ?_, rfl⟩
    simpa [LookupSemantics] using bindingMember
  · rintro ⟨replacement, member, bodyEqual⟩
    rw [normalSubstitutionRowsAt, List.mem_map]
    refine ⟨⟨variableName, replacement⟩, member, ?_⟩
    simp [bodyEqual]

private def normalBodyBuildVariableCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "source-tail"],
      .var "reversed-body", .var "context"]

private def normalBodyBuildVariableSubstitutionPatternAt : Atom :=
  .expression
    [.symbol "mm-substitution", .var "proof", .var "pc",
      .var "variable-name", .var "replacement-body"]

private def normalBodyBuildVariablePrefixTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .var "replacement-body", .var "source-tail",
      .var "reversed-body", .var "context"]

def normalBodyBuildVariablePhaseSpaceAt
    (proofOwner proofAddress context : Atom) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    Space :=
  [normalBodyBuildVariableRule,
   normalBodyBuildRowAt proofOwner proofAddress
     (.var variableName :: sourceTail) reversedBody context,
   normalAssertionSubstitutionRowAt proofOwner proofAddress variableName
     replacementBody].toFinset

private def normalBodyBuildVariableSubstitutionAt
    (proofOwner proofAddress context : Atom) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    Subst :=
  [("replacement-body", listAtom runtimeSymAtom replacementBody),
   ("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("variable-name", stringAtom variableName),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyBuildVariablePhaseAt_selects_directive
    (proofOwner proofAddress context : Atom) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildVariablePhaseSpaceAt proofOwner proofAddress context
            variableName replacementBody sourceTail reversedBody)) =
      some normalBodyBuildVariableDirective := by
  let atoms :=
    [normalBodyBuildVariableRule,
     normalBodyBuildRowAt proofOwner proofAddress
       (.var variableName :: sourceTail) reversedBody context,
     normalAssertionSubstitutionRowAt proofOwner proofAddress variableName
       replacementBody]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildVariableDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildVariableDirective
    (by simp [atoms, normalBodyBuildVariableRule, normalBodyBuildRowAt,
      normalAssertionSubstitutionRowAt])
    (by rfl)

private theorem normalBodyBuildVariableMatchRowAt_mem
    (proofOwner proofAddress context : Atom) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildVariableSubstitutionAt proofOwner proofAddress context
        variableName replacementBody sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildVariablePhaseSpaceAt proofOwner proofAddress context
            variableName replacementBody sourceTail reversedBody)
          normalBodyBuildVariableRule)
        normalBodyBuildVariableDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildRowAt proofOwner proofAddress
    (.var variableName :: sourceTail) reversedBody context
  let substitutionRow := normalAssertionSubstitutionRowAt proofOwner
    proofAddress variableName replacementBody
  let read := readCopyAtom
    (normalBodyBuildVariablePhaseSpaceAt proofOwner proofAddress context
      variableName replacementBody sourceTail reversedBody)
    normalBodyBuildVariableRule
  let afterCursor : Subst :=
    [("context", context),
     ("reversed-body", listAtom runtimeSymAtom reversedBody),
     ("source-tail", listAtom runtimeSymAtom sourceTail),
     ("variable-name", stringAtom variableName),
     ("pc", proofAddress), ("proof", proofOwner)]
  let substitution := normalBodyBuildVariableSubstitutionAt proofOwner
    proofAddress context variableName replacementBody sourceTail reversedBody
  have cursorMem : cursor ∈ read := by
    simp [read, cursor, normalBodyBuildRowAt,
      normalBodyBuildVariablePhaseSpaceAt, normalBodyBuildVariableRule,
      readCopyAtom, consumeAtom, runtimeSymAtom, listAtom]
  have substitutionMem : substitutionRow ∈ read := by
    simp [read, substitutionRow, normalAssertionSubstitutionRowAt,
      normalBodyBuildVariablePhaseSpaceAt, normalBodyBuildVariableRule,
      readCopyAtom, consumeAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildVariableCursorPatternAt cursor =
        some afterCursor := by
    simp [normalBodyBuildVariableCursorPatternAt, cursor,
      normalBodyBuildRowAt, afterCursor, runtimeSymAtom, listAtom, consTag,
      variableTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchSubstitution :
      matchAtom afterCursor normalBodyBuildVariableSubstitutionPatternAt
          substitutionRow = some substitution := by
    simp [normalBodyBuildVariableSubstitutionPatternAt, substitutionRow,
      normalAssertionSubstitutionRowAt, afterCursor, substitution,
      normalBodyBuildVariableSubstitutionAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor, substitutionRow}), ?_, rfl⟩
  have inputExact : normalBodyBuildVariableDirective.rule.input =
      .compat (mkPattern
        [normalBodyBuildVariableCursorPatternAt,
         normalBodyBuildVariableSubstitutionPatternAt]) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterCursor, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem afterCursor matchCursor,
    ?_⟩
  refine ⟨(substitution, substitutionRow),
    matchOneInSpace_mem afterCursor _ read substitutionRow substitutionMem
      substitution matchSubstitution, ?_⟩
  simp [substitution, cursor, substitutionRow]

theorem normalBodyBuildVariablePhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildVariablePhaseSpaceAt proofOwner proofAddress
      context variableName replacementBody sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildVariableDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildPrefixRowAt proofOwner proofAddress replacementBody
            sourceTail reversedBody context ∈ target ∧
        normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildVariablePhaseAt_selects_directive proofOwner
          proofAddress context variableName replacementBody sourceTail
          reversedBody))
  · let source := normalBodyBuildVariablePhaseSpaceAt proofOwner
      proofAddress context variableName replacementBody sourceTail
      reversedBody
    let substitution := normalBodyBuildVariableSubstitutionAt proofOwner
      proofAddress context variableName replacementBody sourceTail
      reversedBody
    have rowMember : substitution ∈
        (matchInputSpec []
          (readCopyAtom source normalBodyBuildVariableDirective.atom)
          normalBodyBuildVariableDirective.rule.input).map Prod.fst := by
      simpa [source, substitution, normalBodyBuildVariableDirective] using
        normalBodyBuildVariableMatchRowAt_mem proofOwner proofAddress context
          variableName replacementBody sourceTail reversedBody
    have sinksExact : normalBodyBuildVariableDirective.rule.tmpl.sinks =
        [.remove normalBodyBuildVariableCursorPatternAt,
         .add normalBodyBuildVariablePrefixTemplateAt,
         .add normalBodyBuildReloadTemplateAt] := by
      rfl
    exact fire_remove_add_add_contains source normalBodyBuildVariableDirective
      normalBodyBuildVariableCursorPatternAt
      normalBodyBuildVariablePrefixTemplateAt normalBodyBuildReloadTemplateAt
      (normalBodyBuildPrefixRowAt proofOwner proofAddress replacementBody
        sourceTail reversedBody context)
      (normalBodyBuildReloadRowAt proofOwner proofAddress) substitution
      sinksExact rowMember (by rfl) (by rfl)

/-! ## Substitution-prefix exhaustion -/

private def normalBodyBuildPrefixNilPatternAt : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "source-tail",
      .var "reversed-body", .var "context"]

private def normalBodyBuildPrefixNilTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .var "source-tail", .var "reversed-body", .var "context"]

def normalBodyBuildPrefixNilPhaseSpaceAt
    (proofOwner proofAddress context : Atom)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyBuildPrefixNilRule,
   normalBodyBuildPrefixRowAt proofOwner proofAddress [] sourceTail
     reversedBody context].toFinset

private def normalBodyBuildPrefixNilSubstitutionAt
    (proofOwner proofAddress context : Atom)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyBuildPrefixNilPhaseAt_selects_directive
    (proofOwner proofAddress context : Atom)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildPrefixNilPhaseSpaceAt proofOwner proofAddress context
            sourceTail reversedBody)) =
      some normalBodyBuildPrefixNilDirective := by
  let atoms :=
    [normalBodyBuildPrefixNilRule,
     normalBodyBuildPrefixRowAt proofOwner proofAddress [] sourceTail
       reversedBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildPrefixNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildPrefixNilDirective
    (by simp [atoms, normalBodyBuildPrefixNilRule,
      normalBodyBuildPrefixRowAt])
    (by rfl)

private theorem normalBodyBuildPrefixNilMatchRowAt_mem
    (proofOwner proofAddress context : Atom)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildPrefixNilSubstitutionAt proofOwner proofAddress context
        sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildPrefixNilPhaseSpaceAt proofOwner proofAddress context
            sourceTail reversedBody)
          normalBodyBuildPrefixNilRule)
        normalBodyBuildPrefixNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildPrefixRowAt proofOwner proofAddress []
    sourceTail reversedBody context
  let substitution := normalBodyBuildPrefixNilSubstitutionAt proofOwner
    proofAddress context sourceTail reversedBody
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyBuildPrefixNilPhaseSpaceAt proofOwner proofAddress context
        sourceTail reversedBody) normalBodyBuildPrefixNilRule := by
    simp [cursor, normalBodyBuildPrefixRowAt,
      normalBodyBuildPrefixNilPhaseSpaceAt, normalBodyBuildPrefixNilRule,
      readCopyAtom, consumeAtom, listAtom]
  have inputExact : normalBodyBuildPrefixNilDirective.rule.input =
      .compat (mkPattern [normalBodyBuildPrefixNilPatternAt]) := by
    rfl
  have matchExact : matchAtom [] normalBodyBuildPrefixNilPatternAt cursor =
      some substitution := by
    simp [normalBodyBuildPrefixNilPatternAt, cursor,
      normalBodyBuildPrefixRowAt, substitution,
      normalBodyBuildPrefixNilSubstitutionAt, listAtom, nilTag, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  exact onePatternRow_mem _ _ cursor normalBodyBuildPrefixNilPatternAt
    substitution cursorMem inputExact matchExact

theorem normalBodyBuildPrefixNilPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildPrefixNilPhaseSpaceAt proofOwner proofAddress
      context sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildPrefixNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildRowAt proofOwner proofAddress sourceTail reversedBody
            context ∈ target ∧
        normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildPrefixNilPhaseAt_selects_directive proofOwner
          proofAddress context sourceTail reversedBody))
  · let source := normalBodyBuildPrefixNilPhaseSpaceAt proofOwner
      proofAddress context sourceTail reversedBody
    let substitution := normalBodyBuildPrefixNilSubstitutionAt proofOwner
      proofAddress context sourceTail reversedBody
    have rowMember : substitution ∈
        (matchInputSpec []
          (readCopyAtom source normalBodyBuildPrefixNilDirective.atom)
          normalBodyBuildPrefixNilDirective.rule.input).map Prod.fst := by
      simpa [source, substitution, normalBodyBuildPrefixNilDirective] using
        normalBodyBuildPrefixNilMatchRowAt_mem proofOwner proofAddress context
          sourceTail reversedBody
    have sinksExact : normalBodyBuildPrefixNilDirective.rule.tmpl.sinks =
        [.remove normalBodyBuildPrefixNilPatternAt,
         .add normalBodyBuildPrefixNilTailTemplateAt,
         .add normalBodyBuildReloadTemplateAt] := by
      rfl
    exact fire_remove_add_add_contains source
      normalBodyBuildPrefixNilDirective normalBodyBuildPrefixNilPatternAt
      normalBodyBuildPrefixNilTailTemplateAt normalBodyBuildReloadTemplateAt
      (normalBodyBuildRowAt proofOwner proofAddress sourceTail reversedBody
        context)
      (normalBodyBuildReloadRowAt proofOwner proofAddress) substitution
      sinksExact rowMember (by rfl) (by rfl)

/-! ## One substitution-prefix symbol -/

private def normalBodyBuildPrefixConsPatternAt : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "replacement-tail"],
      .var "source-tail", .var "reversed-body", .var "context"]

private def normalBodyBuildPrefixConsTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .var "replacement-tail", .var "source-tail",
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "reversed-body"],
      .var "context"]

def normalBodyBuildPrefixConsPhaseSpaceAt
    (proofOwner proofAddress context : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    Space :=
  [normalBodyBuildPrefixConsRule,
   normalBodyBuildPrefixRowAt proofOwner proofAddress
     (replacementSymbol :: replacementTail) sourceTail reversedBody
     context].toFinset

private def normalBodyBuildPrefixConsSubstitutionAt
    (proofOwner proofAddress context : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("replacement-tail", listAtom runtimeSymAtom replacementTail),
   ("replacement-symbol", runtimeSymAtom replacementSymbol),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyBuildPrefixConsPhaseAt_selects_directive
    (proofOwner proofAddress context : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildPrefixConsPhaseSpaceAt proofOwner proofAddress
            context replacementSymbol replacementTail sourceTail
            reversedBody)) =
      some normalBodyBuildPrefixConsDirective := by
  let atoms :=
    [normalBodyBuildPrefixConsRule,
     normalBodyBuildPrefixRowAt proofOwner proofAddress
       (replacementSymbol :: replacementTail) sourceTail reversedBody
       context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildPrefixConsDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildPrefixConsDirective
    (by simp [atoms, normalBodyBuildPrefixConsRule,
      normalBodyBuildPrefixRowAt, listAtom])
    (by rfl)

private theorem normalBodyBuildPrefixConsMatchRowAt_mem
    (proofOwner proofAddress context : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildPrefixConsSubstitutionAt proofOwner proofAddress context
        replacementSymbol replacementTail sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildPrefixConsPhaseSpaceAt proofOwner proofAddress
            context replacementSymbol replacementTail sourceTail
            reversedBody)
          normalBodyBuildPrefixConsRule)
        normalBodyBuildPrefixConsDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildPrefixRowAt proofOwner proofAddress
    (replacementSymbol :: replacementTail) sourceTail reversedBody context
  let substitution := normalBodyBuildPrefixConsSubstitutionAt proofOwner
    proofAddress context replacementSymbol replacementTail sourceTail
    reversedBody
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyBuildPrefixConsPhaseSpaceAt proofOwner proofAddress context
        replacementSymbol replacementTail sourceTail reversedBody)
      normalBodyBuildPrefixConsRule := by
    simp [cursor, normalBodyBuildPrefixRowAt,
      normalBodyBuildPrefixConsPhaseSpaceAt, normalBodyBuildPrefixConsRule,
      readCopyAtom, consumeAtom, listAtom]
  have inputExact : normalBodyBuildPrefixConsDirective.rule.input =
      .compat (mkPattern [normalBodyBuildPrefixConsPatternAt]) := by
    rfl
  have matchExact : matchAtom [] normalBodyBuildPrefixConsPatternAt cursor =
      some substitution := by
    simp [normalBodyBuildPrefixConsPatternAt, cursor,
      normalBodyBuildPrefixRowAt, substitution,
      normalBodyBuildPrefixConsSubstitutionAt, listAtom, consTag, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  exact onePatternRow_mem _ _ cursor normalBodyBuildPrefixConsPatternAt
    substitution cursorMem inputExact matchExact

theorem normalBodyBuildPrefixConsPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildPrefixConsPhaseSpaceAt proofOwner
      proofAddress context replacementSymbol replacementTail sourceTail
      reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildPrefixConsDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildPrefixRowAt proofOwner proofAddress replacementTail
            sourceTail (replacementSymbol :: reversedBody) context ∈ target ∧
        normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildPrefixConsPhaseAt_selects_directive proofOwner
          proofAddress context replacementSymbol replacementTail sourceTail
          reversedBody))
  · let source := normalBodyBuildPrefixConsPhaseSpaceAt proofOwner
      proofAddress context replacementSymbol replacementTail sourceTail
      reversedBody
    let substitution := normalBodyBuildPrefixConsSubstitutionAt proofOwner
      proofAddress context replacementSymbol replacementTail sourceTail
      reversedBody
    have rowMember : substitution ∈
        (matchInputSpec []
          (readCopyAtom source normalBodyBuildPrefixConsDirective.atom)
          normalBodyBuildPrefixConsDirective.rule.input).map Prod.fst := by
      simpa [source, substitution, normalBodyBuildPrefixConsDirective] using
        normalBodyBuildPrefixConsMatchRowAt_mem proofOwner proofAddress context
          replacementSymbol replacementTail sourceTail reversedBody
    have sinksExact : normalBodyBuildPrefixConsDirective.rule.tmpl.sinks =
        [.remove normalBodyBuildPrefixConsPatternAt,
         .add normalBodyBuildPrefixConsTailTemplateAt,
         .add normalBodyBuildReloadTemplateAt] := by
      rfl
    exact fire_remove_add_add_contains source
      normalBodyBuildPrefixConsDirective normalBodyBuildPrefixConsPatternAt
      normalBodyBuildPrefixConsTailTemplateAt normalBodyBuildReloadTemplateAt
      (normalBodyBuildPrefixRowAt proofOwner proofAddress replacementTail
        sourceTail (replacementSymbol :: reversedBody) context)
      (normalBodyBuildReloadRowAt proofOwner proofAddress) substitution
      sinksExact rowMember (by rfl) (by rfl)

/-! ## End of source body -/

private def normalBodyBuildNilPatternAt : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "reversed-body",
      .var "context"]

private def normalBodyBuildNilReverseTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .var "reversed-body", .expression [.symbol "mm-nil"],
      .var "context"]

def normalBodyBuildNilPhaseSpaceAt
    (proofOwner proofAddress context : Atom)
    (reversedBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyBuildNilRule,
   normalBodyBuildRowAt proofOwner proofAddress [] reversedBody
     context].toFinset

private def normalBodyBuildNilSubstitutionAt
    (proofOwner proofAddress context : Atom)
    (reversedBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyBuildNilPhaseAt_selects_directive
    (proofOwner proofAddress context : Atom)
    (reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildNilPhaseSpaceAt proofOwner proofAddress context
            reversedBody)) =
      some normalBodyBuildNilDirective := by
  let atoms :=
    [normalBodyBuildNilRule,
     normalBodyBuildRowAt proofOwner proofAddress [] reversedBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildNilDirective
    (by simp [atoms, normalBodyBuildNilRule, normalBodyBuildRowAt])
    (by rfl)

private theorem normalBodyBuildNilMatchRowAt_mem
    (proofOwner proofAddress context : Atom)
    (reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildNilSubstitutionAt proofOwner proofAddress context
        reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildNilPhaseSpaceAt proofOwner proofAddress context
            reversedBody)
          normalBodyBuildNilRule)
        normalBodyBuildNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildRowAt proofOwner proofAddress [] reversedBody
    context
  let substitution := normalBodyBuildNilSubstitutionAt proofOwner
    proofAddress context reversedBody
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyBuildNilPhaseSpaceAt proofOwner proofAddress context
        reversedBody) normalBodyBuildNilRule := by
    simp [cursor, normalBodyBuildRowAt, normalBodyBuildNilPhaseSpaceAt,
      normalBodyBuildNilRule, readCopyAtom, consumeAtom, listAtom]
  have inputExact : normalBodyBuildNilDirective.rule.input =
      .compat (mkPattern [normalBodyBuildNilPatternAt]) := by
    rfl
  have matchExact : matchAtom [] normalBodyBuildNilPatternAt cursor =
      some substitution := by
    simp [normalBodyBuildNilPatternAt, cursor, normalBodyBuildRowAt,
      substitution, normalBodyBuildNilSubstitutionAt, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  exact onePatternRow_mem _ _ cursor normalBodyBuildNilPatternAt substitution
    cursorMem inputExact matchExact

theorem normalBodyBuildNilPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom)
    (reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildNilPhaseSpaceAt proofOwner proofAddress
      context reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyReverseRowAt proofOwner proofAddress reversedBody [] context ∈
            target ∧
        normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildNilPhaseAt_selects_directive proofOwner proofAddress
          context reversedBody))
  · let source := normalBodyBuildNilPhaseSpaceAt proofOwner proofAddress
      context reversedBody
    let substitution := normalBodyBuildNilSubstitutionAt proofOwner
      proofAddress context reversedBody
    have rowMember : substitution ∈
        (matchInputSpec []
          (readCopyAtom source normalBodyBuildNilDirective.atom)
          normalBodyBuildNilDirective.rule.input).map Prod.fst := by
      simpa [source, substitution, normalBodyBuildNilDirective] using
        normalBodyBuildNilMatchRowAt_mem proofOwner proofAddress context
          reversedBody
    have sinksExact : normalBodyBuildNilDirective.rule.tmpl.sinks =
        [.remove normalBodyBuildNilPatternAt,
         .add normalBodyBuildNilReverseTemplateAt,
         .add normalBodyBuildReloadTemplateAt] := by
      rfl
    exact fire_remove_add_add_contains source normalBodyBuildNilDirective
      normalBodyBuildNilPatternAt normalBodyBuildNilReverseTemplateAt
      normalBodyBuildReloadTemplateAt
      (normalBodyReverseRowAt proofOwner proofAddress reversedBody [] context)
      (normalBodyBuildReloadRowAt proofOwner proofAddress) substitution
      sinksExact rowMember (by rfl) (by rfl)

/-! ## Reversal -/

private def normalBodyReverseConsPatternAt : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons", .var "head", .var "reversed-tail"],
      .var "result-body", .var "context"]

private def normalBodyReverseConsTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .var "reversed-tail",
      .expression [.symbol "mm-cons", .var "head", .var "result-body"],
      .var "context"]

def normalBodyReverseConsPhaseSpaceAt
    (proofOwner proofAddress context : Atom)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyReverseConsRule,
   normalBodyReverseRowAt proofOwner proofAddress (head :: reversedTail)
     resultBody context].toFinset

private def normalBodyReverseConsSubstitutionAt
    (proofOwner proofAddress context : Atom)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("result-body", listAtom runtimeSymAtom resultBody),
   ("reversed-tail", listAtom runtimeSymAtom reversedTail),
   ("head", runtimeSymAtom head),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyReverseConsPhaseAt_selects_directive
    (proofOwner proofAddress context : Atom)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyReverseConsPhaseSpaceAt proofOwner proofAddress context
            head reversedTail resultBody)) =
      some normalBodyReverseConsDirective := by
  let atoms :=
    [normalBodyReverseConsRule,
     normalBodyReverseRowAt proofOwner proofAddress (head :: reversedTail)
       resultBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyReverseConsDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyReverseConsDirective
    (by simp [atoms, normalBodyReverseConsRule, normalBodyReverseRowAt,
      listAtom])
    (by rfl)

private theorem normalBodyReverseConsMatchRowAt_mem
    (proofOwner proofAddress context : Atom)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    normalBodyReverseConsSubstitutionAt proofOwner proofAddress context head
        reversedTail resultBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyReverseConsPhaseSpaceAt proofOwner proofAddress context
            head reversedTail resultBody)
          normalBodyReverseConsRule)
        normalBodyReverseConsDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyReverseRowAt proofOwner proofAddress
    (head :: reversedTail) resultBody context
  let substitution := normalBodyReverseConsSubstitutionAt proofOwner
    proofAddress context head reversedTail resultBody
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyReverseConsPhaseSpaceAt proofOwner proofAddress context head
        reversedTail resultBody) normalBodyReverseConsRule := by
    simp [cursor, normalBodyReverseRowAt, normalBodyReverseConsPhaseSpaceAt,
      normalBodyReverseConsRule, readCopyAtom, consumeAtom, listAtom]
  have inputExact : normalBodyReverseConsDirective.rule.input =
      .compat (mkPattern [normalBodyReverseConsPatternAt]) := by
    rfl
  have matchExact : matchAtom [] normalBodyReverseConsPatternAt cursor =
      some substitution := by
    simp [normalBodyReverseConsPatternAt, cursor, normalBodyReverseRowAt,
      substitution, normalBodyReverseConsSubstitutionAt, listAtom, consTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  exact onePatternRow_mem _ _ cursor normalBodyReverseConsPatternAt
    substitution cursorMem inputExact matchExact

theorem normalBodyReverseConsPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    let source := normalBodyReverseConsPhaseSpaceAt proofOwner proofAddress
      context head reversedTail resultBody
    let target := fireReflectiveSourceExecFact source
      normalBodyReverseConsDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyReverseRowAt proofOwner proofAddress reversedTail
            (head :: resultBody) context ∈ target ∧
        normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyReverseConsPhaseAt_selects_directive proofOwner
          proofAddress context head reversedTail resultBody))
  · let source := normalBodyReverseConsPhaseSpaceAt proofOwner proofAddress
      context head reversedTail resultBody
    let substitution := normalBodyReverseConsSubstitutionAt proofOwner
      proofAddress context head reversedTail resultBody
    have rowMember : substitution ∈
        (matchInputSpec []
          (readCopyAtom source normalBodyReverseConsDirective.atom)
          normalBodyReverseConsDirective.rule.input).map Prod.fst := by
      simpa [source, substitution, normalBodyReverseConsDirective] using
        normalBodyReverseConsMatchRowAt_mem proofOwner proofAddress context
          head reversedTail resultBody
    have sinksExact : normalBodyReverseConsDirective.rule.tmpl.sinks =
        [.remove normalBodyReverseConsPatternAt,
         .add normalBodyReverseConsTailTemplateAt,
         .add normalBodyBuildReloadTemplateAt] := by
      rfl
    exact fire_remove_add_add_contains source normalBodyReverseConsDirective
      normalBodyReverseConsPatternAt normalBodyReverseConsTailTemplateAt
      normalBodyBuildReloadTemplateAt
      (normalBodyReverseRowAt proofOwner proofAddress reversedTail
        (head :: resultBody) context)
      (normalBodyBuildReloadRowAt proofOwner proofAddress) substitution
      sinksExact rowMember (by rfl) (by rfl)

private def normalBodyReverseNilPatternAt : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "result-body",
      .var "context"]

private def normalBodyReverseNilBuiltTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-built", .var "proof", .var "pc",
      .var "context", .var "result-body"]

def normalBodyReverseNilPhaseSpaceAt
    (proofOwner proofAddress context : Atom)
    (resultBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyReverseNilRule,
   normalBodyReverseRowAt proofOwner proofAddress [] resultBody
     context].toFinset

private def normalBodyReverseNilSubstitutionAt
    (proofOwner proofAddress context : Atom)
    (resultBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("result-body", listAtom runtimeSymAtom resultBody),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyReverseNilPhaseAt_selects_directive
    (proofOwner proofAddress context : Atom)
    (resultBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyReverseNilPhaseSpaceAt proofOwner proofAddress context
            resultBody)) =
      some normalBodyReverseNilDirective := by
  let atoms :=
    [normalBodyReverseNilRule,
     normalBodyReverseRowAt proofOwner proofAddress [] resultBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyReverseNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyReverseNilDirective
    (by simp [atoms, normalBodyReverseNilRule, normalBodyReverseRowAt])
    (by rfl)

private theorem normalBodyReverseNilMatchRowAt_mem
    (proofOwner proofAddress context : Atom)
    (resultBody : List Metamath.Verify.Sym) :
    normalBodyReverseNilSubstitutionAt proofOwner proofAddress context
        resultBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyReverseNilPhaseSpaceAt proofOwner proofAddress context
            resultBody)
          normalBodyReverseNilRule)
        normalBodyReverseNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyReverseRowAt proofOwner proofAddress [] resultBody
    context
  let substitution := normalBodyReverseNilSubstitutionAt proofOwner
    proofAddress context resultBody
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyReverseNilPhaseSpaceAt proofOwner proofAddress context
        resultBody) normalBodyReverseNilRule := by
    simp [cursor, normalBodyReverseRowAt, normalBodyReverseNilPhaseSpaceAt,
      normalBodyReverseNilRule, readCopyAtom, consumeAtom, listAtom]
  have inputExact : normalBodyReverseNilDirective.rule.input =
      .compat (mkPattern [normalBodyReverseNilPatternAt]) := by
    rfl
  have matchExact : matchAtom [] normalBodyReverseNilPatternAt cursor =
      some substitution := by
    simp [normalBodyReverseNilPatternAt, cursor, normalBodyReverseRowAt,
      substitution, normalBodyReverseNilSubstitutionAt, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  exact onePatternRow_mem _ _ cursor normalBodyReverseNilPatternAt
    substitution cursorMem inputExact matchExact

theorem normalBodyReverseNilPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress context : Atom)
    (resultBody : List Metamath.Verify.Sym) :
    let source := normalBodyReverseNilPhaseSpaceAt proofOwner proofAddress
      context resultBody
    let target := fireReflectiveSourceExecFact source
      normalBodyReverseNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuiltRowAt proofOwner proofAddress context resultBody ∈
        target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyReverseNilPhaseAt_selects_directive proofOwner proofAddress
          context resultBody))
  · let source := normalBodyReverseNilPhaseSpaceAt proofOwner proofAddress
      context resultBody
    let substitution := normalBodyReverseNilSubstitutionAt proofOwner
      proofAddress context resultBody
    have rowMember : substitution ∈
        (matchInputSpec []
          (readCopyAtom source normalBodyReverseNilDirective.atom)
          normalBodyReverseNilDirective.rule.input).map Prod.fst := by
      simpa [source, substitution, normalBodyReverseNilDirective] using
        normalBodyReverseNilMatchRowAt_mem proofOwner proofAddress context
          resultBody
    have sinksExact : normalBodyReverseNilDirective.rule.tmpl.sinks =
        [.remove normalBodyReverseNilPatternAt,
         .add normalBodyReverseNilBuiltTemplateAt] := by
      rfl
    exact fire_remove_add_contains source normalBodyReverseNilDirective
      normalBodyReverseNilPatternAt normalBodyReverseNilBuiltTemplateAt
      (normalBodyBuiltRowAt proofOwner proofAddress context resultBody)
      substitution sinksExact rowMember (by rfl)

/-! ## Exact recursive correspondence -/

inductive AddressedBodyBuildPrefixTrace
    (proofOwner proofAddress context : Atom)
    (sourceTail : List Metamath.Verify.Sym) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (reversedBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildPrefixNilPhaseSpaceAt proofOwner
          proofAddress context sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildPrefixNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildRowAt proofOwner proofAddress sourceTail reversedBody
                context ∈ target ∧
            normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target) :
      AddressedBodyBuildPrefixTrace proofOwner proofAddress context
        sourceTail [] reversedBody reversedBody
  | cons (symbol : Metamath.Verify.Sym)
      (replacementTail reversedBody finalReversed :
        List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildPrefixConsPhaseSpaceAt proofOwner
          proofAddress context symbol replacementTail sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildPrefixConsDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildPrefixRowAt proofOwner proofAddress replacementTail
                sourceTail (symbol :: reversedBody) context ∈ target ∧
            normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target)
      (tail : AddressedBodyBuildPrefixTrace proofOwner proofAddress context
        sourceTail replacementTail (symbol :: reversedBody) finalReversed) :
      AddressedBodyBuildPrefixTrace proofOwner proofAddress context
        sourceTail (symbol :: replacementTail) reversedBody finalReversed

theorem addressedBodyBuildPrefixTrace_exact
    (proofOwner proofAddress context : Atom)
    (sourceTail replacement reversedBody : List Metamath.Verify.Sym) :
    AddressedBodyBuildPrefixTrace proofOwner proofAddress context sourceTail
      replacement reversedBody (replacement.reverse ++ reversedBody) := by
  induction replacement generalizing reversedBody with
  | nil =>
      simpa using
        AddressedBodyBuildPrefixTrace.nil
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) (sourceTail := sourceTail) reversedBody
          (normalBodyBuildPrefixNilPhaseAt_inhabits_target_native_type
            proofOwner proofAddress context sourceTail reversedBody)
  | cons symbol replacementTail inductionHypothesis =>
      have tail := inductionHypothesis (symbol :: reversedBody)
      have step :=
        normalBodyBuildPrefixConsPhaseAt_inhabits_target_native_type
          proofOwner proofAddress context symbol replacementTail sourceTail
          reversedBody
      simpa [List.reverse_cons, List.append_assoc] using
        AddressedBodyBuildPrefixTrace.cons
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) (sourceTail := sourceTail) symbol
          replacementTail reversedBody
          (replacementTail.reverse ++ symbol :: reversedBody) step tail

theorem AddressedBodyBuildPrefixTrace.finalReversed_eq
    {proofOwner proofAddress context : Atom}
    {sourceTail replacement reversedBody finalReversed :
      List Metamath.Verify.Sym}
    (trace : AddressedBodyBuildPrefixTrace proofOwner proofAddress context
      sourceTail replacement reversedBody finalReversed) :
    finalReversed = replacement.reverse ++ reversedBody := by
  induction trace with
  | nil _ _ => simp
  | cons symbol replacementTail reversedBody finalReversed _ _ induction =>
      simpa [List.reverse_cons, List.append_assoc] using induction

inductive AddressedBodyReverseTrace
    (proofOwner proofAddress context : Atom) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (resultBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyReverseNilPhaseSpaceAt proofOwner proofAddress
          context resultBody
        let target := fireReflectiveSourceExecFact source
          normalBodyReverseNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuiltRowAt proofOwner proofAddress context resultBody ∈
            target) :
      AddressedBodyReverseTrace proofOwner proofAddress context [] resultBody
        resultBody
  | cons (head : Metamath.Verify.Sym)
      (reversedTail resultBody finalBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyReverseConsPhaseSpaceAt proofOwner proofAddress
          context head reversedTail resultBody
        let target := fireReflectiveSourceExecFact source
          normalBodyReverseConsDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyReverseRowAt proofOwner proofAddress reversedTail
                (head :: resultBody) context ∈ target ∧
            normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target)
      (tail : AddressedBodyReverseTrace proofOwner proofAddress context
        reversedTail (head :: resultBody) finalBody) :
      AddressedBodyReverseTrace proofOwner proofAddress context
        (head :: reversedTail) resultBody finalBody

theorem addressedBodyReverseTrace_exact
    (proofOwner proofAddress context : Atom)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    AddressedBodyReverseTrace proofOwner proofAddress context reversedTail
      resultBody (reversedTail.reverse ++ resultBody) := by
  induction reversedTail generalizing resultBody with
  | nil =>
      simpa using
        AddressedBodyReverseTrace.nil
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) resultBody
          (normalBodyReverseNilPhaseAt_inhabits_target_native_type proofOwner
            proofAddress context resultBody)
  | cons head reversedTail inductionHypothesis =>
      have tail := inductionHypothesis (head :: resultBody)
      have step := normalBodyReverseConsPhaseAt_inhabits_target_native_type
        proofOwner proofAddress context head reversedTail resultBody
      simpa [List.reverse_cons, List.append_assoc] using
        AddressedBodyReverseTrace.cons
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) head reversedTail resultBody
          (reversedTail.reverse ++ head :: resultBody) step tail

theorem AddressedBodyReverseTrace.finalBody_eq
    {proofOwner proofAddress context : Atom}
    {reversedTail resultBody finalBody : List Metamath.Verify.Sym}
    (trace : AddressedBodyReverseTrace proofOwner proofAddress context
      reversedTail resultBody finalBody) :
    finalBody = reversedTail.reverse ++ resultBody := by
  induction trace with
  | nil _ _ => simp
  | cons head reversedTail resultBody finalBody _ _ induction =>
      simpa [List.reverse_cons, List.append_assoc] using induction

inductive AddressedBodyBuildTrace
    (proofOwner proofAddress context : Atom)
    (substitution : FiniteSubstitution) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (reversedBody finalBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildNilPhaseSpaceAt proofOwner proofAddress
          context reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildNilDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyReverseRowAt proofOwner proofAddress reversedBody []
                context ∈ target ∧
            normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target)
      (reverseTrace : AddressedBodyReverseTrace proofOwner proofAddress
        context reversedBody [] finalBody) :
      AddressedBodyBuildTrace proofOwner proofAddress context substitution []
        reversedBody finalBody
  | const (name : String)
      (sourceTail reversedBody finalBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyBuildConstPhaseSpaceAt proofOwner proofAddress
          context name sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildConstDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildRowAt proofOwner proofAddress sourceTail
                (.const name :: reversedBody) context ∈ target ∧
            normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target)
      (tail : AddressedBodyBuildTrace proofOwner proofAddress context
        substitution sourceTail (.const name :: reversedBody) finalBody) :
      AddressedBodyBuildTrace proofOwner proofAddress context substitution
        (.const name :: sourceTail) reversedBody finalBody
  | var (name : String)
      (replacementBody sourceTail reversedBody afterPrefix finalBody :
        List Metamath.Verify.Sym)
      (row : normalAssertionSubstitutionRowAt proofOwner proofAddress name
          replacementBody ∈
        normalSubstitutionRowsAt proofOwner proofAddress substitution)
      (nativeStep :
        let source := normalBodyBuildVariablePhaseSpaceAt proofOwner
          proofAddress context name replacementBody sourceTail reversedBody
        let target := fireReflectiveSourceExecFact source
          normalBodyBuildVariableDirective
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
            (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyBuildPrefixRowAt proofOwner proofAddress replacementBody
                sourceTail reversedBody context ∈ target ∧
            normalBodyBuildReloadRowAt proofOwner proofAddress ∈ target)
      (prefixTrace : AddressedBodyBuildPrefixTrace proofOwner proofAddress
        context sourceTail replacementBody reversedBody afterPrefix)
      (tail : AddressedBodyBuildTrace proofOwner proofAddress context
        substitution sourceTail afterPrefix finalBody) :
      AddressedBodyBuildTrace proofOwner proofAddress context substitution
        (.var name :: sourceTail) reversedBody finalBody

theorem addressedBodyBuildTrace_of_bodySubstitution_acc
    (proofOwner proofAddress context : Atom)
    {substitution : FiniteSubstitution}
    {sourceBody resultBody : List Metamath.Verify.Sym}
    (semantics : BodySubstitution substitution sourceBody resultBody)
    (reversedBody : List Metamath.Verify.Sym) :
    AddressedBodyBuildTrace proofOwner proofAddress context substitution
      sourceBody reversedBody (reversedBody.reverse ++ resultBody) := by
  induction semantics generalizing reversedBody with
  | nil =>
      simpa using
        (AddressedBodyBuildTrace.nil
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) (substitution := substitution)
          reversedBody reversedBody.reverse
          (normalBodyBuildNilPhaseAt_inhabits_target_native_type proofOwner
            proofAddress context reversedBody)
          (by
            simpa using
              (addressedBodyReverseTrace_exact proofOwner proofAddress
                context reversedBody [])))
  | @const name sourceTail resultTail tail inductionHypothesis =>
      have tailTrace := inductionHypothesis (.const name :: reversedBody)
      have step := normalBodyBuildConstPhaseAt_inhabits_target_native_type
        proofOwner proofAddress context name sourceTail reversedBody
      simpa [List.reverse_cons, List.append_assoc] using
        AddressedBodyBuildTrace.const
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) (substitution := substitution) name sourceTail
          reversedBody ((.const name :: reversedBody).reverse ++ resultTail)
          step tailTrace
  | @var name replacement sourceTail resultTail binding tail
      inductionHypothesis =>
      let afterPrefix := replacement.body.reverse ++ reversedBody
      have row : normalAssertionSubstitutionRowAt proofOwner proofAddress name
            replacement.body ∈
          normalSubstitutionRowsAt proofOwner proofAddress substitution :=
        (normalAssertionSubstitutionRowAt_mem_iff proofOwner proofAddress
          substitution name replacement.body).2 ⟨replacement, binding, rfl⟩
      have step := normalBodyBuildVariablePhaseAt_inhabits_target_native_type
        proofOwner proofAddress context name replacement.body sourceTail
        reversedBody
      have prefixTrace : AddressedBodyBuildPrefixTrace proofOwner proofAddress
          context sourceTail replacement.body reversedBody afterPrefix :=
        addressedBodyBuildPrefixTrace_exact proofOwner proofAddress context
          sourceTail replacement.body reversedBody
      have tailTrace := inductionHypothesis afterPrefix
      simpa [afterPrefix, List.reverse_append, List.append_assoc] using
        AddressedBodyBuildTrace.var
          (proofOwner := proofOwner) (proofAddress := proofAddress)
          (context := context) (substitution := substitution) name
          replacement.body sourceTail reversedBody afterPrefix
          (afterPrefix.reverse ++ resultTail) row step prefixTrace tailTrace

theorem addressedBodyBuildTrace_of_bodySubstitution
    (proofOwner proofAddress context : Atom)
    {substitution : FiniteSubstitution}
    {sourceBody resultBody : List Metamath.Verify.Sym}
    (semantics : BodySubstitution substitution sourceBody resultBody) :
    AddressedBodyBuildTrace proofOwner proofAddress context substitution
      sourceBody [] resultBody := by
  simpa using addressedBodyBuildTrace_of_bodySubstitution_acc proofOwner
    proofAddress context semantics []

theorem AddressedBodyBuildTrace.reflects_bodySubstitution
    {proofOwner proofAddress context : Atom}
    {substitution : FiniteSubstitution}
    {sourceBody reversedBody finalBody : List Metamath.Verify.Sym}
    (trace : AddressedBodyBuildTrace proofOwner proofAddress context
      substitution sourceBody reversedBody finalBody) :
    ∃ resultBody,
      BodySubstitution substitution sourceBody resultBody ∧
        finalBody = reversedBody.reverse ++ resultBody := by
  induction trace with
  | nil reversedBody finalBody _ reverseTrace =>
      refine ⟨[], .nil, ?_⟩
      simpa using reverseTrace.finalBody_eq
  | const name sourceTail reversedBody finalBody _ _ induction =>
      obtain ⟨resultTail, semantics, finalEqual⟩ := induction
      refine ⟨.const name :: resultTail, .const semantics, ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using finalEqual
  | var name replacementBody sourceTail reversedBody afterPrefix finalBody
      row _ prefixTrace _ induction =>
      obtain ⟨resultTail, tailSemantics, finalEqual⟩ := induction
      obtain ⟨replacement, binding, bodyEqual⟩ :=
        (normalAssertionSubstitutionRowAt_mem_iff proofOwner proofAddress
          substitution name replacementBody).1 row
      refine ⟨replacement.body ++ resultTail,
        .var binding tailSemantics, ?_⟩
      have prefixEqual := prefixTrace.finalReversed_eq
      calc
        finalBody = afterPrefix.reverse ++ resultTail := finalEqual
        _ = (replacementBody.reverse ++ reversedBody).reverse ++
              resultTail := by rw [prefixEqual]
        _ = reversedBody.reverse ++ (replacementBody ++ resultTail) := by
              simp [List.reverse_append, List.append_assoc]
        _ = reversedBody.reverse ++ (replacement.body ++ resultTail) := by
              rw [bodyEqual]

theorem addressedBodyBuildTrace_iff_bodySubstitution
    (proofOwner proofAddress context : Atom)
    (substitution : FiniteSubstitution)
    (sourceBody resultBody : List Metamath.Verify.Sym) :
    AddressedBodyBuildTrace proofOwner proofAddress context substitution
        sourceBody [] resultBody ↔
      BodySubstitution substitution sourceBody resultBody := by
  constructor
  · intro trace
    obtain ⟨reflectedBody, semantics, finalEqual⟩ :=
      trace.reflects_bodySubstitution
    simp at finalEqual
    subst resultBody
    exact semantics
  · exact addressedBodyBuildTrace_of_bodySubstitution proofOwner
      proofAddress context

/-- A source-generated assertion node constructs the arbitrary-address body
trace from its independently interpreted substitution semantics. -/
theorem GeneratedAssertionNode.result_has_addressed_body_trace
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView}
    (hassertion : assertion ∈ projection.assertions)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (node : GeneratedAssertionNode projection target assertion actuals result
      substitution)
    (proofOwner proofAddress context : Atom) :
    AddressedBodyBuildTrace proofOwner proofAddress context substitution
      assertion.formula.body [] result.body := by
  rcases (assertionRuleApplication_iff_instances projection target
      hprojection hassertion).mp node.application with ⟨instances, _⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection instances).mp ⟨node.sideEvidence⟩ with
    ⟨_essentialMatches, _dvSemantics, resultSemantics⟩
  exact addressedBodyBuildTrace_of_bodySubstitution proofOwner proofAddress
    context resultSemantics.2

section AxiomAudit

#print axioms normalBodyBuildConstPhaseAt_inhabits_target_native_type
#print axioms addressedStageAdd_contains_of_row
#print axioms normalAssertionSubstitutionRowAt_mem_iff
#print axioms normalBodyBuildVariablePhaseAt_inhabits_target_native_type
#print axioms normalBodyBuildPrefixNilPhaseAt_inhabits_target_native_type
#print axioms normalBodyBuildPrefixConsPhaseAt_inhabits_target_native_type
#print axioms normalBodyBuildNilPhaseAt_inhabits_target_native_type
#print axioms normalBodyReverseConsPhaseAt_inhabits_target_native_type
#print axioms normalBodyReverseNilPhaseAt_inhabits_target_native_type
#print axioms addressedBodyBuildTrace_of_bodySubstitution
#print axioms AddressedBodyBuildTrace.reflects_bodySubstitution
#print axioms addressedBodyBuildTrace_iff_bodySubstitution
#print axioms GeneratedAssertionNode.result_has_addressed_body_trace

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
