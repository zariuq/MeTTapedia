import Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed

/-!
# Address-parametric normal body matching

The authored body matcher binds its proof counter as an atom.  This module
exposes that representation-independent boundary and relates its complete
directive trace to the source `BodySubstitution` judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalBodyMatchAddressed

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def normalBodyMatchRowAt (proofOwner proofAddress : Atom)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (continuation : Atom) : Atom :=
  .expression
    [.symbol "mm-body-match", proofOwner, proofAddress,
      listAtom runtimeSymAtom sourceBody, listAtom runtimeSymAtom actualBody,
      continuation]

def normalBodyMatchReloadRowAt (proofOwner proofAddress : Atom) : Atom :=
  .expression [.symbol "mm-reload-body-match", proofOwner, proofAddress]

def normalBodyPrefixRowAt (proofOwner proofAddress : Atom)
    (replacementBody actualBody sourceTail : List Metamath.Verify.Sym)
    (continuation : Atom) : Atom :=
  .expression
    [.symbol "mm-body-prefix", proofOwner, proofAddress,
      listAtom runtimeSymAtom replacementBody,
      listAtom runtimeSymAtom actualBody,
      listAtom runtimeSymAtom sourceTail, continuation]

@[simp] theorem normalBodyMatchRowAt_nat_exact
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceBody actualBody : List Metamath.Verify.Sym) :
    normalBodyMatchRowAt proofOwner (natAtom proofPosition) sourceBody
        actualBody continuation =
      normalBodyMatchAtom proofOwner proofPosition sourceBody actualBody
        continuation := by
  rfl

@[simp] theorem normalBodyPrefixRowAt_nat_exact
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (replacementBody actualBody sourceTail : List Metamath.Verify.Sym) :
    normalBodyPrefixRowAt proofOwner (natAtom proofPosition) replacementBody
        actualBody sourceTail continuation =
      normalBodyPrefixAtom proofOwner proofPosition replacementBody actualBody
        sourceTail continuation := by
  rfl

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

private theorem twoPatternRows_mem
    (space : Space) (directive : SourceExecFact)
    (first second firstPattern secondPattern : Atom)
    (afterFirst substitution : Subst)
    (firstMem : first ∈ readCopyAtom space directive.atom)
    (secondMem : second ∈ readCopyAtom space directive.atom)
    (inputExact : directive.rule.input =
      .compat (mkPattern [firstPattern, secondPattern]))
    (firstMatch : matchAtom [] firstPattern first = some afterFirst)
    (secondMatch :
      matchAtom afterFirst secondPattern second = some substitution) :
    substitution ∈
      (matchInputSpec [] (readCopyAtom space directive.atom)
        directive.rule.input).map Prod.fst := by
  rw [List.mem_map]
  refine ⟨(substitution, {first, second}), ?_, rfl⟩
  rw [inputExact]
  simp only [matchInputSpec, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterFirst, first),
    matchOneInSpace_mem [] _ _ first firstMem afterFirst firstMatch, ?_⟩
  refine ⟨(substitution, second),
    matchOneInSpace_mem afterFirst _ _ second secondMem substitution
      secondMatch, ?_⟩
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
    (secondInstantiates : instantiateTemplateAtom? substitution secondTemplate =
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

/-! ## Constant matching -/

private def bodyMatchConstPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "source-tail"],
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "actual-tail"],
      .var "continuation"]

private def bodyMatchConstTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-tail", .var "actual-tail", .var "continuation"]

private def bodyMatchReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

private theorem bodyMatchConst_input_exact :
    normalBodyMatchConstDirective.rule.input =
      .compat (mkPattern [bodyMatchConstPattern]) := by
  rfl

private theorem bodyMatchConst_sinks_exact :
    normalBodyMatchConstDirective.rule.tmpl.sinks =
      [.remove bodyMatchConstPattern, .add bodyMatchConstTailTemplate,
        .add bodyMatchReloadTemplate] := by
  rfl

def normalBodyMatchConstPhaseSpaceAt
    (proofOwner proofAddress continuation : Atom) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) : Space :=
  [normalBodyMatchConstRule,
   normalBodyMatchRowAt proofOwner proofAddress
     (.const constantName :: sourceTail)
     (.const constantName :: actualTail) continuation].toFinset

private def bodyMatchConstSubstitutionAt
    (proofOwner proofAddress continuation : Atom) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) : Subst :=
  [("continuation", continuation),
   ("actual-tail", listAtom runtimeSymAtom actualTail),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("constant-name", stringAtom constantName),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyMatchConstPhaseAt_selects_directive
    (proofOwner proofAddress continuation : Atom) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyMatchConstPhaseSpaceAt proofOwner proofAddress
            continuation constantName sourceTail actualTail)) =
      some normalBodyMatchConstDirective := by
  let atoms :=
    [normalBodyMatchConstRule,
     normalBodyMatchRowAt proofOwner proofAddress
       (.const constantName :: sourceTail)
       (.const constantName :: actualTail) continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyMatchConstDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyMatchConstDirective
    (by simp [atoms, normalBodyMatchConstRule, normalBodyMatchRowAt])
    (by rfl)

private theorem bodyMatchConstRowAt_mem
    (proofOwner proofAddress continuation : Atom) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    bodyMatchConstSubstitutionAt proofOwner proofAddress continuation
        constantName sourceTail actualTail ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyMatchConstPhaseSpaceAt proofOwner proofAddress
            continuation constantName sourceTail actualTail)
          normalBodyMatchConstRule)
        normalBodyMatchConstDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyMatchRowAt proofOwner proofAddress
    (.const constantName :: sourceTail)
    (.const constantName :: actualTail) continuation
  let substitution := bodyMatchConstSubstitutionAt proofOwner proofAddress
    continuation constantName sourceTail actualTail
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyMatchConstPhaseSpaceAt proofOwner proofAddress continuation
        constantName sourceTail actualTail) normalBodyMatchConstRule := by
    simp [cursor, readCopyAtom, consumeAtom,
      normalBodyMatchConstPhaseSpaceAt, normalBodyMatchRowAt,
      normalBodyMatchConstRule, runtimeSymAtom, listAtom]
  apply onePatternRow_mem _ _ cursor bodyMatchConstPattern substitution
    cursorMem bodyMatchConst_input_exact
  simp [bodyMatchConstPattern, cursor, normalBodyMatchRowAt, substitution,
    bodyMatchConstSubstitutionAt, runtimeSymAtom, listAtom, consTag, constTag,
    matchAtom, matchAtom.matchAtomList, Subst.lookup]

theorem normalBodyMatchConstPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress continuation : Atom) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    let source := normalBodyMatchConstPhaseSpaceAt proofOwner proofAddress
      continuation constantName sourceTail actualTail
    let target := fireReflectiveSourceExecFact source
      normalBodyMatchConstDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyMatchRowAt proofOwner proofAddress sourceTail actualTail
            continuation ∈ target ∧
        normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyMatchConstPhaseAt_selects_directive proofOwner proofAddress
          continuation constantName sourceTail actualTail))
  · let substitution := bodyMatchConstSubstitutionAt proofOwner
      proofAddress continuation constantName sourceTail actualTail
    apply fire_remove_add_add_contains _ normalBodyMatchConstDirective
      bodyMatchConstPattern bodyMatchConstTailTemplate
      bodyMatchReloadTemplate _ _ substitution bodyMatchConst_sinks_exact
      (bodyMatchConstRowAt_mem proofOwner proofAddress continuation
        constantName sourceTail actualTail)
    · rfl
    · rfl

theorem bodyMatchConstPattern_rejects_mismatched_constant_at
    (proofOwner proofAddress continuation : Atom)
    (sourceConstant actualConstant : String)
    (sourceTail actualTail : List Metamath.Verify.Sym)
    (different : sourceConstant ≠ actualConstant) :
    matchAtom [] bodyMatchConstPattern
        (normalBodyMatchRowAt proofOwner proofAddress
          (.const sourceConstant :: sourceTail)
          (.const actualConstant :: actualTail) continuation) = none := by
  have encodedDifferent :
      stringAtom actualConstant ≠ stringAtom sourceConstant := by
    intro equal
    exact different (stringAtom_injective equal).symm
  simp [bodyMatchConstPattern, normalBodyMatchRowAt, runtimeSymAtom, listAtom,
    consTag, constTag, matchAtom, matchAtom.matchAtomList, Subst.lookup,
    encodedDifferent]

/-! ## Variable expansion -/

private def bodyMatchVariableCurrentPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "source-tail"],
      .var "actual-body", .var "continuation"]

private def bodyMatchVariableSubstitutionPattern : Atom :=
  .expression
    [.symbol "mm-substitution", .var "proof", .var "pc",
      .var "variable-name", .var "replacement-body"]

private def bodyMatchVariablePrefixTemplate : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .var "replacement-body", .var "actual-body",
      .var "source-tail", .var "continuation"]

private theorem bodyMatchVariable_input_exact :
    normalBodyMatchVariableDirective.rule.input =
      .compat (mkPattern
        [bodyMatchVariableCurrentPattern,
          bodyMatchVariableSubstitutionPattern]) := by
  rfl

private theorem bodyMatchVariable_sinks_exact :
    normalBodyMatchVariableDirective.rule.tmpl.sinks =
      [.remove bodyMatchVariableCurrentPattern,
        .add bodyMatchVariablePrefixTemplate,
        .add bodyMatchReloadTemplate] := by
  rfl

def normalBodyMatchVariablePhaseSpaceAt
    (proofOwner proofAddress continuation : Atom) (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    Space :=
  [normalBodyMatchVariableRule,
   normalBodyMatchRowAt proofOwner proofAddress
     (.var variableName :: sourceTail) actualBody continuation,
   normalAssertionSubstitutionRowAt proofOwner proofAddress variableName
     replacementBody].toFinset

private def bodyMatchVariableAfterCurrentAt
    (proofOwner proofAddress continuation : Atom) (variableName : String)
    (sourceTail actualBody : List Metamath.Verify.Sym) : Subst :=
  [("continuation", continuation),
   ("actual-body", listAtom runtimeSymAtom actualBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("variable-name", stringAtom variableName),
   ("pc", proofAddress), ("proof", proofOwner)]

private def bodyMatchVariableSubstitutionAt
    (proofOwner proofAddress continuation : Atom) (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    Subst :=
  ("replacement-body", listAtom runtimeSymAtom replacementBody) ::
    bodyMatchVariableAfterCurrentAt proofOwner proofAddress continuation
      variableName sourceTail actualBody

theorem normalBodyMatchVariablePhaseAt_selects_directive
    (proofOwner proofAddress continuation : Atom) (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyMatchVariablePhaseSpaceAt proofOwner proofAddress
            continuation variableName replacementBody sourceTail
            actualBody)) =
      some normalBodyMatchVariableDirective := by
  let atoms :=
    [normalBodyMatchVariableRule,
     normalBodyMatchRowAt proofOwner proofAddress
       (.var variableName :: sourceTail) actualBody continuation,
     normalAssertionSubstitutionRowAt proofOwner proofAddress variableName
       replacementBody]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyMatchVariableDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyMatchVariableDirective
    (by simp [atoms, normalBodyMatchVariableRule, normalBodyMatchRowAt,
      normalAssertionSubstitutionRowAt])
    (by rfl)

private theorem bodyMatchVariableRowAt_mem
    (proofOwner proofAddress continuation : Atom) (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    bodyMatchVariableSubstitutionAt proofOwner proofAddress continuation
        variableName replacementBody sourceTail actualBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyMatchVariablePhaseSpaceAt proofOwner proofAddress
            continuation variableName replacementBody sourceTail actualBody)
          normalBodyMatchVariableRule)
        normalBodyMatchVariableDirective.rule.input).map Prod.fst := by
  let current := normalBodyMatchRowAt proofOwner proofAddress
    (.var variableName :: sourceTail) actualBody continuation
  let substitutionRow := normalAssertionSubstitutionRowAt proofOwner
    proofAddress variableName replacementBody
  let afterCurrent := bodyMatchVariableAfterCurrentAt proofOwner proofAddress
    continuation variableName sourceTail actualBody
  let substitution := bodyMatchVariableSubstitutionAt proofOwner proofAddress
    continuation variableName replacementBody sourceTail actualBody
  let read := readCopyAtom
    (normalBodyMatchVariablePhaseSpaceAt proofOwner proofAddress continuation
      variableName replacementBody sourceTail actualBody)
    normalBodyMatchVariableRule
  have currentMem : current ∈ read := by
    simp [read, readCopyAtom, consumeAtom, current, normalBodyMatchRowAt,
      normalBodyMatchVariablePhaseSpaceAt, normalBodyMatchVariableRule,
      runtimeSymAtom, listAtom]
  have substitutionMem : substitutionRow ∈ read := by
    simp [read, readCopyAtom, consumeAtom, substitutionRow,
      normalAssertionSubstitutionRowAt, normalBodyMatchVariablePhaseSpaceAt,
      normalBodyMatchVariableRule]
  have matchCurrent :
      matchAtom [] bodyMatchVariableCurrentPattern current =
        some afterCurrent := by
    simp [bodyMatchVariableCurrentPattern, current, normalBodyMatchRowAt,
      afterCurrent, bodyMatchVariableAfterCurrentAt, runtimeSymAtom,
      listAtom, consTag, variableTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchSubstitution :
      matchAtom afterCurrent bodyMatchVariableSubstitutionPattern
          substitutionRow = some substitution := by
    simp [bodyMatchVariableSubstitutionPattern, substitutionRow,
      normalAssertionSubstitutionRowAt, afterCurrent,
      bodyMatchVariableAfterCurrentAt, substitution,
      bodyMatchVariableSubstitutionAt, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  exact twoPatternRows_mem _ normalBodyMatchVariableDirective current
    substitutionRow bodyMatchVariableCurrentPattern
    bodyMatchVariableSubstitutionPattern afterCurrent substitution currentMem
    substitutionMem bodyMatchVariable_input_exact matchCurrent
    matchSubstitution

theorem normalBodyMatchVariablePhaseAt_inhabits_target_native_type
    (proofOwner proofAddress continuation : Atom) (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    let source := normalBodyMatchVariablePhaseSpaceAt proofOwner proofAddress
      continuation variableName replacementBody sourceTail actualBody
    let target := fireReflectiveSourceExecFact source
      normalBodyMatchVariableDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyPrefixRowAt proofOwner proofAddress replacementBody actualBody
            sourceTail continuation ∈ target ∧
        normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyMatchVariablePhaseAt_selects_directive proofOwner
          proofAddress continuation variableName replacementBody sourceTail
          actualBody))
  · let substitution := bodyMatchVariableSubstitutionAt proofOwner
      proofAddress continuation variableName replacementBody sourceTail
      actualBody
    apply fire_remove_add_add_contains _ normalBodyMatchVariableDirective
      bodyMatchVariableCurrentPattern bodyMatchVariablePrefixTemplate
      bodyMatchReloadTemplate _ _ substitution bodyMatchVariable_sinks_exact
      (bodyMatchVariableRowAt_mem proofOwner proofAddress continuation
        variableName replacementBody sourceTail actualBody)
    · rfl
    · rfl

/-! ## Replacement-prefix matching -/

private def bodyPrefixNilPattern : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "actual-body",
      .var "source-tail", .var "continuation"]

private def bodyPrefixNilTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-tail", .var "actual-body", .var "continuation"]

private theorem bodyPrefixNil_input_exact :
    normalBodyPrefixNilDirective.rule.input =
      .compat (mkPattern [bodyPrefixNilPattern]) := by
  rfl

private theorem bodyPrefixNil_sinks_exact :
    normalBodyPrefixNilDirective.rule.tmpl.sinks =
      [.remove bodyPrefixNilPattern, .add bodyPrefixNilTailTemplate,
        .add bodyMatchReloadTemplate] := by
  rfl

def normalBodyPrefixNilPhaseSpaceAt
    (proofOwner proofAddress continuation : Atom)
    (sourceTail actualBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyPrefixNilRule,
   normalBodyPrefixRowAt proofOwner proofAddress [] actualBody sourceTail
     continuation].toFinset

private def bodyPrefixNilSubstitutionAt
    (proofOwner proofAddress continuation : Atom)
    (sourceTail actualBody : List Metamath.Verify.Sym) : Subst :=
  [("continuation", continuation),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("actual-body", listAtom runtimeSymAtom actualBody),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyPrefixNilPhaseAt_selects_directive
    (proofOwner proofAddress continuation : Atom)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyPrefixNilPhaseSpaceAt proofOwner proofAddress
            continuation sourceTail actualBody)) =
      some normalBodyPrefixNilDirective := by
  let atoms :=
    [normalBodyPrefixNilRule,
     normalBodyPrefixRowAt proofOwner proofAddress [] actualBody sourceTail
       continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyPrefixNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyPrefixNilDirective
    (by simp [atoms, normalBodyPrefixNilRule, normalBodyPrefixRowAt])
    (by rfl)

private theorem bodyPrefixNilRowAt_mem
    (proofOwner proofAddress continuation : Atom)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    bodyPrefixNilSubstitutionAt proofOwner proofAddress continuation sourceTail
        actualBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyPrefixNilPhaseSpaceAt proofOwner proofAddress
            continuation sourceTail actualBody)
          normalBodyPrefixNilRule)
        normalBodyPrefixNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyPrefixRowAt proofOwner proofAddress [] actualBody
    sourceTail continuation
  let substitution := bodyPrefixNilSubstitutionAt proofOwner proofAddress
    continuation sourceTail actualBody
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyPrefixNilPhaseSpaceAt proofOwner proofAddress continuation
        sourceTail actualBody) normalBodyPrefixNilRule := by
    simp [cursor, readCopyAtom, consumeAtom, normalBodyPrefixRowAt,
      normalBodyPrefixNilPhaseSpaceAt, normalBodyPrefixNilRule, listAtom]
  apply onePatternRow_mem _ _ cursor bodyPrefixNilPattern substitution
    cursorMem bodyPrefixNil_input_exact
  simp [bodyPrefixNilPattern, cursor, normalBodyPrefixRowAt, substitution,
    bodyPrefixNilSubstitutionAt, listAtom, nilTag, matchAtom,
    matchAtom.matchAtomList, Subst.lookup]

theorem normalBodyPrefixNilPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress continuation : Atom)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    let source := normalBodyPrefixNilPhaseSpaceAt proofOwner proofAddress
      continuation sourceTail actualBody
    let target := fireReflectiveSourceExecFact source
      normalBodyPrefixNilDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyMatchRowAt proofOwner proofAddress sourceTail actualBody
            continuation ∈ target ∧
        normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyPrefixNilPhaseAt_selects_directive proofOwner proofAddress
          continuation sourceTail actualBody))
  · let substitution := bodyPrefixNilSubstitutionAt proofOwner proofAddress
      continuation sourceTail actualBody
    apply fire_remove_add_add_contains _ normalBodyPrefixNilDirective
      bodyPrefixNilPattern bodyPrefixNilTailTemplate bodyMatchReloadTemplate
      _ _ substitution bodyPrefixNil_sinks_exact
      (bodyPrefixNilRowAt_mem proofOwner proofAddress continuation sourceTail
        actualBody)
    · rfl
    · rfl

private def bodyPrefixConsPattern : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "replacement-tail"],
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "actual-tail"],
      .var "source-tail", .var "continuation"]

private def bodyPrefixConsTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .var "replacement-tail", .var "actual-tail",
      .var "source-tail", .var "continuation"]

private theorem bodyPrefixCons_input_exact :
    normalBodyPrefixConsDirective.rule.input =
      .compat (mkPattern [bodyPrefixConsPattern]) := by
  rfl

private theorem bodyPrefixCons_sinks_exact :
    normalBodyPrefixConsDirective.rule.tmpl.sinks =
      [.remove bodyPrefixConsPattern, .add bodyPrefixConsTailTemplate,
        .add bodyMatchReloadTemplate] := by
  rfl

def normalBodyPrefixConsPhaseSpaceAt
    (proofOwner proofAddress continuation : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    Space :=
  [normalBodyPrefixConsRule,
   normalBodyPrefixRowAt proofOwner proofAddress
     (replacementSymbol :: replacementTail)
     (replacementSymbol :: actualTail) sourceTail continuation].toFinset

private def bodyPrefixConsSubstitutionAt
    (proofOwner proofAddress continuation : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    Subst :=
  [("continuation", continuation),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("actual-tail", listAtom runtimeSymAtom actualTail),
   ("replacement-tail", listAtom runtimeSymAtom replacementTail),
   ("replacement-symbol", runtimeSymAtom replacementSymbol),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyPrefixConsPhaseAt_selects_directive
    (proofOwner proofAddress continuation : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyPrefixConsPhaseSpaceAt proofOwner proofAddress
            continuation replacementSymbol replacementTail actualTail
            sourceTail)) =
      some normalBodyPrefixConsDirective := by
  let atoms :=
    [normalBodyPrefixConsRule,
     normalBodyPrefixRowAt proofOwner proofAddress
       (replacementSymbol :: replacementTail)
       (replacementSymbol :: actualTail) sourceTail continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyPrefixConsDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyPrefixConsDirective
    (by simp [atoms, normalBodyPrefixConsRule, normalBodyPrefixRowAt])
    (by rfl)

private theorem bodyPrefixConsRowAt_mem
    (proofOwner proofAddress continuation : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    bodyPrefixConsSubstitutionAt proofOwner proofAddress continuation
        replacementSymbol replacementTail actualTail sourceTail ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyPrefixConsPhaseSpaceAt proofOwner proofAddress
            continuation replacementSymbol replacementTail actualTail
            sourceTail)
          normalBodyPrefixConsRule)
        normalBodyPrefixConsDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyPrefixRowAt proofOwner proofAddress
    (replacementSymbol :: replacementTail)
    (replacementSymbol :: actualTail) sourceTail continuation
  let substitution := bodyPrefixConsSubstitutionAt proofOwner proofAddress
    continuation replacementSymbol replacementTail actualTail sourceTail
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyPrefixConsPhaseSpaceAt proofOwner proofAddress continuation
        replacementSymbol replacementTail actualTail sourceTail)
      normalBodyPrefixConsRule := by
    simp [cursor, readCopyAtom, consumeAtom, normalBodyPrefixRowAt,
      normalBodyPrefixConsPhaseSpaceAt, normalBodyPrefixConsRule, listAtom]
  apply onePatternRow_mem _ _ cursor bodyPrefixConsPattern substitution
    cursorMem bodyPrefixCons_input_exact
  simp [bodyPrefixConsPattern, cursor, normalBodyPrefixRowAt, substitution,
    bodyPrefixConsSubstitutionAt, listAtom, consTag, matchAtom,
    matchAtom.matchAtomList, Subst.lookup]

theorem normalBodyPrefixConsPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress continuation : Atom)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    let source := normalBodyPrefixConsPhaseSpaceAt proofOwner proofAddress
      continuation replacementSymbol replacementTail actualTail sourceTail
    let target := fireReflectiveSourceExecFact source
      normalBodyPrefixConsDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyPrefixRowAt proofOwner proofAddress replacementTail actualTail
            sourceTail continuation ∈ target ∧
        normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyPrefixConsPhaseAt_selects_directive proofOwner proofAddress
          continuation replacementSymbol replacementTail actualTail
          sourceTail))
  · let substitution := bodyPrefixConsSubstitutionAt proofOwner
      proofAddress continuation replacementSymbol replacementTail actualTail
      sourceTail
    apply fire_remove_add_add_contains _ normalBodyPrefixConsDirective
      bodyPrefixConsPattern bodyPrefixConsTailTemplate bodyMatchReloadTemplate
      _ _ substitution bodyPrefixCons_sinks_exact
      (bodyPrefixConsRowAt_mem proofOwner proofAddress continuation
        replacementSymbol replacementTail actualTail sourceTail)
    · rfl
    · rfl

theorem bodyPrefixConsPattern_rejects_mismatched_symbol_at
    (proofOwner proofAddress continuation : Atom)
    (replacementSymbol actualSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym)
    (different : replacementSymbol ≠ actualSymbol) :
    matchAtom [] bodyPrefixConsPattern
        (normalBodyPrefixRowAt proofOwner proofAddress
          (replacementSymbol :: replacementTail)
          (actualSymbol :: actualTail) sourceTail continuation) = none := by
  have encodedDifferent :
      runtimeSymAtom actualSymbol ≠ runtimeSymAtom replacementSymbol := by
    intro equal
    exact different (runtimeSymAtom_injective equal).symm
  simp [bodyPrefixConsPattern, normalBodyPrefixRowAt, listAtom, consTag,
    matchAtom, matchAtom.matchAtomList, Subst.lookup, encodedDifferent]

/-! ## Completed body -/

private def bodyMatchNilPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .expression [.symbol "mm-nil"],
      .var "continuation"]

private def bodyMatchNilContinuationTemplate : Atom :=
  .var "continuation"

private theorem bodyMatchNil_input_exact :
    normalBodyMatchNilDirective.rule.input =
      .compat (mkPattern [bodyMatchNilPattern]) := by
  rfl

private theorem bodyMatchNil_sinks_exact :
    normalBodyMatchNilDirective.rule.tmpl.sinks =
      [.remove bodyMatchNilPattern, .add bodyMatchNilContinuationTemplate,
        .add bodyMatchReloadTemplate] := by
  rfl

def normalBodyMatchNilPhaseSpaceAt
    (proofOwner proofAddress continuation : Atom) : Space :=
  [normalBodyMatchNilRule,
   normalBodyMatchRowAt proofOwner proofAddress [] [] continuation].toFinset

private def bodyMatchNilSubstitutionAt
    (proofOwner proofAddress continuation : Atom) : Subst :=
  [("continuation", continuation),
   ("pc", proofAddress), ("proof", proofOwner)]

theorem normalBodyMatchNilPhaseAt_selects_directive
    (proofOwner proofAddress continuation : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyMatchNilPhaseSpaceAt proofOwner proofAddress
            continuation)) =
      some normalBodyMatchNilDirective := by
  let atoms :=
    [normalBodyMatchNilRule,
     normalBodyMatchRowAt proofOwner proofAddress [] [] continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyMatchNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyMatchNilDirective
    (by simp [atoms, normalBodyMatchNilRule, normalBodyMatchRowAt])
    (by rfl)

private theorem bodyMatchNilRowAt_mem
    (proofOwner proofAddress continuation : Atom) :
    bodyMatchNilSubstitutionAt proofOwner proofAddress continuation ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyMatchNilPhaseSpaceAt proofOwner proofAddress continuation)
          normalBodyMatchNilRule)
        normalBodyMatchNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyMatchRowAt proofOwner proofAddress [] [] continuation
  let substitution := bodyMatchNilSubstitutionAt proofOwner proofAddress
    continuation
  have cursorMem : cursor ∈ readCopyAtom
      (normalBodyMatchNilPhaseSpaceAt proofOwner proofAddress continuation)
      normalBodyMatchNilRule := by
    simp [cursor, readCopyAtom, consumeAtom, normalBodyMatchRowAt,
      normalBodyMatchNilPhaseSpaceAt, normalBodyMatchNilRule, listAtom]
  apply onePatternRow_mem _ _ cursor bodyMatchNilPattern substitution
    cursorMem bodyMatchNil_input_exact
  simp [bodyMatchNilPattern, cursor, normalBodyMatchRowAt, substitution,
    bodyMatchNilSubstitutionAt, listAtom, nilTag, matchAtom,
    matchAtom.matchAtomList, Subst.lookup]

theorem normalBodyMatchNilPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress continuation : Atom) :
    let source := normalBodyMatchNilPhaseSpaceAt proofOwner proofAddress
      continuation
    let target := fireReflectiveSourceExecFact source
      normalBodyMatchNilDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      continuation ∈ target ∧
        normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyMatchNilPhaseAt_selects_directive proofOwner proofAddress
          continuation))
  · let substitution := bodyMatchNilSubstitutionAt proofOwner proofAddress
      continuation
    apply fire_remove_add_add_contains _ normalBodyMatchNilDirective
      bodyMatchNilPattern bodyMatchNilContinuationTemplate
      bodyMatchReloadTemplate _ _ substitution bodyMatchNil_sinks_exact
      (bodyMatchNilRowAt_mem proofOwner proofAddress continuation)
    · rfl
    · rfl

theorem bodyMatchNilPattern_rejects_actual_remainder_at
    (proofOwner proofAddress continuation : Atom)
    (actualHead : Metamath.Verify.Sym)
    (actualTail : List Metamath.Verify.Sym) :
    matchAtom [] bodyMatchNilPattern
        (normalBodyMatchRowAt proofOwner proofAddress []
          (actualHead :: actualTail) continuation) = none := by
  simp [bodyMatchNilPattern, normalBodyMatchRowAt, listAtom, nilTag, consTag,
    matchAtom, matchAtom.matchAtomList, Subst.lookup]

/-! ## Complete source/target trace -/

inductive AddressedBodyPrefixTrace
    (proofOwner proofAddress continuation : Atom)
    (sourceTail : List Metamath.Verify.Sym) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym →
      List Metamath.Verify.Sym → Prop
  | nil (actualBody : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyPrefixNilPhaseSpaceAt proofOwner proofAddress
          continuation sourceTail actualBody
        let target := fireReflectiveSourceExecFact source
          normalBodyPrefixNilDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyMatchRowAt proofOwner proofAddress sourceTail actualBody
                continuation ∈ target ∧
            normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target) :
      AddressedBodyPrefixTrace proofOwner proofAddress continuation sourceTail
        [] actualBody actualBody
  | cons (symbol : Metamath.Verify.Sym)
      (replacementTail actualTail finalActual : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyPrefixConsPhaseSpaceAt proofOwner proofAddress
          continuation symbol replacementTail actualTail sourceTail
        let target := fireReflectiveSourceExecFact source
          normalBodyPrefixConsDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyPrefixRowAt proofOwner proofAddress replacementTail
                actualTail sourceTail continuation ∈ target ∧
            normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target)
      (tail : AddressedBodyPrefixTrace proofOwner proofAddress continuation
        sourceTail replacementTail actualTail finalActual) :
      AddressedBodyPrefixTrace proofOwner proofAddress continuation sourceTail
        (symbol :: replacementTail) (symbol :: actualTail) finalActual

theorem addressedBodyPrefixTrace_append
    (proofOwner proofAddress continuation : Atom)
    (sourceTail replacement actualTail : List Metamath.Verify.Sym) :
    AddressedBodyPrefixTrace proofOwner proofAddress continuation sourceTail
      replacement (replacement ++ actualTail) actualTail := by
  induction replacement with
  | nil =>
      exact .nil actualTail
        (normalBodyPrefixNilPhaseAt_inhabits_target_native_type proofOwner
          proofAddress continuation sourceTail actualTail)
  | cons symbol replacementTail inductionHypothesis =>
      exact .cons symbol replacementTail (replacementTail ++ actualTail)
        actualTail
        (normalBodyPrefixConsPhaseAt_inhabits_target_native_type proofOwner
          proofAddress continuation symbol replacementTail
          (replacementTail ++ actualTail) sourceTail)
        inductionHypothesis

inductive AddressedBodyMatchTrace
    (proofOwner proofAddress continuation : Atom)
    (substitution : FiniteSubstitution) :
    List Metamath.Verify.Sym → List Metamath.Verify.Sym → Prop
  | nil
      (nativeStep :
        let source := normalBodyMatchNilPhaseSpaceAt proofOwner proofAddress
          continuation
        let target := fireReflectiveSourceExecFact source
          normalBodyMatchNilDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          continuation ∈ target ∧
            normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target) :
      AddressedBodyMatchTrace proofOwner proofAddress continuation substitution
        [] []
  | const (name : String)
      (sourceTail actualTail : List Metamath.Verify.Sym)
      (nativeStep :
        let source := normalBodyMatchConstPhaseSpaceAt proofOwner proofAddress
          continuation name sourceTail actualTail
        let target := fireReflectiveSourceExecFact source
          normalBodyMatchConstDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyMatchRowAt proofOwner proofAddress sourceTail actualTail
                continuation ∈ target ∧
            normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target)
      (tail : AddressedBodyMatchTrace proofOwner proofAddress continuation
        substitution sourceTail actualTail) :
      AddressedBodyMatchTrace proofOwner proofAddress continuation substitution
        (.const name :: sourceTail) (.const name :: actualTail)
  | var (name : String)
      (replacementBody sourceTail actualTail : List Metamath.Verify.Sym)
      (row : normalAssertionSubstitutionRowAt proofOwner proofAddress name
          replacementBody ∈
        normalSubstitutionRowsAt proofOwner proofAddress substitution)
      (nativeStep :
        let source := normalBodyMatchVariablePhaseSpaceAt proofOwner
          proofAddress continuation name replacementBody sourceTail
          (replacementBody ++ actualTail)
        let target := fireReflectiveSourceExecFact source
          normalBodyMatchVariableDirective
        (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
            (reflectiveSourceExecExactTargetNativeType target).pred ∧
          normalBodyPrefixRowAt proofOwner proofAddress replacementBody
                (replacementBody ++ actualTail) sourceTail continuation ∈
              target ∧
            normalBodyMatchReloadRowAt proofOwner proofAddress ∈ target)
      (prefixTrace : AddressedBodyPrefixTrace proofOwner proofAddress
        continuation sourceTail replacementBody
          (replacementBody ++ actualTail) actualTail)
      (tail : AddressedBodyMatchTrace proofOwner proofAddress continuation
        substitution sourceTail actualTail) :
      AddressedBodyMatchTrace proofOwner proofAddress continuation substitution
        (.var name :: sourceTail) (replacementBody ++ actualTail)

theorem addressedBodyMatchTrace_of_bodySubstitution
    (proofOwner proofAddress continuation : Atom)
    {substitution : FiniteSubstitution}
    {source actual : List Metamath.Verify.Sym}
    (semantics : BodySubstitution substitution source actual) :
    AddressedBodyMatchTrace proofOwner proofAddress continuation substitution
      source actual := by
  induction semantics with
  | nil =>
      exact .nil
        (normalBodyMatchNilPhaseAt_inhabits_target_native_type proofOwner
          proofAddress continuation)
  | const tail inductionHypothesis =>
      exact .const _ _ _
        (normalBodyMatchConstPhaseAt_inhabits_target_native_type proofOwner
          proofAddress continuation _ _ _)
        inductionHypothesis
  | var binding tail inductionHypothesis =>
      exact .var _ _ _ _
        ((normalAssertionSubstitutionRowAt_mem_iff proofOwner proofAddress
          substitution _ _).2 ⟨_, binding, rfl⟩)
        (normalBodyMatchVariablePhaseAt_inhabits_target_native_type proofOwner
          proofAddress continuation _ _ _ _)
        (addressedBodyPrefixTrace_append proofOwner proofAddress continuation
          _ _ _)
        inductionHypothesis

theorem AddressedBodyMatchTrace.reflects_bodySubstitution
    {proofOwner proofAddress continuation : Atom}
    {substitution : FiniteSubstitution}
    {source actual : List Metamath.Verify.Sym}
    (trace : AddressedBodyMatchTrace proofOwner proofAddress continuation
      substitution source actual) :
    BodySubstitution substitution source actual := by
  induction trace with
  | nil _ => exact .nil
  | const _ _ _ _ _ induction => exact .const induction
  | var name replacementBody sourceTail actualTail row _ _ _ induction =>
      obtain ⟨replacement, binding, bodyEqual⟩ :=
        (normalAssertionSubstitutionRowAt_mem_iff proofOwner proofAddress
          substitution name replacementBody).1 row
      rw [← bodyEqual]
      exact .var binding induction

theorem addressedBodyMatchTrace_iff_bodySubstitution
    (proofOwner proofAddress continuation : Atom)
    (substitution : FiniteSubstitution)
    (source actual : List Metamath.Verify.Sym) :
    AddressedBodyMatchTrace proofOwner proofAddress continuation substitution
        source actual ↔
      BodySubstitution substitution source actual :=
  ⟨AddressedBodyMatchTrace.reflects_bodySubstitution,
    addressedBodyMatchTrace_of_bodySubstitution proofOwner proofAddress
      continuation⟩

section AxiomAudit

#print axioms normalBodyMatchConstPhaseAt_inhabits_target_native_type
#print axioms normalBodyMatchVariablePhaseAt_inhabits_target_native_type
#print axioms normalBodyPrefixNilPhaseAt_inhabits_target_native_type
#print axioms normalBodyPrefixConsPhaseAt_inhabits_target_native_type
#print axioms normalBodyMatchNilPhaseAt_inhabits_target_native_type
#print axioms addressedBodyMatchTrace_of_bodySubstitution
#print axioms AddressedBodyMatchTrace.reflects_bodySubstitution
#print axioms addressedBodyMatchTrace_iff_bodySubstitution

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalBodyMatchAddressed
