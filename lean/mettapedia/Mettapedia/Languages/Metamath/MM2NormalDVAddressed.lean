import Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
import Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed

/-!
# Address-parametric disjoint-variable execution

The normal disjoint-variable machine treats the proof counter as an opaque
address.  This module exposes that latent polymorphism and proves the actual
scheduled MM2 phases at an arbitrary proof address.  Pair and body cursors
remain natural-number positions because they enumerate finite source data;
only the proof address is representation-dependent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalDVAddressed

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2NormalAddressSegment
open Mettapedia.Languages.Metamath.MM2NormalAssertionEntryAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Addressed runtime rows -/

def normalDVNextPairRowAt (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", scopeOwner, proofOwner, proofAddress,
      stringAtom assertionLabel, natAtom pairPosition, natAtom pairEnd,
      listAtom runtimeSymAtom sourceBody, context]

def normalDVReloadRowAt (proofOwner proofAddress : Atom) : Atom :=
  .expression [.symbol "mm-reload-dv", proofOwner, proofAddress]

def normalDVScanLeftRowAt (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", scopeOwner, proofOwner, proofAddress,
      stringAtom assertionLabel, natAtom nextPairPosition, natAtom pairEnd,
      listAtom runtimeSymAtom leftBody,
      listAtom runtimeSymAtom rightBody,
      listAtom runtimeSymAtom sourceBody, context]

def normalDVScanRightRowAt (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightRemainder rightBody sourceBody :
      List Metamath.Verify.Sym) (context : Atom) : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", scopeOwner, proofOwner, proofAddress,
      stringAtom assertionLabel, natAtom nextPairPosition, natAtom pairEnd,
      stringAtom leftVariable, listAtom runtimeSymAtom leftTail,
      listAtom runtimeSymAtom rightRemainder,
      listAtom runtimeSymAtom rightBody,
      listAtom runtimeSymAtom sourceBody, context]

@[simp] theorem normalDVNextPairRowAt_nat_exact
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (pairPosition pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalDVNextPairRowAt scopeOwner proofOwner (natAtom proofPosition)
        assertionLabel pairPosition pairEnd sourceBody context =
      normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
        pairPosition pairEnd sourceBody context := by
  rfl

@[simp] theorem normalDVReloadRowAt_nat_exact
    (proofOwner : Atom) (proofPosition : Nat) :
    normalDVReloadRowAt proofOwner (natAtom proofPosition) =
      normalDVReloadAtom proofOwner proofPosition := by
  rfl

@[simp] theorem normalDVScanLeftRowAt_nat_exact
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVScanLeftRowAt scopeOwner proofOwner (natAtom proofPosition)
        assertionLabel nextPairPosition pairEnd leftBody rightBody sourceBody
        context =
      normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
        nextPairPosition pairEnd leftBody rightBody sourceBody context := by
  rfl

@[simp] theorem normalDVScanRightRowAt_nat_exact
    (scopeOwner proofOwner : Atom) (proofPosition : Nat)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightRemainder rightBody sourceBody :
      List Metamath.Verify.Sym) (context : Atom) :
    normalDVScanRightRowAt scopeOwner proofOwner (natAtom proofPosition)
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightRemainder rightBody sourceBody context =
      normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
        nextPairPosition pairEnd leftVariable leftTail rightRemainder rightBody
        sourceBody context := by
  rfl

/-! ## Small proof combinators for authored unary phases -/

private theorem unaryMatchRow_mem
    (read : Space) (pattern cursor : Atom) (substitution : Subst)
    (cursorMem : cursor ∈ read)
    (matchExact : matchAtom [] pattern cursor = some substitution) :
    substitution ∈
      (matchInputSpec [] read (.compat (mkPattern [pattern]))).map Prod.fst := by
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [matchInputSpec, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] pattern read cursor cursorMem substitution matchExact,
    ?_⟩
  simp

private theorem selectedUnaryPhase
    (atoms : List Atom) (directive : SourceExecFact)
    (nodup : atoms.Nodup)
    (supported : cSupportedSourceExecFacts atoms = [directive]) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace atoms.toFinset) = some directive :=
  reflective_selects_of_computable_supported_singleton atoms directive nodup
    supported

/-! ## Persistent verifier-code reload -/

def normalDVReloadPhaseSpaceAt (proofOwner proofAddress : Atom) : Space :=
  [normalDVReloadRule, normalDVReloadRowAt proofOwner proofAddress,
   normalDVRuleBundle].toFinset

theorem normalDVReloadPhaseAt_selects_directive
    (proofOwner proofAddress : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVReloadPhaseSpaceAt proofOwner proofAddress)) =
      some normalDVReloadDirective := by
  let atoms := [normalDVReloadRule,
    normalDVReloadRowAt proofOwner proofAddress, normalDVRuleBundle]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVReloadDirective
  exact selectedUnaryPhase atoms normalDVReloadDirective
    (by
      simp [atoms, normalDVReloadRule, normalDVReloadRowAt,
        normalDVRuleBundle])
    (by rfl)

theorem normalDVReloadPhaseAt_inhabits_target_native_type
    (proofOwner proofAddress : Atom) :
    let source := normalDVReloadPhaseSpaceAt proofOwner proofAddress
    let target := fireReflectiveSourceExecFact source normalDVReloadDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalDVReloadPhaseAt_selects_directive proofOwner proofAddress))

/-! ## Terminal DV cursor and body-construction handoff -/

private def normalDVCompleteCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", .var "hyp-end", .var "hyp-end",
      .var "source-body", .var "context"]

private def normalDVCompleteBodyTemplateAt : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .var "source-body", .expression [.symbol "mm-nil"],
      .var "context"]

def normalDVCompletePhaseSpaceAt (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Space :=
  [normalDVCompleteRule,
   normalDVNextPairRowAt scopeOwner proofOwner proofAddress assertionLabel
     pairEnd pairEnd sourceBody context].toFinset

theorem normalDVCompletePhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVCompletePhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd sourceBody context)) =
      some normalDVCompleteDirective := by
  let atoms :=
    [normalDVCompleteRule,
     normalDVNextPairRowAt scopeOwner proofOwner proofAddress assertionLabel
       pairEnd pairEnd sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVCompleteDirective
  exact selectedUnaryPhase atoms normalDVCompleteDirective
    (by
      simp [atoms, normalDVCompleteRule, normalDVNextPairRowAt])
    (by rfl)

private def normalDVCompleteSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("hyp-end", natAtom pairEnd), ("label", stringAtom assertionLabel),
   ("pc", proofAddress), ("proof", proofOwner), ("scope", scopeOwner)]

private theorem normalDVCompleteMatchRowAt_mem
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalDVCompleteSubstitutionAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVCompletePhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd sourceBody context)
          normalDVCompleteRule)
        normalDVCompleteDirective.rule.input).map Prod.fst := by
  let cursor := normalDVNextPairRowAt scopeOwner proofOwner proofAddress
    assertionLabel pairEnd pairEnd sourceBody context
  let substitution := normalDVCompleteSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel pairEnd sourceBody context
  let read := readCopyAtom
    (normalDVCompletePhaseSpaceAt scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context) normalDVCompleteRule
  have cursorMem : cursor ∈ read := by
    simp [read, cursor, readCopyAtom, consumeAtom,
      normalDVCompletePhaseSpaceAt, normalDVCompleteRule,
      normalDVNextPairRowAt]
  have matchExact : matchAtom [] normalDVCompleteCursorPatternAt cursor =
      some substitution := by
    simp [normalDVCompleteCursorPatternAt, cursor,
      normalDVNextPairRowAt, substitution,
      normalDVCompleteSubstitutionAt, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have inputExact : normalDVCompleteDirective.rule.input =
      .compat (mkPattern [normalDVCompleteCursorPatternAt]) := by
    rfl
  rw [inputExact]
  exact unaryMatchRow_mem read normalDVCompleteCursorPatternAt cursor
    substitution cursorMem matchExact

theorem normalDVCompleteDirectiveAt_fires_body_build
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context ∈
      fireReflectiveSourceExecFact
        (normalDVCompletePhaseSpaceAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context)
        normalDVCompleteDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVCompletePhaseSpaceAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context)
      normalDVCompleteDirective.atom)
    normalDVCompleteDirective.rule.input).map Prod.fst
  let substitution := normalDVCompleteSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel pairEnd sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVCompleteDirective] using
      normalDVCompleteMatchRowAt_mem scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context
  have instantiates :
      instantiateTemplateAtom? substitution normalDVCompleteBodyTemplateAt =
        some (normalBodyBuildRowAt proofOwner proofAddress sourceBody []
          context) := by
    rfl
  have staged := addressedStageAdd_contains_of_row rows substitution
    normalDVCompleteBodyTemplateAt
    (normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context)
    rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalDVCompleteDirective]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

theorem normalDVCompletePhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    let source := normalDVCompletePhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVCompleteDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context ∈
        target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVCompletePhaseAt_selects_directive scopeOwner proofOwner
          proofAddress assertionLabel pairEnd sourceBody context))
  · exact normalDVCompleteDirectiveAt_fires_body_build scopeOwner
      proofOwner proofAddress assertionLabel pairEnd sourceBody context

/-! ## Left-body constant step -/

private def normalDVLeftConstCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "source-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVLeftConstTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "source-tail", .var "body",
      .var "source-body", .var "context"]

private def normalDVReloadTemplateAt : Atom :=
  .expression [.symbol "mm-reload-dv", .var "proof", .var "pc"]

private theorem unaryDVPhase_inhabits_and_fires
    (source : Space) (directive : SourceExecFact)
    (pattern cursor : Atom) (substitution : Subst)
    (outputTemplate output proofOwner proofAddress : Atom)
    (selection : selectNextScheduled
        (supportedSourceExecFactsOfSpace source) = some directive)
    (inputExact : directive.rule.input =
      .compat (mkPattern [pattern]))
    (sinksExact : directive.rule.tmpl =
      mkTemplate
        [.remove pattern, .add outputTemplate,
          .add normalDVReloadTemplateAt])
    (cursorMem : cursor ∈ readCopyAtom source directive.atom)
    (matchExact : matchAtom [] pattern cursor = some substitution)
    (outputInstantiates :
      instantiateTemplateAtom? substitution outputTemplate = some output)
    (reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVReloadTemplateAt =
        some (normalDVReloadRowAt proofOwner proofAddress)) :
    let target := fireReflectiveSourceExecFact source directive
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      output ∈ target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let rows := (matchInputSpec [] (readCopyAtom source directive.atom)
    directive.rule.input).map Prod.fst
  have rowMember : substitution ∈ rows := by
    change substitution ∈
      (matchInputSpec [] (readCopyAtom source directive.atom)
        directive.rule.input).map Prod.fst
    rw [inputExact]
    exact unaryMatchRow_mem (readCopyAtom source directive.atom) pattern
      cursor substitution cursorMem matchExact
  have outputStaged := addressedStageAdd_contains_of_row rows substitution
    outputTemplate output rowMember outputInstantiates
  have reloadStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVReloadTemplateAt
    (normalDVReloadRowAt proofOwner proofAddress) rowMember
    reloadInstantiates
  refine ⟨reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected selection), ?_, ?_⟩
  · simp only [fireReflectiveSourceExecFact, sinksExact, mkTemplate,
      applyReflectiveSinkBatch]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr outputStaged))
  · simp only [fireReflectiveSourceExecFact, sinksExact, mkTemplate,
      applyReflectiveSinkBatch]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

def normalDVLeftConstPhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVLeftConstRule,
   normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
     nextPairPosition pairEnd (.const constantName :: leftTail) rightBody
     sourceBody context].toFinset

theorem normalDVLeftConstPhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel nextPairPosition pairEnd constantName leftTail
            rightBody sourceBody context)) =
      some normalDVLeftConstDirective := by
  let atoms :=
    [normalDVLeftConstRule,
     normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
       nextPairPosition pairEnd (.const constantName :: leftTail) rightBody
       sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVLeftConstDirective
  exact selectedUnaryPhase atoms normalDVLeftConstDirective
    (by simp [atoms, normalDVLeftConstRule, normalDVScanLeftRowAt])
    (by rfl)

private def normalDVLeftConstSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("constant-name", stringAtom constantName),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

private theorem normalDVLeftConstMatchRowAt_mem
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVLeftConstSubstitutionAt scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel nextPairPosition pairEnd constantName leftTail
            rightBody sourceBody context)
          normalDVLeftConstRule)
        normalDVLeftConstDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanLeftRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd (.const constantName :: leftTail)
    rightBody sourceBody context
  let substitution := normalDVLeftConstSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd constantName leftTail
    rightBody sourceBody context
  let read := readCopyAtom
    (normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd constantName leftTail rightBody
      sourceBody context) normalDVLeftConstRule
  have cursorMem : cursor ∈ read := by
    simp [read, cursor, readCopyAtom, consumeAtom,
      normalDVLeftConstPhaseSpaceAt, normalDVLeftConstRule,
      normalDVScanLeftRowAt]
  have matchExact : matchAtom [] normalDVLeftConstCursorPatternAt cursor =
      some substitution := by
    simp [normalDVLeftConstCursorPatternAt, cursor,
      normalDVScanLeftRowAt, substitution,
      normalDVLeftConstSubstitutionAt, runtimeSymAtom, listAtom, consTag,
      constTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have inputExact : normalDVLeftConstDirective.rule.input =
      .compat (mkPattern [normalDVLeftConstCursorPatternAt]) := by
    rfl
  rw [inputExact]
  exact unaryMatchRow_mem read normalDVLeftConstCursorPatternAt cursor
    substitution cursorMem matchExact

theorem normalDVLeftConstDirectiveAt_fires_tail
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let target := fireReflectiveSourceExecFact
      (normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context)
      normalDVLeftConstDirective
    normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context)
      normalDVLeftConstDirective.atom)
    normalDVLeftConstDirective.rule.input).map Prod.fst
  let substitution := normalDVLeftConstSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd constantName leftTail
    rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVLeftConstDirective] using
      normalDVLeftConstMatchRowAt_mem scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalDVLeftConstTailTemplateAt =
        some (normalDVScanLeftRowAt scopeOwner proofOwner proofAddress
          assertionLabel nextPairPosition pairEnd leftTail rightBody sourceBody
          context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVReloadTemplateAt =
        some (normalDVReloadRowAt proofOwner proofAddress) := by
    rfl
  have tailStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVLeftConstTailTemplateAt
    (normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
      nextPairPosition pairEnd leftTail rightBody sourceBody context)
    rowMember tailInstantiates
  have reloadStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVReloadTemplateAt (normalDVReloadRowAt proofOwner proofAddress)
    rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftConstDirective]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftConstDirective]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVLeftConstPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd constantName
      leftTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVLeftConstDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
          target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVLeftConstPhaseAt_selects_directive scopeOwner proofOwner
          proofAddress assertionLabel nextPairPosition pairEnd constantName
          leftTail rightBody sourceBody context))
  · exact normalDVLeftConstDirectiveAt_fires_tail scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd constantName
      leftTail rightBody sourceBody context

/-! ## Remaining unary scan phases -/

private def normalDVLeftVariableCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "source-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVLeftVariableRightTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .var "body", .var "body", .var "source-body", .var "context"]

def normalDVLeftVariablePhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVLeftVariableRule,
   normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
     nextPairPosition pairEnd (.var leftVariable :: leftTail) rightBody
     sourceBody context].toFinset

theorem normalDVLeftVariablePhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVLeftVariablePhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel nextPairPosition pairEnd leftVariable leftTail
            rightBody sourceBody context)) =
      some normalDVLeftVariableDirective := by
  let atoms :=
    [normalDVLeftVariableRule,
     normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
       nextPairPosition pairEnd (.var leftVariable :: leftTail) rightBody
       sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVLeftVariableDirective
  exact selectedUnaryPhase atoms normalDVLeftVariableDirective
    (by simp [atoms, normalDVLeftVariableRule, normalDVScanLeftRowAt])
    (by rfl)

private def normalDVLeftVariableSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

theorem normalDVLeftVariablePhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVLeftVariablePhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVLeftVariableDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd leftVariable leftTail rightBody rightBody
            sourceBody context ∈ target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let source := normalDVLeftVariablePhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable leftTail
    rightBody sourceBody context
  let cursor := normalDVScanLeftRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd (.var leftVariable :: leftTail)
    rightBody sourceBody context
  let substitution := normalDVLeftVariableSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable leftTail
    rightBody sourceBody context
  let output := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
    rightBody sourceBody context
  have cursorMem : cursor ∈ readCopyAtom source
      normalDVLeftVariableDirective.atom := by
    simp [source, cursor, readCopyAtom, consumeAtom,
      normalDVLeftVariablePhaseSpaceAt, normalDVLeftVariableDirective,
      normalDVLeftVariableRule, normalDVScanLeftRowAt]
  have matchExact : matchAtom [] normalDVLeftVariableCursorPatternAt cursor =
      some substitution := by
    simp [normalDVLeftVariableCursorPatternAt, cursor,
      normalDVScanLeftRowAt, substitution,
      normalDVLeftVariableSubstitutionAt, runtimeSymAtom, listAtom, consTag,
      variableTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  exact unaryDVPhase_inhabits_and_fires source normalDVLeftVariableDirective
    normalDVLeftVariableCursorPatternAt cursor substitution
    normalDVLeftVariableRightTemplateAt output proofOwner proofAddress
    (normalDVLeftVariablePhaseAt_selects_directive scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context)
    (by rfl) (by rfl) cursorMem matchExact (by rfl) (by rfl)

private def normalDVRightConstCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "actual-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVRightConstTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .var "actual-tail", .var "body", .var "source-body",
      .var "context"]

def normalDVRightConstPhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVRightConstRule,
   normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
     nextPairPosition pairEnd leftVariable leftTail
     (.const constantName :: rightTail) rightBody sourceBody context].toFinset

theorem normalDVRightConstPhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVRightConstPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel nextPairPosition pairEnd leftVariable constantName
            leftTail rightTail rightBody sourceBody context)) =
      some normalDVRightConstDirective := by
  let atoms :=
    [normalDVRightConstRule,
     normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
       nextPairPosition pairEnd leftVariable leftTail
       (.const constantName :: rightTail) rightBody sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVRightConstDirective
  exact selectedUnaryPhase atoms normalDVRightConstDirective
    (by simp [atoms, normalDVRightConstRule, normalDVScanRightRowAt])
    (by rfl)

private def normalDVRightConstSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("actual-tail", listAtom runtimeSymAtom rightTail),
   ("constant-name", stringAtom constantName),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

theorem normalDVRightConstPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVRightConstPhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      constantName leftTail rightTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVRightConstDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
            sourceBody context ∈ target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let source := normalDVRightConstPhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable
    constantName leftTail rightTail rightBody sourceBody context
  let cursor := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail
    (.const constantName :: rightTail) rightBody sourceBody context
  let substitution := normalDVRightConstSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable
    constantName leftTail rightTail rightBody sourceBody context
  let output := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail rightTail
    rightBody sourceBody context
  have cursorMem : cursor ∈ readCopyAtom source
      normalDVRightConstDirective.atom := by
    simp [source, cursor, readCopyAtom, consumeAtom,
      normalDVRightConstPhaseSpaceAt, normalDVRightConstDirective,
      normalDVRightConstRule, normalDVScanRightRowAt]
  have matchExact : matchAtom [] normalDVRightConstCursorPatternAt cursor =
      some substitution := by
    simp [normalDVRightConstCursorPatternAt, cursor,
      normalDVScanRightRowAt, substitution,
      normalDVRightConstSubstitutionAt, runtimeSymAtom, listAtom, consTag,
      constTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  exact unaryDVPhase_inhabits_and_fires source normalDVRightConstDirective
    normalDVRightConstCursorPatternAt cursor substitution
    normalDVRightConstTailTemplateAt output proofOwner proofAddress
    (normalDVRightConstPhaseAt_selects_directive scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      constantName leftTail rightTail rightBody sourceBody context)
    (by rfl) (by rfl) cursorMem matchExact (by rfl) (by rfl)

private def normalDVRightNilCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .expression [.symbol "mm-nil"], .var "body",
      .var "source-body", .var "context"]

private def normalDVRightNilLeftTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "source-tail", .var "body",
      .var "source-body", .var "context"]

def normalDVRightNilPhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVRightNilRule,
   normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
     nextPairPosition pairEnd leftVariable leftTail [] rightBody sourceBody
     context].toFinset

theorem normalDVRightNilPhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVRightNilPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel nextPairPosition pairEnd leftVariable leftTail
            rightBody sourceBody context)) =
      some normalDVRightNilDirective := by
  let atoms :=
    [normalDVRightNilRule,
     normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
       nextPairPosition pairEnd leftVariable leftTail [] rightBody sourceBody
       context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVRightNilDirective
  exact selectedUnaryPhase atoms normalDVRightNilDirective
    (by simp [atoms, normalDVRightNilRule, normalDVScanRightRowAt])
    (by rfl)

private def normalDVRightNilSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

theorem normalDVRightNilPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVRightNilPhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source normalDVRightNilDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
          target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let source := normalDVRightNilPhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable leftTail
    rightBody sourceBody context
  let cursor := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail [] rightBody
    sourceBody context
  let substitution := normalDVRightNilSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable leftTail
    rightBody sourceBody context
  let output := normalDVScanLeftRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftTail rightBody sourceBody
    context
  have cursorMem : cursor ∈ readCopyAtom source
      normalDVRightNilDirective.atom := by
    simp [source, cursor, readCopyAtom, consumeAtom,
      normalDVRightNilPhaseSpaceAt, normalDVRightNilDirective,
      normalDVRightNilRule, normalDVScanRightRowAt]
  have matchExact : matchAtom [] normalDVRightNilCursorPatternAt cursor =
      some substitution := by
    simp [normalDVRightNilCursorPatternAt, cursor,
      normalDVScanRightRowAt, substitution, normalDVRightNilSubstitutionAt,
      listAtom, nilTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  exact unaryDVPhase_inhabits_and_fires source normalDVRightNilDirective
    normalDVRightNilCursorPatternAt cursor substitution
    normalDVRightNilLeftTemplateAt output proofOwner proofAddress
    (normalDVRightNilPhaseAt_selects_directive scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context)
    (by rfl) (by rfl) cursorMem matchExact (by rfl) (by rfl)

private def normalDVLeftNilCursorPatternAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .expression [.symbol "mm-nil"],
      .var "body", .var "source-body", .var "context"]

private def normalDVLeftNilNextPairTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "source-body", .var "context"]

def normalDVLeftNilPhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVLeftNilRule,
   normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
     nextPairPosition pairEnd [] rightBody sourceBody context].toFinset

theorem normalDVLeftNilPhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVLeftNilPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel nextPairPosition pairEnd rightBody sourceBody
            context)) =
      some normalDVLeftNilDirective := by
  let atoms :=
    [normalDVLeftNilRule,
     normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
       nextPairPosition pairEnd [] rightBody sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVLeftNilDirective
  exact selectedUnaryPhase atoms normalDVLeftNilDirective
    (by simp [atoms, normalDVLeftNilRule, normalDVScanLeftRowAt])
    (by rfl)

private def normalDVLeftNilSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

theorem normalDVLeftNilPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVLeftNilPhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd rightBody
      sourceBody context
    let target := fireReflectiveSourceExecFact source normalDVLeftNilDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVNextPairRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd sourceBody context ∈ target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let source := normalDVLeftNilPhaseSpaceAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd rightBody sourceBody context
  let cursor := normalDVScanLeftRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd [] rightBody sourceBody context
  let substitution := normalDVLeftNilSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd rightBody sourceBody
    context
  let output := normalDVNextPairRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd sourceBody context
  have cursorMem : cursor ∈ readCopyAtom source
      normalDVLeftNilDirective.atom := by
    simp [source, cursor, readCopyAtom, consumeAtom,
      normalDVLeftNilPhaseSpaceAt, normalDVLeftNilDirective,
      normalDVLeftNilRule, normalDVScanLeftRowAt]
  have matchExact : matchAtom [] normalDVLeftNilCursorPatternAt cursor =
      some substitution := by
    simp [normalDVLeftNilCursorPatternAt, cursor,
      normalDVScanLeftRowAt, substitution, normalDVLeftNilSubstitutionAt,
      listAtom, nilTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  exact unaryDVPhase_inhabits_and_fires source normalDVLeftNilDirective
    normalDVLeftNilCursorPatternAt cursor substitution
    normalDVLeftNilNextPairTemplateAt output proofOwner proofAddress
    (normalDVLeftNilPhaseAt_selects_directive scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd rightBody sourceBody
      context)
    (by rfl) (by rfl) cursorMem matchExact (by rfl) (by rfl)

/-! ## Right-body variable step and caller-DV authority -/

private def normalDVRightVariablePatternAtomsAt : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end", .var "variable-name", .var "source-tail",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-variable", .var "hyp-label"],
            .var "actual-tail"],
        .var "body", .var "source-body", .var "context"],
   .expression
      [.symbol "mm-caller-dv", .var "scope",
        .var "variable-name", .var "hyp-label"]]

private def normalDVRightVariableCursorPatternAt : Atom :=
  normalDVRightVariablePatternAtomsAt[0]'(by decide)

private def normalDVRightVariableTailTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .var "actual-tail", .var "body", .var "source-body",
      .var "context"]

def normalDVRightVariablePhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVRightVariableRule,
   normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
     nextPairPosition pairEnd leftVariable leftTail
     (.var rightVariable :: rightTail) rightBody sourceBody context,
   callerDVRow scopeOwner leftVariable rightVariable].toFinset

theorem normalDVRightVariablePhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVRightVariablePhaseSpaceAt scopeOwner proofOwner
            proofAddress assertionLabel nextPairPosition pairEnd leftVariable
            rightVariable leftTail rightTail rightBody sourceBody context)) =
      some normalDVRightVariableDirective := by
  let atoms :=
    [normalDVRightVariableRule,
     normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
       nextPairPosition pairEnd leftVariable leftTail
       (.var rightVariable :: rightTail) rightBody sourceBody context,
     callerDVRow scopeOwner leftVariable rightVariable]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVRightVariableDirective
  exact selectedUnaryPhase atoms normalDVRightVariableDirective
    (by
      simp [atoms, normalDVRightVariableRule, normalDVScanRightRowAt,
        callerDVRow])
    (by rfl)

private def normalDVRightVariableSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("actual-tail", listAtom runtimeSymAtom rightTail),
   ("hyp-label", stringAtom rightVariable),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

private theorem normalDVRightVariableMatchRowAt_mem
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVRightVariableSubstitutionAt scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable rightVariable
        leftTail rightTail rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVRightVariablePhaseSpaceAt scopeOwner proofOwner
            proofAddress assertionLabel nextPairPosition pairEnd leftVariable
            rightVariable leftTail rightTail rightBody sourceBody context)
          normalDVRightVariableRule)
        normalDVRightVariableDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail
    (.var rightVariable :: rightTail) rightBody sourceBody context
  let obligation := callerDVRow scopeOwner leftVariable rightVariable
  let substitution := normalDVRightVariableSubstitutionAt scopeOwner
    proofOwner proofAddress assertionLabel nextPairPosition pairEnd
    leftVariable rightVariable leftTail rightTail rightBody sourceBody context
  let read := readCopyAtom
    (normalDVRightVariablePhaseSpaceAt scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd leftVariable rightVariable
      leftTail rightTail rightBody sourceBody context)
    normalDVRightVariableRule
  have cursorMem : cursor ∈ read := by
    simp [read, cursor, readCopyAtom, consumeAtom,
      normalDVRightVariablePhaseSpaceAt, normalDVRightVariableRule,
      normalDVScanRightRowAt]
  have obligationMem : obligation ∈ read := by
    simp [read, obligation, readCopyAtom, consumeAtom,
      normalDVRightVariablePhaseSpaceAt, normalDVRightVariableRule,
      callerDVRow]
  have matchCursor :
      matchAtom [] normalDVRightVariableCursorPatternAt cursor =
        some substitution := by
    simp [normalDVRightVariableCursorPatternAt,
      normalDVRightVariablePatternAtomsAt, cursor, normalDVScanRightRowAt,
      substitution, normalDVRightVariableSubstitutionAt, runtimeSymAtom,
      listAtom, consTag, variableTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchObligation :
      matchAtom substitution
          (normalDVRightVariablePatternAtomsAt[1]'(by decide)) obligation =
        some substitution := by
    simp [normalDVRightVariablePatternAtomsAt, obligation, callerDVRow,
      substitution, normalDVRightVariableSubstitutionAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor, obligation}), ?_, rfl⟩
  have inputExact : normalDVRightVariableDirective.rule.input =
      .compat (mkPattern normalDVRightVariablePatternAtomsAt) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, normalDVRightVariablePatternAtomsAt, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution matchCursor,
    ?_⟩
  refine ⟨(substitution, obligation),
    matchOneInSpace_mem substitution _ read obligation obligationMem
      substitution matchObligation, ?_⟩
  simp [substitution, cursor, obligation]

theorem normalDVRightVariablePhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVRightVariablePhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel nextPairPosition pairEnd leftVariable
      rightVariable leftTail rightTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVRightVariableDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
            sourceBody context ∈ target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let source := normalDVRightVariablePhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable
    rightVariable leftTail rightTail rightBody sourceBody context
  let rows := (matchInputSpec []
    (readCopyAtom source normalDVRightVariableDirective.atom)
    normalDVRightVariableDirective.rule.input).map Prod.fst
  let substitution := normalDVRightVariableSubstitutionAt scopeOwner
    proofOwner proofAddress assertionLabel nextPairPosition pairEnd
    leftVariable rightVariable leftTail rightTail rightBody sourceBody context
  let output := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail rightTail
    rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, source, substitution, normalDVRightVariableDirective] using
      normalDVRightVariableMatchRowAt_mem scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable rightVariable
        leftTail rightTail rightBody sourceBody context
  have outputInstantiates :
      instantiateTemplateAtom? substitution
          normalDVRightVariableTailTemplateAt = some output := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVReloadTemplateAt =
        some (normalDVReloadRowAt proofOwner proofAddress) := by
    rfl
  have outputStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVRightVariableTailTemplateAt output rowMember outputInstantiates
  have reloadStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVReloadTemplateAt (normalDVReloadRowAt proofOwner proofAddress)
    rowMember reloadInstantiates
  refine ⟨reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalDVRightVariablePhaseAt_selects_directive scopeOwner proofOwner
        proofAddress assertionLabel nextPairPosition pairEnd leftVariable
        rightVariable leftTail rightTail rightBody sourceBody context)),
    ?_, ?_⟩
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightVariableDirective]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr outputStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightVariableDirective]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- The variable branch cannot discharge its second authored premise without
the exact caller-DV row. -/
theorem normalDVRightVariableAt_missing_caller_rejects_obligation
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let cursor := normalDVScanRightRowAt scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd leftVariable leftTail
      (.var rightVariable :: rightTail) rightBody sourceBody context
    let source : Space := [normalDVRightVariableRule, cursor].toFinset
    matchOneInSpace
        (normalDVRightVariableSubstitutionAt scopeOwner proofOwner
          proofAddress assertionLabel nextPairPosition pairEnd leftVariable
          rightVariable leftTail rightTail rightBody sourceBody context)
        (normalDVRightVariablePatternAtomsAt[1]'(by decide))
        (readCopyAtom source normalDVRightVariableRule) = [] := by
  dsimp only
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨candidateSubstitution, candidateAtom⟩ candidateMember
  have candidateSpec := matchOneInSpace_spec
    (normalDVRightVariableSubstitutionAt scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd leftVariable rightVariable
      leftTail rightTail rightBody sourceBody context)
    (normalDVRightVariablePatternAtomsAt[1]'(by decide))
    (readCopyAtom
      ([normalDVRightVariableRule,
        normalDVScanRightRowAt scopeOwner proofOwner proofAddress
          assertionLabel nextPairPosition pairEnd leftVariable leftTail
          (.var rightVariable :: rightTail) rightBody sourceBody context]
        ).toFinset normalDVRightVariableRule)
    candidateSubstitution candidateAtom candidateMember
  rcases candidateSpec with ⟨candidateInRead, candidateMatches⟩
  have candidateCases :
      candidateAtom = normalDVRightVariableRule ∨
        (candidateAtom ≠ normalDVRightVariableRule ∧
          candidateAtom = normalDVScanRightRowAt scopeOwner proofOwner
            proofAddress assertionLabel nextPairPosition pairEnd leftVariable
            leftTail (.var rightVariable :: rightTail) rightBody sourceBody
            context) := by
    simpa [readCopyAtom, consumeAtom] using candidateInRead
  rcases candidateCases with ruleCase | ⟨_, cursorCase⟩
  · subst candidateAtom
    simp [normalDVRightVariablePatternAtomsAt,
      normalDVRightVariableRule, matchAtom, matchAtom.matchAtomList]
      at candidateMatches
  · subst candidateAtom
    simp [normalDVRightVariablePatternAtomsAt, normalDVScanRightRowAt,
      runtimeSymAtom, listAtom, consTag, variableTag, matchAtom,
      matchAtom.matchAtomList] at candidateMatches

/-! ## Assertion-finish handoff into the addressed DV machine -/

private def normalAssertionFinishPatternAtomsAt : List Atom :=
  [.expression
      [.symbol "mm-assertion-bind", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label", .var "hyp-end",
        .var "hyp-end", .var "stack-end", .var "stack-base"],
   .expression
      [.symbol "mm-assertion-result", .var "scope", .var "label",
        .var "result-typecode", .var "source-body"],
   .expression
      [.symbol "mm-assertion-dv-header", .var "scope", .var "label",
        .var "assertion-position"],
   .expression
      [.symbol "mm-index-successor", .var "proof", .var "stack-base",
        .var "next-top"]]

private def normalAssertionFinishNextPairTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", natAtom 0, .var "assertion-position",
      .var "source-body",
      .expression
        [.symbol "mm-assertion-result-context", .var "scope",
          .var "next-pc", .var "label", .var "result-typecode",
          .var "stack-base", .var "next-top"]]

def normalAssertionFinishPhaseAtomsAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) : List Atom :=
  [normalAssertionFinishRule,
   normalAssertionBindRowAt scopeOwner proofOwner segment assertionLabel
     hypothesisEnd hypothesisEnd stackEnd stackBase,
   normalAssertionResultAtom scopeOwner assertionLabel resultTypecode
     sourceBody,
   .expression
      [.symbol "mm-assertion-dv-header", scopeOwner,
        stringAtom assertionLabel, natAtom dvEnd],
   segment.stackSuccessorRow proofOwner stackBase]

def normalAssertionFinishPhaseSpaceAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) : Space :=
  (normalAssertionFinishPhaseAtomsAt scopeOwner proofOwner segment
    assertionLabel hypothesisEnd stackEnd stackBase resultTypecode sourceBody
    dvEnd).toFinset

private theorem normalAssertionFinishPhaseAtomsAt_nodup
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) :
    (normalAssertionFinishPhaseAtomsAt scopeOwner proofOwner segment
      assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
      sourceBody dvEnd).Nodup := by
  simp [normalAssertionFinishPhaseAtomsAt, normalAssertionFinishRule,
    normalAssertionBindRowAt, normalAssertionResultAtom,
    NormalAddressSegment.stackSuccessorRow]

theorem normalAssertionFinishPhaseAt_selects_directive
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionFinishPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
            sourceBody dvEnd)) =
      some normalAssertionFinishDirective := by
  let atoms := normalAssertionFinishPhaseAtomsAt scopeOwner proofOwner
    segment assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
    sourceBody dvEnd
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionFinishDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionFinishDirective
    (normalAssertionFinishPhaseAtomsAt_nodup scopeOwner proofOwner segment
      assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
      sourceBody dvEnd)
    (by rfl)

private def normalAssertionFinishSubstitutionAt
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) : Subst :=
  [("next-top", segment.stackAddress (stackBase + 1)),
   ("assertion-position", natAtom dvEnd),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("result-typecode", stringAtom resultTypecode),
   ("stack-base", segment.stackAddress stackBase),
   ("stack-end", segment.stackAddress stackEnd),
   ("hyp-end", natAtom hypothesisEnd),
   ("label", stringAtom assertionLabel), ("next-pc", segment.nextProof),
   ("pc", segment.currentProof), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalAssertionFinishMatchRowAt_mem
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) :
    normalAssertionFinishSubstitutionAt scopeOwner proofOwner segment
        assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
        sourceBody dvEnd ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionFinishPhaseSpaceAt scopeOwner proofOwner segment
            assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
            sourceBody dvEnd)
          normalAssertionFinishRule)
        normalAssertionFinishDirective.rule.input).map Prod.fst := by
  let bind := normalAssertionBindRowAt scopeOwner proofOwner segment
    assertionLabel hypothesisEnd hypothesisEnd stackEnd stackBase
  let resultRow := normalAssertionResultAtom scopeOwner assertionLabel
    resultTypecode sourceBody
  let dvHeader : Atom :=
    .expression
      [.symbol "mm-assertion-dv-header", scopeOwner,
        stringAtom assertionLabel, natAtom dvEnd]
  let successor := segment.stackSuccessorRow proofOwner stackBase
  let read := readCopyAtom
    (normalAssertionFinishPhaseSpaceAt scopeOwner proofOwner segment
      assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
      sourceBody dvEnd) normalAssertionFinishRule
  let afterBind : Subst :=
    [("stack-base", segment.stackAddress stackBase),
     ("stack-end", segment.stackAddress stackEnd),
     ("hyp-end", natAtom hypothesisEnd),
     ("label", stringAtom assertionLabel),
     ("next-pc", segment.nextProof), ("pc", segment.currentProof),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let afterResult : Subst :=
    [("source-body", listAtom runtimeSymAtom sourceBody),
     ("result-typecode", stringAtom resultTypecode)] ++ afterBind
  let afterDV : Subst :=
    ("assertion-position", natAtom dvEnd) :: afterResult
  let finalRow := normalAssertionFinishSubstitutionAt scopeOwner proofOwner
    segment assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
    sourceBody dvEnd
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionFinishPhaseSpaceAt scopeOwner
        proofOwner segment assertionLabel hypothesisEnd stackEnd stackBase
        resultTypecode sourceBody dvEnd) : atom ∈ read := by
    by_cases equal : atom = normalAssertionFinishRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have bindMem : bind ∈ read := by
    apply readMember
    simp [bind, normalAssertionFinishPhaseSpaceAt,
      normalAssertionFinishPhaseAtomsAt]
  have resultMem : resultRow ∈ read := by
    apply readMember
    simp [resultRow, normalAssertionFinishPhaseSpaceAt,
      normalAssertionFinishPhaseAtomsAt]
  have dvMem : dvHeader ∈ read := by
    apply readMember
    simp [dvHeader, normalAssertionFinishPhaseSpaceAt,
      normalAssertionFinishPhaseAtomsAt]
  have successorMem : successor ∈ read := by
    apply readMember
    simp [successor, normalAssertionFinishPhaseSpaceAt,
      normalAssertionFinishPhaseAtomsAt]
  have matchBind :
      matchAtom [] (normalAssertionFinishPatternAtomsAt[0]'(by decide))
          bind = some afterBind := by
    simp [normalAssertionFinishPatternAtomsAt, bind,
      normalAssertionBindRowAt, afterBind, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchResult :
      matchAtom afterBind
          (normalAssertionFinishPatternAtomsAt[1]'(by decide)) resultRow =
        some afterResult := by
    simp [normalAssertionFinishPatternAtomsAt, resultRow,
      normalAssertionResultAtom, afterBind, afterResult, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchDV :
      matchAtom afterResult
          (normalAssertionFinishPatternAtomsAt[2]'(by decide)) dvHeader =
        some afterDV := by
    simp [normalAssertionFinishPatternAtomsAt, dvHeader, afterResult, afterDV,
      afterBind, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchSuccessor :
      matchAtom afterDV
          (normalAssertionFinishPatternAtomsAt[3]'(by decide)) successor =
        some finalRow := by
    simp [normalAssertionFinishPatternAtomsAt, successor,
      NormalAddressSegment.stackSuccessorRow, afterDV, afterResult,
      afterBind, finalRow, normalAssertionFinishSubstitutionAt, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {bind, resultRow, dvHeader, successor}), ?_, rfl⟩
  have inputExact : normalAssertionFinishDirective.rule.input =
      .compat (mkPattern normalAssertionFinishPatternAtomsAt) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, normalAssertionFinishPatternAtomsAt, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterBind, bind),
    matchOneInSpace_mem [] _ read bind bindMem afterBind matchBind, ?_⟩
  refine ⟨(afterResult, resultRow),
    matchOneInSpace_mem afterBind _ read resultRow resultMem afterResult
      matchResult, ?_⟩
  refine ⟨(afterDV, dvHeader),
    matchOneInSpace_mem afterResult _ read dvHeader dvMem afterDV matchDV,
    ?_⟩
  refine ⟨(finalRow, successor),
    matchOneInSpace_mem afterDV _ read successor successorMem finalRow
      matchSuccessor, ?_⟩
  simp [finalRow, bind, resultRow, dvHeader, successor]

theorem normalAssertionFinishPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner : Atom) (segment : NormalAddressSegment)
    (assertionLabel : String) (hypothesisEnd stackEnd stackBase : Nat)
    (resultTypecode : String) (sourceBody : List Metamath.Verify.Sym)
    (dvEnd : Nat) :
    let context := segment.resultContext scopeOwner assertionLabel
      resultTypecode stackBase
    let source := normalAssertionFinishPhaseSpaceAt scopeOwner proofOwner
      segment assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
      sourceBody dvEnd
    let target := fireReflectiveSourceExecFact source
      normalAssertionFinishDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVNextPairRowAt scopeOwner proofOwner segment.currentProof
            assertionLabel 0 dvEnd sourceBody context ∈ target ∧
        normalDVReloadRowAt proofOwner segment.currentProof ∈ target := by
  dsimp only
  let source := normalAssertionFinishPhaseSpaceAt scopeOwner proofOwner
    segment assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
    sourceBody dvEnd
  let rows := (matchInputSpec []
    (readCopyAtom source normalAssertionFinishDirective.atom)
    normalAssertionFinishDirective.rule.input).map Prod.fst
  let substitution := normalAssertionFinishSubstitutionAt scopeOwner
    proofOwner segment assertionLabel hypothesisEnd stackEnd stackBase
    resultTypecode sourceBody dvEnd
  let output := normalDVNextPairRowAt scopeOwner proofOwner
    segment.currentProof assertionLabel 0 dvEnd sourceBody
    (segment.resultContext scopeOwner assertionLabel resultTypecode stackBase)
  have rowMember : substitution ∈ rows := by
    simpa [rows, source, substitution, normalAssertionFinishDirective] using
      normalAssertionFinishMatchRowAt_mem scopeOwner proofOwner segment
        assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
        sourceBody dvEnd
  have outputInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionFinishNextPairTemplateAt = some output := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVReloadTemplateAt =
        some (normalDVReloadRowAt proofOwner segment.currentProof) := by
    rfl
  have outputStaged := addressedStageAdd_contains_of_row rows substitution
    normalAssertionFinishNextPairTemplateAt output rowMember
    outputInstantiates
  have reloadStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVReloadTemplateAt
    (normalDVReloadRowAt proofOwner segment.currentProof) rowMember
    reloadInstantiates
  refine ⟨reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalAssertionFinishPhaseAt_selects_directive scopeOwner proofOwner
        segment assertionLabel hypothesisEnd stackEnd stackBase resultTypecode
        sourceBody dvEnd)), ?_, ?_⟩
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionFinishDirective]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr outputStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionFinishDirective]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-! ## Ordered pair entry -/

private def normalDVPairBeginPatternAtomsAt : List Atom :=
  [.expression
      [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
        .var "pc", .var "label", .var "hyp-position",
        .var "hyp-end", .var "source-body", .var "context"],
   .expression
      [.symbol "mm-assertion-dv-pair", .var "scope", .var "label",
        .var "hyp-position", .var "variable-name", .var "hyp-label"],
   .expression
      [.symbol "mm-assertion-dv-successor", .var "scope", .var "label",
        .var "hyp-position", .var "next-hyp-position"],
   .expression
      [.symbol "mm-substitution", .var "proof", .var "pc",
        .var "variable-name", .var "actual-body"],
   .expression
      [.symbol "mm-substitution", .var "proof", .var "pc",
        .var "hyp-label", .var "body"]]

private def normalDVPairBeginScanTemplateAt : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "actual-body", .var "body",
      .var "source-body", .var "context"]

def normalDVPairBeginPhaseAtomsAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : List Atom :=
  [normalDVPairBeginRule,
   normalDVNextPairRowAt scopeOwner proofOwner proofAddress assertionLabel
     pairPosition pairEnd sourceBody context,
   .expression
      [.symbol "mm-assertion-dv-pair", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        stringAtom leftVariable, stringAtom rightVariable],
   .expression
      [.symbol "mm-assertion-dv-successor", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        natAtom nextPairPosition],
   normalAssertionSubstitutionRowAt proofOwner proofAddress leftVariable
     leftBody,
   normalAssertionSubstitutionRowAt proofOwner proofAddress rightVariable
     rightBody]

def normalDVPairBeginPhaseSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  (normalDVPairBeginPhaseAtomsAt scopeOwner proofOwner proofAddress
    assertionLabel pairPosition nextPairPosition pairEnd leftVariable
    rightVariable leftBody rightBody sourceBody context).toFinset

private theorem normalDVPairBeginPhaseAtomsAt_nodup
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (variablesDistinct : leftVariable ≠ rightVariable) :
    (normalDVPairBeginPhaseAtomsAt scopeOwner proofOwner proofAddress
      assertionLabel pairPosition nextPairPosition pairEnd leftVariable
      rightVariable leftBody rightBody sourceBody context).Nodup := by
  have encodedDistinct :
      stringAtom leftVariable ≠ stringAtom rightVariable := by
    intro equal
    exact variablesDistinct (stringAtom_injective equal)
  simp [normalDVPairBeginPhaseAtomsAt, normalDVPairBeginRule,
    normalDVNextPairRowAt, normalAssertionSubstitutionRowAt,
    encodedDistinct]

theorem normalDVPairBeginPhaseAt_selects_directive
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (variablesDistinct : leftVariable ≠ rightVariable) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel pairPosition nextPairPosition pairEnd leftVariable
            rightVariable leftBody rightBody sourceBody context)) =
      some normalDVPairBeginDirective := by
  let atoms := normalDVPairBeginPhaseAtomsAt scopeOwner proofOwner
    proofAddress assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVPairBeginDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVPairBeginDirective
    (normalDVPairBeginPhaseAtomsAt_nodup scopeOwner proofOwner proofAddress
      assertionLabel pairPosition nextPairPosition pairEnd leftVariable
      rightVariable leftBody rightBody sourceBody context variablesDistinct)
    (by rfl)

private def normalDVPairBeginSubstitutionAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("body", listAtom runtimeSymAtom rightBody),
   ("actual-body", listAtom runtimeSymAtom leftBody),
   ("next-hyp-position", natAtom nextPairPosition),
   ("hyp-label", stringAtom rightVariable),
   ("variable-name", stringAtom leftVariable),
   ("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("hyp-end", natAtom pairEnd),
   ("hyp-position", natAtom pairPosition),
   ("label", stringAtom assertionLabel), ("pc", proofAddress),
   ("proof", proofOwner), ("scope", scopeOwner)]

private theorem normalDVPairBeginMatchRowAt_mem
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVPairBeginSubstitutionAt scopeOwner proofOwner proofAddress
        assertionLabel pairPosition nextPairPosition pairEnd leftVariable
        rightVariable leftBody rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel pairPosition nextPairPosition pairEnd leftVariable
            rightVariable leftBody rightBody sourceBody context)
          normalDVPairBeginRule)
        normalDVPairBeginDirective.rule.input).map Prod.fst := by
  let cursor := normalDVNextPairRowAt scopeOwner proofOwner proofAddress
    assertionLabel pairPosition pairEnd sourceBody context
  let pairRow : Atom :=
    .expression
      [.symbol "mm-assertion-dv-pair", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        stringAtom leftVariable, stringAtom rightVariable]
  let successor : Atom :=
    .expression
      [.symbol "mm-assertion-dv-successor", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        natAtom nextPairPosition]
  let leftRow := normalAssertionSubstitutionRowAt proofOwner proofAddress
    leftVariable leftBody
  let rightRow := normalAssertionSubstitutionRowAt proofOwner proofAddress
    rightVariable rightBody
  let read := readCopyAtom
    (normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner proofAddress
      assertionLabel pairPosition nextPairPosition pairEnd leftVariable
      rightVariable leftBody rightBody sourceBody context)
    normalDVPairBeginRule
  let afterCursor : Subst :=
    [("context", context),
     ("source-body", listAtom runtimeSymAtom sourceBody),
     ("hyp-end", natAtom pairEnd),
     ("hyp-position", natAtom pairPosition),
     ("label", stringAtom assertionLabel), ("pc", proofAddress),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let afterPair : Subst :=
    [("hyp-label", stringAtom rightVariable),
     ("variable-name", stringAtom leftVariable)] ++ afterCursor
  let afterSuccessor : Subst :=
    ("next-hyp-position", natAtom nextPairPosition) :: afterPair
  let afterLeft : Subst :=
    ("actual-body", listAtom runtimeSymAtom leftBody) :: afterSuccessor
  let finalRow := normalDVPairBeginSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  have readMember (atom : Atom)
      (member : atom ∈ normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner
        proofAddress assertionLabel pairPosition nextPairPosition pairEnd
        leftVariable rightVariable leftBody rightBody sourceBody context) :
      atom ∈ read := by
    by_cases equal : atom = normalDVPairBeginRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have cursorMem : cursor ∈ read := by
    apply readMember
    simp [cursor, normalDVPairBeginPhaseSpaceAt,
      normalDVPairBeginPhaseAtomsAt]
  have pairMem : pairRow ∈ read := by
    apply readMember
    simp [pairRow, normalDVPairBeginPhaseSpaceAt,
      normalDVPairBeginPhaseAtomsAt]
  have successorMem : successor ∈ read := by
    apply readMember
    simp [successor, normalDVPairBeginPhaseSpaceAt,
      normalDVPairBeginPhaseAtomsAt]
  have leftMem : leftRow ∈ read := by
    apply readMember
    simp [leftRow, normalDVPairBeginPhaseSpaceAt,
      normalDVPairBeginPhaseAtomsAt]
  have rightMem : rightRow ∈ read := by
    apply readMember
    simp [rightRow, normalDVPairBeginPhaseSpaceAt,
      normalDVPairBeginPhaseAtomsAt]
  have matchCursor :
      matchAtom [] (normalDVPairBeginPatternAtomsAt[0]'(by decide)) cursor =
        some afterCursor := by
    simp [normalDVPairBeginPatternAtomsAt, cursor, normalDVNextPairRowAt,
      afterCursor, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchPair :
      matchAtom afterCursor
          (normalDVPairBeginPatternAtomsAt[1]'(by decide)) pairRow =
        some afterPair := by
    simp [normalDVPairBeginPatternAtomsAt, pairRow, afterCursor, afterPair,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchSuccessor :
      matchAtom afterPair
          (normalDVPairBeginPatternAtomsAt[2]'(by decide)) successor =
        some afterSuccessor := by
    simp [normalDVPairBeginPatternAtomsAt, successor, afterPair,
      afterSuccessor, afterCursor, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchLeft :
      matchAtom afterSuccessor
          (normalDVPairBeginPatternAtomsAt[3]'(by decide)) leftRow =
        some afterLeft := by
    simp [normalDVPairBeginPatternAtomsAt, leftRow,
      normalAssertionSubstitutionRowAt, afterSuccessor, afterPair,
      afterCursor, afterLeft, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchRight :
      matchAtom afterLeft
          (normalDVPairBeginPatternAtomsAt[4]'(by decide)) rightRow =
        some finalRow := by
    simp [normalDVPairBeginPatternAtomsAt, rightRow,
      normalAssertionSubstitutionRowAt, afterLeft, afterSuccessor,
      afterPair, afterCursor, finalRow, normalDVPairBeginSubstitutionAt,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {cursor, pairRow, successor, leftRow, rightRow}), ?_,
    rfl⟩
  have inputExact : normalDVPairBeginDirective.rule.input =
      .compat (mkPattern normalDVPairBeginPatternAtomsAt) := by
    rfl
  rw [inputExact]
  simp only [matchInputSpec, normalDVPairBeginPatternAtomsAt, mkPattern,
    matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterCursor, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem afterCursor matchCursor,
    ?_⟩
  refine ⟨(afterPair, pairRow),
    matchOneInSpace_mem afterCursor _ read pairRow pairMem afterPair
      matchPair, ?_⟩
  refine ⟨(afterSuccessor, successor),
    matchOneInSpace_mem afterPair _ read successor successorMem
      afterSuccessor matchSuccessor, ?_⟩
  refine ⟨(afterLeft, leftRow),
    matchOneInSpace_mem afterSuccessor _ read leftRow leftMem afterLeft
      matchLeft, ?_⟩
  refine ⟨(finalRow, rightRow),
    matchOneInSpace_mem afterLeft _ read rightRow rightMem finalRow
      matchRight, ?_⟩
  simp [finalRow, cursor, pairRow, successor, leftRow, rightRow]

theorem normalDVPairBeginPhaseAt_inhabits_target_native_type
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (variablesDistinct : leftVariable ≠ rightVariable) :
    let source := normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner
      proofAddress assertionLabel pairPosition nextPairPosition pairEnd
      leftVariable rightVariable leftBody rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source normalDVPairBeginDirective
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
            nextPairPosition pairEnd leftBody rightBody sourceBody context ∈
          target ∧
        normalDVReloadRowAt proofOwner proofAddress ∈ target := by
  dsimp only
  let source := normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  let rows := (matchInputSpec []
    (readCopyAtom source normalDVPairBeginDirective.atom)
    normalDVPairBeginDirective.rule.input).map Prod.fst
  let substitution := normalDVPairBeginSubstitutionAt scopeOwner proofOwner
    proofAddress assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  let output := normalDVScanLeftRowAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftBody rightBody sourceBody
    context
  have rowMember : substitution ∈ rows := by
    simpa [rows, source, substitution, normalDVPairBeginDirective] using
      normalDVPairBeginMatchRowAt_mem scopeOwner proofOwner proofAddress
        assertionLabel pairPosition nextPairPosition pairEnd leftVariable
        rightVariable leftBody rightBody sourceBody context
  have outputInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginScanTemplateAt =
        some output := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVReloadTemplateAt =
        some (normalDVReloadRowAt proofOwner proofAddress) := by
    rfl
  have outputStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVPairBeginScanTemplateAt output rowMember outputInstantiates
  have reloadStaged := addressedStageAdd_contains_of_row rows substitution
    normalDVReloadTemplateAt (normalDVReloadRowAt proofOwner proofAddress)
    rowMember reloadInstantiates
  refine ⟨reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalDVPairBeginPhaseAt_selects_directive scopeOwner proofOwner
        proofAddress assertionLabel pairPosition nextPairPosition pairEnd
        leftVariable rightVariable leftBody rightBody sourceBody context
        variablesDistinct)), ?_, ?_⟩
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVPairBeginDirective]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr outputStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVPairBeginDirective]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-! ## Recursive addressed semantic traces -/

def AddressedDVReloadStep (proofOwner proofAddress : Atom) : Prop :=
  let source := normalDVReloadPhaseSpaceAt proofOwner proofAddress
  let target := fireReflectiveSourceExecFact source normalDVReloadDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
    (reflectiveSourceExecExactTargetNativeType target).pred

def AddressedDVRightConstStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVRightConstPhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable
    constantName leftTail rightTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVRightConstDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
          sourceBody context ∈ target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

def AddressedDVRightVariableStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVRightVariablePhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable
    rightVariable leftTail rightTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVRightVariableDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
          sourceBody context ∈ target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

def AddressedDVRightNilStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVRightNilPhaseSpaceAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
    sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVRightNilDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

inductive AddressedDVRightTrace
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : List Metamath.Verify.Sym → Prop where
  | nil
      (nativeStep : AddressedDVRightNilStep scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress) :
      AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context []
  | const (constantName : String) (rightTail : List Metamath.Verify.Sym)
      (nativeStep : AddressedDVRightConstStep scopeOwner proofOwner
        proofAddress assertionLabel nextPairPosition pairEnd leftVariable
        constantName leftTail rightTail rightBody sourceBody context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress)
      (tail : AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context rightTail) :
      AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context (.const constantName :: rightTail)
  | var (rightVariable : String)
      (rightTail : List Metamath.Verify.Sym)
      (callerRow : callerDVRow scopeOwner leftVariable rightVariable ∈
        callerDVRowsOfPairs scopeOwner callerDV)
      (nativeStep : AddressedDVRightVariableStep scopeOwner proofOwner
        proofAddress assertionLabel nextPairPosition pairEnd leftVariable
        rightVariable leftTail rightTail rightBody sourceBody context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress)
      (tail : AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context rightTail) :
      AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context (.var rightVariable :: rightTail)

theorem addressedDVRightTrace_of_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (rightScan : List Metamath.Verify.Sym)
    (semantics : AllWithSemantics callerDV leftVariable
      (BodyVariables rightScan)) :
    AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
      sourceBody context rightScan := by
  induction rightScan with
  | nil =>
      exact .nil
        (normalDVRightNilPhaseAt_inhabits_target_native_type scopeOwner
          proofOwner proofAddress assertionLabel nextPairPosition pairEnd
          leftVariable leftTail rightBody sourceBody context)
        (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
          proofAddress)
  | cons symbol rightTail inductionHypothesis =>
      cases symbol with
      | const constantName =>
          have tailSemantics : AllWithSemantics callerDV leftVariable
              (BodyVariables rightTail) := by
            simpa [BodyVariables] using semantics
          exact .const constantName rightTail
            (normalDVRightConstPhaseAt_inhabits_target_native_type scopeOwner
              proofOwner proofAddress assertionLabel nextPairPosition pairEnd
              leftVariable constantName leftTail rightTail rightBody
              sourceBody context)
            (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
              proofAddress)
            (inductionHypothesis tailSemantics)
      | var rightVariable =>
          have relation : DVRelation callerDV leftVariable rightVariable :=
            semantics rightVariable (by simp [BodyVariables])
          have tailSemantics : AllWithSemantics callerDV leftVariable
              (BodyVariables rightTail) := by
            intro right member
            exact semantics right (by simp [BodyVariables, member])
          exact .var rightVariable rightTail
            ((callerDVRow_mem_callerDVRowsOfPairs_iff scopeOwner callerDV
              leftVariable rightVariable).2 relation)
            (normalDVRightVariablePhaseAt_inhabits_target_native_type
              scopeOwner proofOwner proofAddress assertionLabel
              nextPairPosition pairEnd leftVariable rightVariable leftTail
              rightTail rightBody sourceBody context)
            (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
              proofAddress)
            (inductionHypothesis tailSemantics)

theorem AddressedDVRightTrace.reflects_semantics
    {callerDV : List (String × String)}
    {scopeOwner proofOwner proofAddress : Atom}
    {assertionLabel : String} {nextPairPosition pairEnd : Nat}
    {leftVariable : String}
    {leftTail rightBody sourceBody : List Metamath.Verify.Sym}
    {context : Atom} {rightScan : List Metamath.Verify.Sym}
    (trace : AddressedDVRightTrace callerDV scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
      sourceBody context rightScan) :
    AllWithSemantics callerDV leftVariable (BodyVariables rightScan) := by
  induction trace with
  | nil =>
      intro right member
      simp [BodyVariables] at member
  | const constantName rightTail nativeStep reloadStep tail induction =>
      simpa [BodyVariables] using induction
  | var rightVariable rightTail callerRow nativeStep reloadStep tail
      induction =>
      intro right member
      simp only [BodyVariables, List.mem_cons] at member
      rcases member with equal | member
      · subst right
        exact (callerDVRow_mem_callerDVRowsOfPairs_iff scopeOwner callerDV
          leftVariable rightVariable).1 callerRow
      · exact induction right member

def AddressedDVLeftConstStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVLeftConstPhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd constantName
    leftTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVLeftConstDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

def AddressedDVLeftVariableStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVLeftVariablePhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source
    normalDVLeftVariableDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanRightRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightBody rightBody
          sourceBody context ∈ target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

def AddressedDVLeftNilStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVLeftNilPhaseSpaceAt scopeOwner proofOwner proofAddress
    assertionLabel nextPairPosition pairEnd rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVLeftNilDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVNextPairRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd sourceBody context ∈ target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

inductive AddressedDVLeftTrace
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : List Metamath.Verify.Sym → Prop where
  | nil
      (nativeStep : AddressedDVLeftNilStep scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress) :
      AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context []
  | const (constantName : String) (leftTail : List Metamath.Verify.Sym)
      (nativeStep : AddressedDVLeftConstStep scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress)
      (tail : AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        leftTail) :
      AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        (.const constantName :: leftTail)
  | var (leftVariable : String) (leftTail : List Metamath.Verify.Sym)
      (nativeStep : AddressedDVLeftVariableStep scopeOwner proofOwner
        proofAddress assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress)
      (right : AddressedDVRightTrace callerDV scopeOwner proofOwner
        proofAddress assertionLabel nextPairPosition pairEnd leftVariable
        leftTail rightBody sourceBody context rightBody)
      (tail : AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        leftTail) :
      AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
        (.var leftVariable :: leftTail)

theorem addressedDVLeftTrace_of_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (leftScan : List Metamath.Verify.Sym)
    (semantics : AllPairsSemantics callerDV (BodyVariables leftScan)
      (BodyVariables rightBody)) :
    AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd rightBody sourceBody context
      leftScan := by
  induction leftScan with
  | nil =>
      exact .nil
        (normalDVLeftNilPhaseAt_inhabits_target_native_type scopeOwner
          proofOwner proofAddress assertionLabel nextPairPosition pairEnd
          rightBody sourceBody context)
        (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
          proofAddress)
  | cons symbol leftTail inductionHypothesis =>
      cases symbol with
      | const constantName =>
          have tailSemantics : AllPairsSemantics callerDV
              (BodyVariables leftTail) (BodyVariables rightBody) := by
            simpa [BodyVariables] using semantics
          exact .const constantName leftTail
            (normalDVLeftConstPhaseAt_inhabits_target_native_type scopeOwner
              proofOwner proofAddress assertionLabel nextPairPosition pairEnd
              constantName leftTail rightBody sourceBody context)
            (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
              proofAddress)
            (inductionHypothesis tailSemantics)
      | var leftVariable =>
          have rightSemantics : AllWithSemantics callerDV leftVariable
              (BodyVariables rightBody) :=
            semantics leftVariable (by simp [BodyVariables])
          have tailSemantics : AllPairsSemantics callerDV
              (BodyVariables leftTail) (BodyVariables rightBody) := by
            intro left member
            exact semantics left (by simp [BodyVariables, member])
          exact .var leftVariable leftTail
            (normalDVLeftVariablePhaseAt_inhabits_target_native_type
              scopeOwner proofOwner proofAddress assertionLabel
              nextPairPosition pairEnd leftVariable leftTail rightBody
              sourceBody context)
            (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
              proofAddress)
            (addressedDVRightTrace_of_semantics callerDV scopeOwner proofOwner
              proofAddress assertionLabel nextPairPosition pairEnd leftVariable
              leftTail rightBody sourceBody context rightBody rightSemantics)
            (inductionHypothesis tailSemantics)

theorem AddressedDVLeftTrace.reflects_semantics
    {callerDV : List (String × String)}
    {scopeOwner proofOwner proofAddress : Atom}
    {assertionLabel : String} {nextPairPosition pairEnd : Nat}
    {rightBody sourceBody : List Metamath.Verify.Sym}
    {context : Atom} {leftScan : List Metamath.Verify.Sym}
    (trace : AddressedDVLeftTrace callerDV scopeOwner proofOwner proofAddress
      assertionLabel nextPairPosition pairEnd rightBody sourceBody context
      leftScan) :
    AllPairsSemantics callerDV (BodyVariables leftScan)
      (BodyVariables rightBody) := by
  induction trace with
  | nil =>
      intro left member
      simp [BodyVariables] at member
  | const constantName leftTail nativeStep reloadStep tail induction =>
      simpa [BodyVariables] using induction
  | var leftVariable leftTail nativeStep reloadStep right tail induction =>
      intro left member
      simp only [BodyVariables, List.mem_cons] at member
      rcases member with equal | member
      · subst left
        exact right.reflects_semantics
      · exact induction left member

def AddressedDVPairBeginStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Prop :=
  let source := normalDVPairBeginPhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVPairBeginDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalDVScanLeftRowAt scopeOwner proofOwner proofAddress assertionLabel
          nextPairPosition pairEnd leftBody rightBody sourceBody context ∈
        target ∧
      normalDVReloadRowAt proofOwner proofAddress ∈ target

def AddressedDVCompleteStep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Prop :=
  let source := normalDVCompletePhaseSpaceAt scopeOwner proofOwner
    proofAddress assertionLabel pairEnd sourceBody context
  let target := fireReflectiveSourceExecFact source normalDVCompleteDirective
  (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred ∧
    normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context ∈ target

inductive AddressedDVListsTrace
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (substitution : FiniteSubstitution) :
    List (String × String) → Nat → Prop where
  | nil
      (nativeStep : AddressedDVCompleteStep scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context) :
      AddressedDVListsTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context substitution [] pairEnd
  | cons (leftVariable rightVariable : String)
      (calleeTail : List (String × String))
      (leftReplacement rightReplacement : ConstantHeadedFormula)
      (pairPosition : Nat)
      (leftLookup : LookupSemantics substitution leftVariable leftReplacement)
      (rightLookup : LookupSemantics substitution rightVariable
        rightReplacement)
      (leftRow : normalAssertionSubstitutionRowAt proofOwner proofAddress
          leftVariable leftReplacement.body ∈
        normalSubstitutionRowsAt proofOwner proofAddress substitution)
      (rightRow : normalAssertionSubstitutionRowAt proofOwner proofAddress
          rightVariable rightReplacement.body ∈
        normalSubstitutionRowsAt proofOwner proofAddress substitution)
      (variablesDistinct : leftVariable ≠ rightVariable)
      (nativeStep : AddressedDVPairBeginStep scopeOwner proofOwner proofAddress
        assertionLabel pairPosition (pairPosition + 1) pairEnd leftVariable
        rightVariable leftReplacement.body rightReplacement.body sourceBody
        context)
      (reloadStep : AddressedDVReloadStep proofOwner proofAddress)
      (leftTrace : AddressedDVLeftTrace callerDV scopeOwner proofOwner
        proofAddress assertionLabel (pairPosition + 1) pairEnd
        rightReplacement.body sourceBody context leftReplacement.body)
      (tail : AddressedDVListsTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context substitution calleeTail
        (pairPosition + 1)) :
      AddressedDVListsTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context substitution
        ((leftVariable, rightVariable) :: calleeTail) pairPosition

theorem addressedDVListsTrace_of_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (substitution : FiniteSubstitution)
    (calleeDV : List (String × String)) (pairPosition : Nat)
    (positionEnd : pairPosition + calleeDV.length = pairEnd)
    (namesDistinct : DVPairNamesDistinct calleeDV)
    (semantics : DVListsSemantics substitution callerDV calleeDV) :
    AddressedDVListsTrace callerDV scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context substitution calleeDV
      pairPosition := by
  induction calleeDV generalizing pairPosition with
  | nil =>
      simp at positionEnd
      subst pairPosition
      exact .nil
        (normalDVCompletePhaseAt_inhabits_target_native_type scopeOwner
          proofOwner proofAddress assertionLabel pairEnd sourceBody context)
  | cons pair calleeTail inductionHypothesis =>
      rcases pair with ⟨leftVariable, rightVariable⟩
      rcases semantics (leftVariable, rightVariable) (by simp) with
        ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
          pairSemantics⟩
      have variablesDistinct : leftVariable ≠ rightVariable :=
        namesDistinct (leftVariable, rightVariable) (by simp)
      have tailDistinct : DVPairNamesDistinct calleeTail := by
        intro pair member
        exact namesDistinct pair (by simp [member])
      have tailSemantics : DVListsSemantics substitution callerDV
          calleeTail := by
        intro pair member
        exact semantics pair (by simp [member])
      have tailEnd : pairPosition + 1 + calleeTail.length = pairEnd := by
        simp only [List.length_cons] at positionEnd
        omega
      have leftRow : normalAssertionSubstitutionRowAt proofOwner proofAddress
            leftVariable leftReplacement.body ∈
          normalSubstitutionRowsAt proofOwner proofAddress substitution :=
        (normalAssertionSubstitutionRowAt_mem_iff proofOwner proofAddress
          substitution leftVariable leftReplacement.body).2
          ⟨leftReplacement, leftLookup, rfl⟩
      have rightRow : normalAssertionSubstitutionRowAt proofOwner proofAddress
            rightVariable rightReplacement.body ∈
          normalSubstitutionRowsAt proofOwner proofAddress substitution :=
        (normalAssertionSubstitutionRowAt_mem_iff proofOwner proofAddress
          substitution rightVariable rightReplacement.body).2
          ⟨rightReplacement, rightLookup, rfl⟩
      exact .cons leftVariable rightVariable calleeTail leftReplacement
        rightReplacement pairPosition leftLookup rightLookup leftRow rightRow
        variablesDistinct
        (normalDVPairBeginPhaseAt_inhabits_target_native_type scopeOwner
          proofOwner proofAddress assertionLabel pairPosition
          (pairPosition + 1) pairEnd leftVariable rightVariable
          leftReplacement.body rightReplacement.body sourceBody context
          variablesDistinct)
        (normalDVReloadPhaseAt_inhabits_target_native_type proofOwner
          proofAddress)
        (addressedDVLeftTrace_of_semantics callerDV scopeOwner proofOwner
          proofAddress assertionLabel (pairPosition + 1) pairEnd
          rightReplacement.body sourceBody context leftReplacement.body
          pairSemantics)
        (inductionHypothesis (pairPosition := pairPosition + 1) tailEnd
          tailDistinct tailSemantics)

theorem AddressedDVListsTrace.reflects_semantics
    {callerDV : List (String × String)}
    {scopeOwner proofOwner proofAddress : Atom}
    {assertionLabel : String} {pairEnd : Nat}
    {sourceBody : List Metamath.Verify.Sym} {context : Atom}
    {substitution : FiniteSubstitution}
    {calleeDV : List (String × String)} {pairPosition : Nat}
    (trace : AddressedDVListsTrace callerDV scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context substitution calleeDV
      pairPosition) :
    DVListsSemantics substitution callerDV calleeDV := by
  induction trace with
  | nil =>
      intro pair member
      simp at member
  | cons leftVariable rightVariable calleeTail leftReplacement
      rightReplacement pairPosition leftLookup rightLookup leftRow rightRow
      variablesDistinct nativeStep reloadStep leftTrace tail induction =>
      intro pair member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · cases equal
        exact ⟨leftReplacement, rightReplacement, leftLookup, rightLookup,
          leftTrace.reflects_semantics⟩
      · exact induction pair member

theorem addressedDVListsTrace_iff_semantics
    (callerDV : List (String × String))
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (substitution : FiniteSubstitution)
    (calleeDV : List (String × String)) (pairPosition : Nat)
    (positionEnd : pairPosition + calleeDV.length = pairEnd)
    (namesDistinct : DVPairNamesDistinct calleeDV) :
    AddressedDVListsTrace callerDV scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context substitution calleeDV
        pairPosition ↔
      DVListsSemantics substitution callerDV calleeDV :=
  ⟨AddressedDVListsTrace.reflects_semantics,
    addressedDVListsTrace_of_semantics callerDV scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context substitution
      calleeDV pairPosition positionEnd namesDistinct⟩

section AxiomAudit

#print axioms normalDVNextPairRowAt_nat_exact
#print axioms normalDVReloadPhaseAt_inhabits_target_native_type
#print axioms normalDVCompletePhaseAt_inhabits_target_native_type
#print axioms normalDVLeftConstPhaseAt_inhabits_target_native_type
#print axioms normalDVLeftVariablePhaseAt_inhabits_target_native_type
#print axioms normalDVRightConstPhaseAt_inhabits_target_native_type
#print axioms normalDVRightNilPhaseAt_inhabits_target_native_type
#print axioms normalDVLeftNilPhaseAt_inhabits_target_native_type
#print axioms normalDVRightVariablePhaseAt_inhabits_target_native_type
#print axioms normalDVRightVariableAt_missing_caller_rejects_obligation
#print axioms normalAssertionFinishPhaseAt_inhabits_target_native_type
#print axioms normalDVPairBeginPhaseAt_inhabits_target_native_type
#print axioms addressedDVRightTrace_of_semantics
#print axioms AddressedDVRightTrace.reflects_semantics
#print axioms addressedDVLeftTrace_of_semantics
#print axioms AddressedDVLeftTrace.reflects_semantics
#print axioms addressedDVListsTrace_of_semantics
#print axioms AddressedDVListsTrace.reflects_semantics
#print axioms addressedDVListsTrace_iff_semantics

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalDVAddressed
