import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicNativeListCanonicalSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticContextualCategory
import Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
import Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist

open Mettapedia.GSLT.LanguageDef

/-!
# Checked higher-order MIL programs in Prime's native List relator

This module gives a second, structurally independent exact-image bridge from
the generic inference checker into Prime's native dependent type theory.  A
validated learned calculus language contains an element relation and the two
structural rules for its List lifting.  Checked proof trees receive an
independent proof-relevant interpretation and are then reified as inhabitants
of the genuinely native strictly-positive `List.mapRel` family.

The bridge is generic over every checked List-relator derivation in this
finite definition.  It retains one element witness and one recursive witness
for every cons node.  It neither introduces a special ILP evaluator nor claims
that arbitrary raw Prime terms are canonical List spines.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILCheckedNativeListPrograms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Presentation
open Presentation.Declaration
open NativeIndexedFamilies

/-! ## A validated recursive List-relator definition -/

private def valueConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "MILValue"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "MILValue")
    syntaxPattern := [] }

def successor : Pattern := .apply "MIL.Successor" []
def one : Pattern := .apply "MIL.One" []
def two : Pattern := .apply "MIL.Two" []
def nil : Pattern := .apply "MIL.Nil" []
def cons (head tail : Pattern) : Pattern := .apply "MIL.Cons" [head, tail]

def relates (relation source target : Pattern) : Pattern :=
  .apply "MIL.Rel" [relation, source, target]

def mapRel (relation sources targets : Pattern) : Pattern :=
  .apply "MIL.MapRel" [relation, sources, targets]

private def listRelationLanguage : LanguageDef :=
  { name := "prime-mil-native-list-relator"
    types := [TypeDecl.plain "MILValue"]
    terms :=
      [valueConstructor "MIL.Successor" 0,
        valueConstructor "MIL.One" 0,
        valueConstructor "MIL.Two" 0,
        valueConstructor "MIL.Nil" 0,
        valueConstructor "MIL.Cons" 2]
    equations := []
    rewrites := [] }

private def baseDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend listRelationLanguage
    { judgments :=
        [{ head := "MIL.Rel", arity := 3 },
          { head := "MIL.MapRel", arity := 3 }]
      rules := [] }

private theorem listRelationLanguage_validate :
    listRelationLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly listRelationLanguage <;>
    simp [listRelationLanguage, valueConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

private theorem baseDefinition_valid :
    baseDefinition.isValid = true := by
  have hvalidate : baseDefinition.toLanguageDef.validate = [] := by
    simpa [baseDefinition] using listRelationLanguage_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [baseDefinition, listRelationLanguage, valueConstructor,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

def base : ValidatedCalculusLanguageDef :=
  ⟨baseDefinition, baseDefinition_valid⟩

def successorRule : RuleSchema :=
  { id := ⟨"mil-successor-one-two"⟩
    metavariables := []
    premises := []
    conclusion := relates successor one two }

def mapNilRule : RuleSchema :=
  { id := ⟨"mil-map-rel-nil"⟩
    metavariables := [("relation", 0)]
    premises := []
    conclusion := mapRel (.fvar "relation") nil nil }

def mapConsRule : RuleSchema :=
  { id := ⟨"mil-map-rel-cons"⟩
    metavariables :=
      [("relation", 0), ("sourceHead", 0), ("targetHead", 0),
        ("sourceTail", 0), ("targetTail", 0)]
    premises :=
      [relates (.fvar "relation") (.fvar "sourceHead")
          (.fvar "targetHead"),
        mapRel (.fvar "relation") (.fvar "sourceTail")
          (.fvar "targetTail")]
    conclusion :=
      mapRel (.fvar "relation")
        (cons (.fvar "sourceHead") (.fvar "sourceTail"))
        (cons (.fvar "targetHead") (.fvar "targetTail")) }

def learnedDelta : CalculusLanguageExtension :=
  { newTerms := []
    newJudgments := []
    newRules := [successorRule, mapNilRule, mapConsRule] }

private theorem learned_disjoint :
    learnedDelta.disjointFrom base.1 = true := by
  simp [learnedDelta, CalculusLanguageExtension.disjointFrom, base,
    baseDefinition, listRelationLanguage, successorRule, mapNilRule,
    mapConsRule]

private theorem learned_policy :
    learnedDelta.policyHolds base.1
      (.extendsBaseJudgments ["MIL.Rel", "MIL.MapRel"]) = true := by
  simp [learnedDelta, CalculusLanguageExtension.policyHolds, base,
    baseDefinition, successorRule, mapNilRule, mapConsRule, relates, mapRel]

private theorem learned_target_valid :
    (learnedDelta.apply base.1).isValid = true := by
  have hvalidate : (learnedDelta.apply base.1).toLanguageDef.validate = [] := by
    simpa [learnedDelta, CalculusLanguageExtension.apply, base,
      baseDefinition] using listRelationLanguage_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [learnedDelta, CalculusLanguageExtension.apply, base, baseDefinition,
    listRelationLanguage, valueConstructor, successorRule, mapNilRule,
    mapConsRule, relates, mapRel, successor, one, two, nil, cons,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

def learned : ValidatedCalculusLanguageExtension base where
  extension := learnedDelta
  policy := .extendsBaseJudgments ["MIL.Rel", "MIL.MapRel"]
  disjoint := learned_disjoint
  policyHolds := learned_policy
  valid := learned_target_valid

/-! ## Checked recursive proof artifacts -/

def successorProof : RawProof :=
  .node { ruleId := successorRule.id, arguments := [] } []

def nilProof : RawProof :=
  .node { ruleId := mapNilRule.id, arguments := [successor] } []

def singletonMapProof : RawProof :=
  .node
    { ruleId := mapConsRule.id
      arguments := [successor, one, two, nil, nil] }
    [successorProof, nilProof]

def singletonSource : Pattern := cons one nil
def singletonTarget : Pattern := cons two nil

theorem singletonMapProof_checked :
    checkRaw learned.target
        (mapRel successor singletonSource singletonTarget)
        singletonMapProof = true := by
  simp [checkRaw, checkRawChildren, singletonMapProof, successorProof,
    nilProof, learned, ValidatedCalculusLanguageExtension.target, learnedDelta,
    CalculusLanguageExtension.apply, base, baseDefinition, successorRule,
    mapNilRule, mapConsRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, relates, mapRel, successor, one, two, nil, cons,
    singletonSource, singletonTarget, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def missingTailProof : RawProof :=
  .node
    { ruleId := mapConsRule.id
      arguments := [successor, one, two, nil, nil] }
    [successorProof]

theorem missingTailProof_rejected :
    checkRaw learned.target
        (mapRel successor singletonSource singletonTarget)
        missingTailProof = false := by
  simp [checkRaw, checkRawChildren, missingTailProof, successorProof,
    learned, ValidatedCalculusLanguageExtension.target, learnedDelta,
    CalculusLanguageExtension.apply, base, baseDefinition, successorRule,
    mapNilRule, mapConsRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, relates, mapRel, successor, one, two, nil, cons,
    singletonSource, singletonTarget, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## Independent proof-relevant semantics -/

/-- Element-level evidence.  The relation symbol remains an explicit index;
the one learned fact inhabits only the successor fibre. -/
inductive Step : Pattern → Pattern → Pattern → Type where
  | successor : Step successor one two

/-- Proof-relevant pointwise lifting over authored List syntax.  Each cons
retains both its head evidence and its recursive tail evidence. -/
inductive ListStep (relation : Pattern) : Pattern → Pattern → Type where
  | nil : ListStep relation nil nil
  | cons {sourceHead targetHead sourceTail targetTail : Pattern} :
      Step relation sourceHead targetHead →
        ListStep relation sourceTail targetTail →
          ListStep relation (cons sourceHead sourceTail)
            (cons targetHead targetTail)

private def authoredHead? : Pattern → Option Pattern
  | .apply _ [head, _tail] => some head
  | _ => none

private def authoredTail? : Pattern → Option Pattern
  | .apply _ [_head, tail] => some tail
  | _ => none

/-- Constructor inversion with all index equalities retained explicitly.
Keeping the Pattern equalities as data avoids asking dependent elimination to
decide authored constructor-label disequalities. -/
theorem ListStep.constructorView {relation sources targets : Pattern}
    (evidence : ListStep relation sources targets) :
    (sources = MILCheckedNativeListPrograms.nil ∧
      targets = MILCheckedNativeListPrograms.nil ∧
      HEq evidence (@ListStep.nil relation)) ∨
      ∃ (sourceHead targetHead sourceTail targetTail : Pattern)
        (head : Step relation sourceHead targetHead)
        (tail : ListStep relation sourceTail targetTail),
        sources = MILCheckedNativeListPrograms.cons sourceHead sourceTail ∧
          targets = MILCheckedNativeListPrograms.cons targetHead targetTail ∧
          HEq evidence (ListStep.cons head tail) := by
  cases evidence with
  | nil => exact Or.inl ⟨rfl, rfl, HEq.rfl⟩
  | cons head tail =>
      exact Or.inr ⟨_, _, _, _, head, tail, rfl, rfl, HEq.rfl⟩

def Meaning : Pattern → Type
  | .apply "MIL.Rel" [relation, source, target] =>
      Step relation source target
  | .apply "MIL.MapRel" [relation, sources, targets] =>
      ListStep relation sources targets
  | _ => Empty

def baseSemantics : CalculusLanguageSemantics base Meaning where
  ruleMeaning := by
    intro ruleInstance premises conclusion application _premiseEvidence
    have noRules : base.1.rules = [] := rfl
    have impossible : False := by
      rcases application with ⟨rule, lookup, _⟩
      unfold CalculusLanguageDef.lookupRule? at lookup
      rw [noRules] at lookup
      simp at lookup
    exact False.elim impossible

/-- The structural checker and this interpretation are deliberately
independent.  Validation identifies the exact stored schema; ordered premise
evidence then constructs the corresponding proof-relevant List spine. -/
def learnedSemantics : SemanticExtension base learned Meaning where
  baseSemantics := baseSemantics
  addedRuleMeaning := by
    intro rule member ruleInstance premises conclusion lookup application
      premiseEvidence
    simp only [learned, learnedDelta, List.mem_cons, List.not_mem_nil,
      or_false] at member
    have instantiated :=
      instantiateRule?_eq_some_iff_application.mpr application
    by_cases successorMember : rule = successorRule
    · subst rule
      rcases ruleInstance with ⟨ruleId, arguments⟩
      cases arguments with
      | cons argument arguments =>
          simp [instantiateRule?, lookup, successorRule,
            argumentsValidAt] at instantiated
      | nil =>
          simp [instantiateRule?, lookup, successorRule,
            instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
            instantiateSchemasAt?, relates, successor, one, two]
            at instantiated
          rcases instantiated with ⟨_, rfl, rfl⟩
          exact Step.successor
    · by_cases nilMember : rule = mapNilRule
      · subst rule
        rcases ruleInstance with ⟨ruleId, arguments⟩
        cases arguments with
        | nil =>
            simp [instantiateRule?, lookup, mapNilRule,
              argumentsValidAt] at instantiated
        | cons relation remaining =>
          cases remaining with
          | cons extra tail =>
              simp [instantiateRule?, lookup, mapNilRule,
                argumentsValidAt] at instantiated
          | nil =>
              simp [instantiateRule?, lookup, mapNilRule,
                instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
                instantiateSchemasAt?, lookupArgumentAt?, mapRel, nil]
                at instantiated
              rcases instantiated with ⟨_, rfl, rfl⟩
              exact ListStep.nil
      · have consMember : rule = mapConsRule := by
          rcases member with successorEquality | nilEquality | consEquality
          · exact False.elim (successorMember successorEquality)
          · exact False.elim (nilMember nilEquality)
          · exact consEquality
        subst rule
        rcases ruleInstance with ⟨ruleId, arguments⟩
        cases arguments with
        | nil =>
            simp [instantiateRule?, lookup, mapConsRule,
              argumentsValidAt] at instantiated
        | cons relation remaining =>
          cases remaining with
          | nil =>
              simp [instantiateRule?, lookup, mapConsRule,
                argumentsValidAt] at instantiated
          | cons sourceHead remaining =>
            cases remaining with
            | nil =>
                simp [instantiateRule?, lookup, mapConsRule,
                  argumentsValidAt] at instantiated
            | cons targetHead remaining =>
              cases remaining with
              | nil =>
                  simp [instantiateRule?, lookup, mapConsRule,
                    argumentsValidAt] at instantiated
              | cons sourceTail remaining =>
                cases remaining with
                | nil =>
                    simp [instantiateRule?, lookup, mapConsRule,
                      argumentsValidAt] at instantiated
                | cons targetTail remaining =>
                  cases remaining with
                  | cons extra tail =>
                      simp [instantiateRule?, lookup, mapConsRule,
                        argumentsValidAt] at instantiated
                  | nil =>
                      simp [instantiateRule?, lookup, mapConsRule,
                        instantiateSchema?, instantiateSchemaAt?,
                        instantiateSchemas?, instantiateSchemasAt?,
                        lookupArgumentAt?, relates, mapRel, cons]
                        at instantiated
                      rcases instantiated with ⟨_, rfl, rfl⟩
                      cases premiseEvidence with
                      | cons headEvidence rest =>
                        cases rest with
                        | cons tailEvidence rest =>
                          cases rest
                          exact ListStep.cons headEvidence tailEvidence

noncomputable def singletonDerivation :
    Derivation learned.target
      (mapRel successor singletonSource singletonTarget) :=
  Classical.choose
    (G2_checkRaw_iff_exists_derivation_erases_to.mp
      singletonMapProof_checked)

@[simp] theorem singletonDerivation_erase :
    singletonDerivation.erase = singletonMapProof :=
  Classical.choose_spec
    (G2_checkRaw_iff_exists_derivation_erases_to.mp
      singletonMapProof_checked)

/-- The accepted recursive proof constructs the full head/tail evidence
spine, not merely endpoint reachability. -/
noncomputable def singletonEvidence :
    ListStep successor singletonSource singletonTarget :=
  learnedSemantics.interpret singletonDerivation

/-- Decomposing the evidence produced from the checked proof recovers both
the element witness and the recursive tail witness.  This is stronger than
merely observing that the two fibres happen to be inhabited. -/
theorem singletonEvidence_retains_head_and_tail :
    ∃ (head : Step successor one two)
      (tail : ListStep successor nil nil),
      singletonEvidence = ListStep.cons head tail := by
  rcases ListStep.constructorView singletonEvidence with empty | nonempty
  · exact False.elim ((by decide : singletonSource ≠ nil) empty.1)
  · rcases nonempty with
      ⟨sourceHead, targetHead, sourceTail, targetTail, head, tail,
        sourceShape, targetShape, evidenceShape⟩
    cases head
    have sourceTailEq : sourceTail = nil := by
      have projected := congrArg authoredTail? sourceShape
      simpa [singletonSource, cons, authoredTail?] using projected.symm
    have targetTailEq : targetTail = nil := by
      have projected := congrArg authoredTail? targetShape
      simpa [singletonTarget, cons, authoredTail?] using projected.symm
    subst sourceTail
    subst targetTail
    exact ⟨Step.successor, tail, eq_of_heq evidenceShape⟩

/-! ## A formed declaration-aware native relation context -/

namespace NativeCanary

abbrev NativeHasType {n : Nat} :=
  @Presentation.HasType Tower.Head IntrinsicRelator.rules n

/-- Add a source inhabitant of `A` to the native `A,B,R` telescope. -/
def contextABRSource : Tower.Ctx 4 :=
  .snoc IntrinsicRelator.contextABR (.var 2)

/-- Add a target inhabitant of `B`. -/
def contextABRSourceTarget : Tower.Ctx 5 :=
  .snoc contextABRSource (.var 2)

/-- The exact proof-relevant relation fibre at the chosen endpoints. -/
def edgeType : Tower.Tm 5 :=
  .app (.app (.var 2) (.var 1)) (.var 0)

/-- Add an inhabitant of `R source target`.  In the final context the six
entries are `A,B,R,source,target,edge`, in that order. -/
def contextABRSourceTargetEdge : Tower.Ctx 6 :=
  .snoc contextABRSourceTarget edgeType

def contextAWellFormed :
    ContextWellFormed IntrinsicRelator.rules IntrinsicRelator.contextA := by
  apply ContextWellFormed.snoc
  · exact .nil
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)

def contextABWellFormed :
    ContextWellFormed IntrinsicRelator.rules IntrinsicRelator.contextAB := by
  apply ContextWellFormed.snoc
  · exact contextAWellFormed
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)

def contextABRWellFormed :
    ContextWellFormed IntrinsicRelator.rules IntrinsicRelator.contextABR := by
  apply ContextWellFormed.snoc
  · exact contextABWellFormed
  · exact IntrinsicRelator.relationType_hasType
  · exact .sort IntrinsicRelator.relationTypeLevel

def contextABRSourceWellFormed :
    ContextWellFormed IntrinsicRelator.rules contextABRSource := by
  apply ContextWellFormed.snoc
  · exact contextABRWellFormed
  · exact Presentation.HasType.var 2
  · exact .sort Intrinsic.elementLevel

def contextABRSourceTargetWellFormed :
    ContextWellFormed IntrinsicRelator.rules contextABRSourceTarget := by
  apply ContextWellFormed.snoc
  · exact contextABRSourceWellFormed
  · exact Presentation.HasType.var 2
  · exact .sort Intrinsic.elementLevel

theorem edgeType_hasType :
    NativeHasType contextABRSourceTarget edgeType
      (sortTm Intrinsic.motiveLevel) := by
  apply IntrinsicRelator.relationApp_hasType
    (source := (.var 4 : Tower.Tm 5)) (target := .var 3)
    (relation := .var 2) (sourceTerm := .var 1) (targetTerm := .var 0)
  · exact Presentation.HasType.var 2
  · exact Presentation.HasType.var 1
  · exact Presentation.HasType.var 0

def contextWellFormed :
    ContextWellFormed IntrinsicRelator.rules
      contextABRSourceTargetEdge := by
  apply ContextWellFormed.snoc
  · exact contextABRSourceTargetWellFormed
  · exact edgeType_hasType
  · exact .sort Intrinsic.motiveLevel

def formedContext :
    SyntacticContextual.FormedContext IntrinsicRelator.rules where
  arity := 6
  context := contextABRSourceTargetEdge
  wellFormed := contextWellFormed

def sourceType : Tower.Tm 6 := .var 5
def targetType : Tower.Tm 6 := .var 4
def relationTerm : Tower.Tm 6 := .var 3

def typedSource :
    IntrinsicCanonicalSemantics.TypedTerm
      contextABRSourceTargetEdge sourceType where
  term := .var 2
  typing := Presentation.HasType.var 2

def typedTarget :
    IntrinsicCanonicalSemantics.TypedTerm
      contextABRSourceTargetEdge targetType where
  term := .var 1
  typing := Presentation.HasType.var 1

def typedEdge :
    IntrinsicCanonicalSemantics.TypedRelationEvidence relationTerm
      typedSource typedTarget where
  term := .var 0
  typing := Presentation.HasType.var 0

theorem sourceType_hasType :
    NativeHasType contextABRSourceTargetEdge sourceType
      (sortTm Intrinsic.elementLevel) :=
  Presentation.HasType.var 5

theorem targetType_hasType :
    NativeHasType contextABRSourceTargetEdge targetType
      (sortTm Intrinsic.elementLevel) :=
  Presentation.HasType.var 4

theorem relationTerm_hasType :
    NativeHasType contextABRSourceTargetEdge relationTerm
      (.pi sourceType (.pi (Presentation.rename wk targetType)
        (sortTm Intrinsic.motiveLevel))) :=
  Presentation.HasType.var 3

end NativeCanary

/-! ## Exact native image of every checked successor List derivation -/

/-- The exact constructor image in Prime's native List relator.  Its Pattern
indices make an endpoint mismatch unconstructible; its projections below
carry the actual raw Prime terms and typing derivations. -/
inductive NativeImage : Pattern → Pattern → Type where
  | nil : NativeImage nil nil
  | cons {sourceTail targetTail : Pattern} :
      NativeImage sourceTail targetTail →
        NativeImage (cons one sourceTail) (cons two targetTail)

namespace NativeImage

open NativeCanary

def sourceList : {sources targets : Pattern} →
    NativeImage sources targets →
      IntrinsicCanonicalSemantics.CanonicalList
        contextABRSourceTargetEdge sourceType
  | _, _, .nil => []
  | _, _, .cons tail => typedSource :: tail.sourceList

def targetList : {sources targets : Pattern} →
    NativeImage sources targets →
      IntrinsicCanonicalSemantics.CanonicalList
        contextABRSourceTargetEdge targetType
  | _, _, .nil => []
  | _, _, .cons tail => typedTarget :: tail.targetList

def evidence : {sources targets : Pattern} →
    (image : NativeImage sources targets) →
      IntrinsicCanonicalSemantics.CanonicalMapRel relationTerm
        image.sourceList image.targetList
  | _, _, .nil => .nil
  | _, _, .cons tail => .cons typedEdge tail.evidence

/-- The native family at the exact encoded List indices is a formed type over
the formed declaration context. -/
def typeOver {sources targets : Pattern}
    (image : NativeImage sources targets) :
    SyntacticContextual.TypeOver formedContext where
  code := IntrinsicRelator.mapRelApp sourceType targetType relationTerm
    (IntrinsicCanonicalSemantics.encodeList sourceType image.sourceList)
    (IntrinsicCanonicalSemantics.encodeList targetType image.targetList)
  level := .sort Intrinsic.motiveLevel
  isUniverse := .sort Intrinsic.motiveLevel
  formed := IntrinsicRelator.mapRelApp_hasType
    sourceType_hasType targetType_hasType relationTerm_hasType
    (IntrinsicCanonicalSemantics.encodeList_hasType sourceType_hasType
      image.sourceList)
    (IntrinsicCanonicalSemantics.encodeList_hasType targetType_hasType
      image.targetList)

/-- The checker image becomes an actual proof-carrying Prime term in the
native strictly-positive family. -/
def term {sources targets : Pattern}
    (image : NativeImage sources targets) :
    SyntacticContextual.Term formedContext image.typeOver where
  code := IntrinsicCanonicalSemantics.encodeMapRel image.evidence
  typed := IntrinsicCanonicalSemantics.encodeMapRel_hasType
    sourceType_hasType targetType_hasType relationTerm_hasType image.evidence

end NativeImage

def ListStep.toNativeImage : {sources targets : Pattern} →
    ListStep successor sources targets → NativeImage sources targets
  | _, _, .nil => .nil
  | _, _, .cons head tail => by
      cases head
      exact .cons tail.toNativeImage

/-- Every native successor image has either the empty target or a target
whose visible head is exactly `two`. -/
theorem NativeImage.targetShape {sources targets : Pattern}
    (image : NativeImage sources targets) :
    targets = MILCheckedNativeListPrograms.nil ∨
      ∃ tail, targets = MILCheckedNativeListPrograms.cons two tail := by
  cases image with
  | nil => exact Or.inl rfl
  | cons tail => exact Or.inr ⟨_, rfl⟩

/-- A shared-index mismatch is rejected by the native family itself: there
is no constructor whose successor image maps `one` back to `one`. -/
theorem mismatched_endpoint_has_no_native_image :
    ¬ Nonempty (NativeImage (cons one nil) (cons one nil)) := by
  rintro ⟨image⟩
  rcases image.targetShape with empty | nonempty
  · exact (by decide : cons one nil ≠ nil) empty
  · rcases nonempty with ⟨tail, targetShape⟩
    have heads := congrArg authoredHead? targetShape
    have impossible : one = two := by
      simpa [cons, authoredHead?] using heads
    exact (by decide : one ≠ two) impossible

/-! ## Instance of the common checked-native waist -/

/-- The dependent result type is retained together with its intrinsically
typed term. -/
abbrev NativeArtifact (_goal : Pattern × Pattern) :=
  Sigma fun type : SyntacticContextual.TypeOver NativeCanary.formedContext =>
    SyntacticContextual.Term NativeCanary.formedContext type

/-- Recursive List evidence displayed as Prime's native indexed `mapRel`
term. -/
noncomputable def nativeRealization :
    NativeRealization (Pattern × Pattern)
      (fun goal => Meaning (mapRel successor goal.1 goal.2)) where
  Artifact := NativeArtifact
  realize := by
    intro goal evidence
    let image := ListStep.toNativeImage evidence
    exact ⟨image.typeOver, image.term⟩

/-- The checked recursive List definition, its independent semantics, and
its intrinsic Prime realization packaged through the common waist. -/
noncomputable def checkedNativeWaist : CheckedNativeWaist learned.target where
  Meaning := Meaning
  semantics := learnedSemantics.targetSemantics
  Goal := Pattern × Pattern
  surface := fun goal => mapRel successor goal.1 goal.2
  native := nativeRealization

/-! ## General checked-to-native exact-image theorem -/

structure CheckedNativeMapProgram (sources targets : Pattern) : Type where
  checked : Derivation learned.target (mapRel successor sources targets)

namespace CheckedNativeMapProgram

noncomputable def semanticEvidence {sources targets : Pattern}
    (program : CheckedNativeMapProgram sources targets) :
    ListStep successor sources targets :=
  learnedSemantics.interpret program.checked

noncomputable def nativeImage {sources targets : Pattern}
    (program : CheckedNativeMapProgram sources targets) :
    NativeImage sources targets :=
  program.semanticEvidence.toNativeImage

noncomputable def nativeTerm {sources targets : Pattern}
    (program : CheckedNativeMapProgram sources targets) :
    SyntacticContextual.Term NativeCanary.formedContext
      program.nativeImage.typeOver :=
  program.nativeImage.term

/-- The specialized recursive List program is exactly a consumer of the
common checked-native waist. -/
noncomputable def toWaist {sources targets : Pattern}
    (program : CheckedNativeMapProgram sources targets) :
    checkedNativeWaist.CheckedProgram (sources, targets) :=
  ⟨program.checked⟩

/-- Common-waist projection and the specialized API construct the identical
intrinsic native term. -/
theorem toWaist_artifact_code {sources targets : Pattern}
    (program : CheckedNativeMapProgram sources targets) :
    program.toWaist.artifact.2.code = program.nativeTerm.code :=
  rfl

end CheckedNativeMapProgram

/-- Exact raw erasure is retained beside the native result, so two proof
programs with the same endpoint are never silently identified. -/
structure CheckedRawNativeMapProgram
    (sources targets : Pattern) (raw : RawProof) : Type where
  checked : Derivation learned.target (mapRel successor sources targets)
  erases : checked.erase = raw

namespace CheckedRawNativeMapProgram

def toChecked {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    CheckedNativeMapProgram sources targets :=
  ⟨program.checked⟩

/-- The specialized exact-erasure carrier maps directly to the common waist. -/
noncomputable def toWaist {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    checkedNativeWaist.CheckedRawProgram (sources, targets) raw where
  checked := program.checked
  erases := program.erases

/-- The common waist contains exactly the specialized recursive-List proof
program, including its raw erasure identity. -/
noncomputable def ofWaist {sources targets : Pattern} {raw : RawProof}
    (program : checkedNativeWaist.CheckedRawProgram
      (sources, targets) raw) :
    CheckedRawNativeMapProgram sources targets raw where
  checked := program.checked
  erases := program.erases

/-- The specialized and common exact-erasure carriers are equivalent. -/
noncomputable def waistEquiv {sources targets : Pattern} {raw : RawProof} :
    CheckedRawNativeMapProgram sources targets raw ≃
      checkedNativeWaist.CheckedRawProgram (sources, targets) raw where
  toFun := toWaist
  invFun := ofWaist
  left_inv := by
    intro program
    cases program
    rfl
  right_inv := by
    intro program
    cases program
    rfl

end CheckedRawNativeMapProgram

/-- Raw generic checking and inhabitation of the native exact-image bridge
coincide for every proof program in the supported successor-List fragment. -/
theorem checkedRaw_iff_nonempty_native
    (sources targets : Pattern) (raw : RawProof) :
    checkRaw learned.target (mapRel successor sources targets) raw = true ↔
      Nonempty (CheckedRawNativeMapProgram sources targets raw) := by
  constructor
  · intro accepted
    rcases (G2_checkRaw_iff_exists_derivation_erases_to.mp accepted) with
      ⟨derivation, erases⟩
    exact ⟨⟨derivation, erases⟩⟩
  · rintro ⟨program⟩
    rw [← program.erases]
    exact checkRaw_erase program.checked

noncomputable def singletonNative :
    CheckedRawNativeMapProgram singletonSource singletonTarget
      singletonMapProof where
  checked := singletonDerivation
  erases := singletonDerivation_erase

/-- The positive end-to-end witness simultaneously retains the raw proof,
the independent semantic spine, and native intrinsic typing. -/
theorem singleton_preserves_checker_semantics_and_native_typing :
    singletonNative.checked.erase = singletonMapProof ∧
      Nonempty (ListStep successor singletonSource singletonTarget) ∧
      NativeCanary.NativeHasType NativeCanary.contextABRSourceTargetEdge
        singletonNative.toChecked.nativeTerm.code
        singletonNative.toChecked.nativeImage.typeOver.code := by
  exact ⟨singletonNative.erases,
    ⟨singletonNative.toChecked.semanticEvidence⟩,
    singletonNative.toChecked.nativeTerm.typed⟩

/-- The recursive positive control crosses the common waist with the exact
raw proof and the identical intrinsic native term. -/
theorem singleton_crosses_common_waist :
    (CheckedRawNativeMapProgram.toWaist singletonNative).checked.erase =
        singletonMapProof ∧
      (CheckedRawNativeMapProgram.toWaist singletonNative).toChecked.artifact.2.code =
        singletonNative.toChecked.nativeTerm.code := by
  exact ⟨singletonNative.erases, rfl⟩

/-- The missing recursive child has neither a checked derivation nor a native
program in this exact image. -/
theorem missing_tail_has_no_native_program :
    ¬ Nonempty
      (CheckedRawNativeMapProgram singletonSource singletonTarget
        missingTailProof) := by
  intro inhabited
  have accepted :=
    (checkedRaw_iff_nonempty_native singletonSource singletonTarget
      missingTailProof).mpr inhabited
  rw [missingTailProof_rejected] at accepted
  contradiction

/-- The same missing recursive child cannot inhabit the common waist. -/
theorem missing_tail_has_no_common_waist_program :
    ¬ Nonempty
      (checkedNativeWaist.CheckedRawProgram
        (singletonSource, singletonTarget) missingTailProof) := by
  intro inhabited
  apply missing_tail_has_no_native_program
  rcases inhabited with ⟨program⟩
  exact ⟨CheckedRawNativeMapProgram.ofWaist program⟩

#print axioms singletonMapProof_checked
#print axioms missingTailProof_rejected
#print axioms singletonDerivation_erase
#print axioms singletonEvidence_retains_head_and_tail
#print axioms mismatched_endpoint_has_no_native_image
#print axioms checkedRaw_iff_nonempty_native
#print axioms singleton_preserves_checker_semantics_and_native_typing
#print axioms missing_tail_has_no_native_program
#print axioms CheckedRawNativeMapProgram.waistEquiv
#print axioms singleton_crosses_common_waist
#print axioms missing_tail_has_no_common_waist_program

end MILCheckedNativeListPrograms
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
