import Mettapedia.GSLT.LanguageDef.GroundFactExtension
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredEquationInference

/-!
# Structural admission of every authored Prime equation table

The equation source generator already emits finite zero-premise rules.  This
module proves, uniformly in the source document, that those rows instantiate
the generic conservative ground-fact extension.  The result removes any need
to validate one closed example by normalizing the complete base calculus.

This remains an authentication layer.  Native object-language substitution
and typed conversion are separate capabilities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredEquationStructuralAdmission

open AuthoredDeclarationSignature
open AuthoredEquationInference
open DeclarationAwarePatternCodec
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionGluing
open Mettapedia.GSLT.LanguageDef.GroundFactExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax

def judgment : JudgmentDecl :=
  { head := "prime-authored-equation", arity := 8 }

def claimArguments (claim : EquationClaim) : List Pattern :=
  [ encodeNat claim.sourceIndex,
    encodeNat claim.equationIndex,
    encodeDeclName claim.label,
    encodeNat claim.arity,
    encodeCtx towerHeadCodec claim.context,
    encodeTm towerHeadCodec claim.left,
    encodeTm towerHeadCodec claim.right,
    encodeTm towerHeadCodec claim.type ]

@[simp] theorem encodeEquationClaim_eq (claim : EquationClaim) :
    encodeEquationClaim claim = .apply judgment.head (claimArguments claim) :=
  rfl

theorem claimArguments_ground (claim : EquationClaim) :
    Pattern.isGroundListAt 0 (claimArguments claim) = true := by
  cases claim with
  | mk sourceIndex equationIndex label arity context left right type =>
      simp [claimArguments, Pattern.isGroundListAt, encodeNat_ground,
        encodeDeclName_ground,
        encodeCtx_ground towerHeadCodec encodeTowerHead_ground,
        encodeTm_ground towerHeadCodec encodeTowerHead_ground]

theorem claimArguments_canonical (claim : EquationClaim) :
    Pattern.hasCanonicalBinderMetadataList (claimArguments claim) = true := by
  cases claim with
  | mk sourceIndex equationIndex label arity context left right type =>
      simp [claimArguments, Pattern.hasCanonicalBinderMetadataList,
        encodeNat_canonical, encodeDeclName_canonical,
        encodeCtx_canonical towerHeadCodec encodeTowerHead_canonical,
        encodeTm_canonical towerHeadCodec encodeTowerHead_canonical]

theorem base_language_eq_data_with_levels :
    basePresentation.1.toLanguageDef =
      withAddedTerms DeclarationAwareDataLanguage.language
        [DeclarationAwareCheckedContext.levelSpineNilConstructor,
          DeclarationAwareCheckedContext.levelSpineSnocConstructor] := by
  simp [basePresentation,
    DeclarationAwareTypedConversion.typedConversionExtension,
    ValidatedCalculusLanguageExtension.target,
    DeclarationAwareTypedConversion.typedConversionDelta,
    DeclarationAwareFormedTyping.formedTypingExtension,
    DeclarationAwareFormedTyping.formedTypingDelta,
    DeclarationAwareCheckedContext.contextFormationExtension,
    DeclarationAwareCheckedContext.contextFormationDelta,
    CalculusLanguageExtension.apply,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition_language_eq_data,
    withAddedTerms]

private theorem data_levelSpine_disjoint :
    List.Disjoint
      (DeclarationAwareDataLanguage.language.terms.map
        (fun term => term.label))
      ([DeclarationAwareCheckedContext.levelSpineNilConstructor,
          DeclarationAwareCheckedContext.levelSpineSnocConstructor].map
        (fun term => term.label)) := by
  simp [List.disjoint_left, DeclarationAwareDataLanguage.language,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareCheckedContext.levelSpineNilConstructor,
    DeclarationAwareCheckedContext.levelSpineSnocConstructor]

private theorem data_constructor_refines_base :
    ConstructorArityRefines DeclarationAwareDataLanguage.language
      basePresentation.1.toLanguageDef := by
  intro head arity valid
  rw [base_language_eq_data_with_levels]
  exact languageHasConstructorArity_withAddedTerms
    DeclarationAwareDataLanguage.language
    [DeclarationAwareCheckedContext.levelSpineNilConstructor,
      DeclarationAwareCheckedContext.levelSpineSnocConstructor]
    data_levelSpine_disjoint valid

theorem claimArguments_fixed (claim : EquationClaim) :
    fixedConstructorListsValid basePresentation.1.toLanguageDef
      (claimArguments claim) = true := by
  apply fixedConstructorListsValid_of_refines
    data_constructor_refines_base
  cases claim with
  | mk sourceIndex equationIndex label arity context left right type =>
      simp [claimArguments, fixedConstructorListsValid]

def equationRow {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) (ordinal : Nat) :
    Row basePresentation.1.toLanguageDef judgment where
  id := generatedRuleId ordinal
  arguments := claimArguments located.claim
  idNonempty := by simp [generatedRuleId]
  arity := rfl
  ground := claimArguments_ground located.claim
  canonical := claimArguments_canonical located.claim
  fixedConstructors := claimArguments_fixed located.claim

def rows (declarations : List SourceDeclaration) :
    List (Row basePresentation.1.toLanguageDef judgment) :=
  (equationInventory declarations).zipIdx.map fun pair =>
    equationRow pair.1 pair.2

@[simp] theorem row_rule_eq_generated
    {declarations : List SourceDeclaration}
    (located : LocatedEquation declarations) (ordinal : Nat) :
    (equationRow located ordinal).rule = generatedRule ordinal located := by
  rfl

theorem row_rules_eq_generated (declarations : List SourceDeclaration) :
    (rows declarations).map Row.rule = generatedRules declarations := by
  simp [rows, generatedRules, Function.comp_def]

theorem row_ids_distinct (declarations : List SourceDeclaration) :
    (((rows declarations).map fun row => row.id).eraseDups.length ==
      ((rows declarations).map fun row => row.id).length) = true := by
  apply (eraseDups_length_iff_nodup _).2
  have generated :
      (((equationInventory declarations).zipIdx.map Prod.snd).map
        generatedRuleId).Nodup :=
    (List.nodup_zipIdx_map_snd _).map generatedRuleId_injective
  have rowIds :
      (rows declarations).map (fun row => row.id) =
        ((equationInventory declarations).zipIdx.map Prod.snd).map
          generatedRuleId := by
    simp only [rows, List.map_map]
    apply List.map_congr_left
    intro pair pairMember
    rfl
  rw [rowIds]
  exact generated

def family (source : SourceDocument) :
    Family basePresentation.1.toLanguageDef where
  judgment := judgment
  rows := rows (elaborate source)
  languageValid := validated_languageValid basePresentation
  judgmentHeadNonempty := rfl
  judgmentTermDisjoint := by
    rw [base_language_eq_data_with_levels]
    decide
  judgmentNotReserved := by decide
  ruleIdsDistinct := row_ids_distinct (elaborate source)

theorem family_rules_eq_generated (source : SourceDocument) :
    (family source).calculus.rules = generatedRules (elaborate source) := by
  exact row_rules_eq_generated (elaborate source)

private theorem judgment_fresh :
    (!(basePresentation.1.judgments.any fun existing =>
      existing.head == judgment.head)) = true := by
  decide

private theorem ne_generatedRuleId_of_not_startsWith
    (id : RuleId)
    (notPrefix :
      id.value.startsWith "prime-authored-equation." = false)
    (ordinal : Nat) :
    id ≠ generatedRuleId ordinal := by
  intro equality
  have prefixEquality := congrArg
    (fun ruleId : RuleId =>
      ruleId.value.startsWith "prime-authored-equation.") equality
  simp [notPrefix, generatedRuleId] at prefixEquality

private theorem generated_id_fresh (ordinal : Nat) :
    (!(basePresentation.1.rules.any fun existing =>
      existing.id == generatedRuleId ordinal)) = true := by
  simp [basePresentation,
    DeclarationAwareTypedConversion.typedConversionExtension,
    ValidatedCalculusLanguageExtension.target,
    DeclarationAwareTypedConversion.typedConversionDelta,
    DeclarationAwareFormedTyping.formedTypingExtension,
    DeclarationAwareFormedTyping.formedTypingDelta,
    DeclarationAwareCheckedContext.contextFormationExtension,
    DeclarationAwareCheckedContext.contextFormationDelta,
    CalculusLanguageExtension.apply,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    DeclarationAwareCheckedContext.contextNilRule,
    DeclarationAwareCheckedContext.contextSnocRule,
    DeclarationAwareFormedTyping.formedTypingRule,
    DeclarationAwareTypedConversion.typedConversionReflRule,
    ne_generatedRuleId_of_not_startsWith]

theorem rows_fresh (declarations : List SourceDeclaration) :
    (rows declarations).all (fun row =>
      !(basePresentation.1.rules.any fun existing => existing.id == row.id)) =
        true := by
  apply List.all_eq_true.mpr
  intro row member
  rcases List.mem_map.mp member with ⟨pair, pairMember, rfl⟩
  exact generated_id_fresh pair.2

def overBase (source : SourceDocument) : Over basePresentation where
  family := family source
  judgmentFresh := judgment_fresh
  ruleIdsFresh := rows_fresh (elaborate source)

theorem delta_eq (source : SourceDocument) :
    (overBase source).delta = equationFactDelta source := by
  change
    ({ newJudgments := [judgment]
       newRules := (rows (elaborate source)).map Row.rule } :
      CalculusLanguageExtension) = equationFactDelta source
  unfold equationFactDelta
  rw [row_rules_eq_generated]
  rfl

/-- Every generated authored-equation table is a valid conservative extension,
uniformly in the source document. -/
def structuralExtension (source : SourceDocument) :
    ValidatedCalculusLanguageExtension basePresentation :=
  (overBase source).validatedExtension

theorem structuralExtension_delta (source : SourceDocument) :
    (structuralExtension source).extension = equationFactDelta source := by
  exact delta_eq source

theorem admit_eq_structural (source : SourceDocument) :
    admit? source = some (structuralExtension source) := by
  unfold admit?
  rw [← delta_eq source]
  simp [structuralExtension, Over.validatedExtension,
    (overBase source).delta_disjoint, (overBase source).delta_policy,
    (overBase source).target_valid]

/-- Source-parametric admitted facts, replacing closed-fixture admission. -/
def admitted (source : SourceDocument) : AdmittedFacts source where
  extension := structuralExtension source
  admission := admit_eq_structural source

/-- The ground-fact layer is exactly conservative for every raw proof whose
goal already belongs to the rooted Prime signature. -/
theorem base_goal_checkRaw_iff (source : SourceDocument)
    {goal : Pattern}
    (baseShape : basePresentation.1.hasJudgmentShape goal = true)
    (proof : RawProof) :
    checkRaw (structuralExtension source).target goal proof = true ↔
      checkRaw basePresentation goal proof = true := by
  exact
    Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity.ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
      (structuralExtension source) rfl baseShape proof

private theorem typedConversion_has_baseShape
    (query : DeclarationAwareTypedConversion.TypedConversionQuery) :
    basePresentation.1.hasJudgmentShape
      (DeclarationAwareTypedConversion.encodeTypedConversionQuery query) =
        true := by
  cases query
  simp [basePresentation,
    DeclarationAwareTypedConversion.typedConversionExtension,
    ValidatedCalculusLanguageExtension.target,
    DeclarationAwareTypedConversion.typedConversionDelta,
    DeclarationAwareFormedTyping.formedTypingExtension,
    DeclarationAwareFormedTyping.formedTypingDelta,
    DeclarationAwareCheckedContext.contextFormationExtension,
    DeclarationAwareCheckedContext.contextFormationDelta,
    CalculusLanguageExtension.apply,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareDataLanguage.definition,
    CalculusLanguageDef.hasJudgmentShape,
    CalculusLanguageDef.lookupJudgment?,
    DeclarationAwareTypedConversion.encodeTypedConversionQuery,
    DeclarationAwareTypedConversion.typedConversionPattern]

/-- Negative control: authenticated equation tables create no new generic
typed-conversion proof artifacts. -/
theorem typed_conversion_checkRaw_iff (source : SourceDocument)
    (query : DeclarationAwareTypedConversion.TypedConversionQuery)
    (proof : RawProof) :
    checkRaw (structuralExtension source).target
        (DeclarationAwareTypedConversion.encodeTypedConversionQuery query)
        proof = true ↔
      checkRaw basePresentation
        (DeclarationAwareTypedConversion.encodeTypedConversionQuery query)
        proof = true := by
  exact base_goal_checkRaw_iff source
    (typedConversion_has_baseShape query) proof

/-- Negative control: the conservative layer never reuses the rooted typed
conversion judgment. -/
theorem authored_judgment_ne_typed_conversion :
    judgment.head ≠ "prime-typed-conversion" := by decide

#print axioms row_ids_distinct
#print axioms family_rules_eq_generated
#print axioms rows_fresh
#print axioms structuralExtension_delta
#print axioms admit_eq_structural
#print axioms admitted
#print axioms base_goal_checkRaw_iff
#print axioms typed_conversion_checkRaw_iff
#print axioms authored_judgment_ne_typed_conversion

end AuthoredEquationStructuralAdmission
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
