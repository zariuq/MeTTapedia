import Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticNaturalModel

/-!
# OSLF and the intrinsic syntactic natural model: a separating canary

This module gives the generic calculus-to-OSLF semantic bridge an independent
dependent-type-theoretic meaning.  The positive judgment says that context
comprehension by `U₁` has a newest variable; its witness is the intrinsic
variable constructor of the cumulative tower's syntactic natural model.

The negative judgment says that the empty comprehension spine has a variable.
That proposition is constructor-theoretically empty.  A second calculus which
adds the negative judgment as a structurally valid zero-premise rule therefore
has no sound model under this interpretation.  Structural GSLT admission and
generated OSLF reachability do not mint CwF adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace OSLFSyntacticModelCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Presentation
open Presentation.SyntacticContextual
open Presentation.SyntacticNaturalModel

/-! ## Two authored judgments -/

def extendedVariableJudgment : Pattern :=
  .apply "HasExtendedVariable" []

def emptyVariableJudgment : Pattern :=
  .apply "HasEmptyVariable" []

private def ruleId (name : String) : RuleId := ⟨name⟩

def extendedVariableRule : RuleSchema where
  id := ruleId "extended-variable"
  metavariables := []
  premises := []
  conclusion := extendedVariableJudgment

def emptyVariableRule : RuleSchema where
  id := ruleId "empty-variable"
  metavariables := []
  premises := []
  conclusion := emptyVariableJudgment

def language : LanguageDef where
  name := "cumulative-tower-variable-canary"
  types := []
  terms := []
  equations := []
  rewrites := []

private def judgments : List JudgmentDecl :=
  [{ head := "HasExtendedVariable", arity := 0 },
   { head := "HasEmptyVariable", arity := 0 }]

/-- The sound authored fragment contains only the comprehension-variable
rule. -/
def soundDefinition : CalculusLanguageDef where
  toLanguageDef := language
  judgments := judgments
  rules := [extendedVariableRule]

/-- The adversarial extension is structurally valid but additionally claims
a variable in the empty context. -/
def unsoundDefinition : CalculusLanguageDef where
  toLanguageDef := language
  judgments := judgments
  rules := [extendedVariableRule, emptyVariableRule]

theorem soundDefinition_valid : soundDefinition.isValid = true := by
  have validate : soundDefinition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [soundDefinition, language, LanguageDef.typeNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [soundDefinition, language, judgments, extendedVariableRule,
    extendedVariableJudgment, ruleId,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorListsValid,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

theorem unsoundDefinition_valid : unsoundDefinition.isValid = true := by
  have validate : unsoundDefinition.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [unsoundDefinition, language, LanguageDef.typeNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [unsoundDefinition, language, judgments, extendedVariableRule,
    emptyVariableRule, extendedVariableJudgment, emptyVariableJudgment,
    ruleId, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorListsValid,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

def soundChecked : ValidatedCalculusLanguageDef :=
  ⟨soundDefinition, soundDefinition_valid⟩

def unsoundChecked : ValidatedCalculusLanguageDef :=
  ⟨unsoundDefinition, unsoundDefinition_valid⟩

def extendedVariableInstance : RuleInstance where
  ruleId := ruleId "extended-variable"
  arguments := []

def emptyVariableInstance : RuleInstance where
  ruleId := ruleId "empty-variable"
  arguments := []

def extendedVariableApplication :
    RuleApplication soundChecked extendedVariableInstance []
      extendedVariableJudgment := by
  apply instantiateRule?_eq_some_iff_application.mp
  simp [instantiateRule?, soundChecked, soundDefinition, language, judgments,
    extendedVariableInstance, extendedVariableRule, extendedVariableJudgment,
    ruleId,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemasAt?, instantiateSchemaAt?]

def extendedVariableDerivation :
    Derivation soundChecked extendedVariableJudgment :=
  .byRule extendedVariableInstance extendedVariableApplication .nil

def emptyVariableApplication :
    RuleApplication unsoundChecked emptyVariableInstance []
      emptyVariableJudgment := by
  apply instantiateRule?_eq_some_iff_application.mp
  simp [instantiateRule?, unsoundChecked, unsoundDefinition, language,
    judgments, emptyVariableInstance, extendedVariableRule,
    emptyVariableRule, emptyVariableJudgment, ruleId,
    CalculusLanguageDef.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?]

def emptyVariableDerivation :
    Derivation unsoundChecked emptyVariableJudgment :=
  .byRule emptyVariableInstance emptyVariableApplication .nil

/-! ## Independent CwF meaning -/

abbrev ExtendedVariable :=
  SyntacticNaturalModel.Variable
    (.snoc SyntacticNaturalModel.TowerExamples.emptySpine
      SyntacticContextual.TowerExamples.universeOne)
    (SyntacticContextual.TowerExamples.universeOne.reindex
      (projectionHom SyntacticContextual.TowerExamples.empty
        SyntacticContextual.TowerExamples.universeOne))

abbrev EmptyVariable :=
  SyntacticNaturalModel.Variable
    SyntacticNaturalModel.TowerExamples.emptySpine
    SyntacticContextual.TowerExamples.universeOne

def intrinsicMeaning (judgment : Pattern) : Prop :=
  (judgment = extendedVariableJudgment ∧ Nonempty ExtendedVariable) ∨
    (judgment = emptyVariableJudgment ∧ Nonempty EmptyVariable)

theorem extendedVariableMeaning :
    intrinsicMeaning extendedVariableJudgment := by
  exact Or.inl ⟨rfl,
    ⟨SyntacticNaturalModel.TowerExamples.universeOneVariable⟩⟩

theorem emptyVariableMeaning_false :
    ¬ intrinsicMeaning emptyVariableJudgment := by
  rintro (⟨different, _⟩ | ⟨_, ⟨nativeVar⟩⟩)
  · simp [extendedVariableJudgment, emptyVariableJudgment] at different
  · let emptyInstance : IsEmpty EmptyVariable :=
      SyntacticNaturalModel.TowerExamples.no_variable_in_empty
        SyntacticContextual.TowerExamples.universeOne
    exact (emptyInstance.false nativeVar).elim

/-! ## Exact positive bridge and negative obstruction -/

private theorem sound_application_conclusion
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application :
      RuleApplication soundChecked ruleInstance premises conclusion) :
    premises = [] ∧ conclusion = extendedVariableJudgment := by
  have instantiated :=
    instantiateRule?_eq_some_iff_application.mpr application
  rcases ruleInstance with ⟨⟨identifier⟩, arguments⟩
  by_cases identifierEq : identifier = "extended-variable"
  · subst identifier
    cases arguments with
    | nil =>
        have result :
            premises = [] ∧ extendedVariableJudgment = conclusion := by
          simpa [instantiateRule?, soundChecked, soundDefinition, language,
            judgments, extendedVariableRule, extendedVariableJudgment, ruleId,
            CalculusLanguageDef.lookupRule?, argumentsValidAt,
            RuleSchema.sideConditionsHold, instantiateSchemas?,
            instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?]
            using instantiated
        exact ⟨result.1, result.2.symm⟩
    | cons argument rest =>
        simp [instantiateRule?, soundChecked, soundDefinition, language,
          judgments, extendedVariableRule, ruleId,
          CalculusLanguageDef.lookupRule?, argumentsValidAt] at instantiated
  · simp [instantiateRule?, soundChecked, soundDefinition, language,
      judgments, extendedVariableRule, ruleId,
      CalculusLanguageDef.lookupRule?, Ne.symm identifierEq]
      at instantiated

private theorem sound_ruleSound :
    ∀ ruleInstance premises conclusion,
      RuleApplication soundChecked ruleInstance premises conclusion →
        (∀ premise ∈ premises, intrinsicMeaning premise) →
          intrinsicMeaning conclusion := by
  intro ruleInstance premises conclusion application _premisesMeaning
  obtain ⟨_, rfl⟩ :=
    sound_application_conclusion ruleInstance premises conclusion application
  exact extendedVariableMeaning

private theorem meaning_complete (judgment : Pattern) :
    intrinsicMeaning judgment →
      Nonempty (Derivation soundChecked judgment) := by
  rintro (⟨rfl, _⟩ | ⟨rfl, ⟨nativeVar⟩⟩)
  · exact ⟨extendedVariableDerivation⟩
  · let emptyInstance : IsEmpty EmptyVariable :=
      SyntacticNaturalModel.TowerExamples.no_variable_in_empty
        SyntacticContextual.TowerExamples.universeOne
    exact False.elim (emptyInstance.false nativeVar)

/-- The authored sound fragment, its generated OSLF reachability type, and
the independent intrinsic-variable meaning agree exactly. -/
def exactIntrinsicModel :
    ExactModel soundChecked intrinsicMeaning where
  ruleSound := sound_ruleSound
  complete := meaning_complete

theorem oslf_iff_intrinsicMeaning (judgment : Pattern) :
    (gsltOSLF (proofSearchGSLT soundChecked)).satisfies [judgment]
        (derivableNativeType soundChecked).pred ↔
      intrinsicMeaning judgment :=
  exactIntrinsicModel.nativeType_iff_meaning judgment

theorem positive_oslf_and_intrinsic :
    (gsltOSLF (proofSearchGSLT soundChecked)).satisfies
        [extendedVariableJudgment] (derivableNativeType soundChecked).pred ∧
      intrinsicMeaning extendedVariableJudgment := by
  constructor
  · exact (satisfies_derivableNativeType_iff_derivation
      soundChecked extendedVariableJudgment).2
        ⟨extendedVariableDerivation⟩
  · exact extendedVariableMeaning

/-- The structurally admitted negative rule is incompatible with the
independent CwF meaning, so no sound semantic bridge exists for it. -/
theorem unsound_rule_has_no_intrinsic_model :
    ¬ Nonempty (SoundModel unsoundChecked intrinsicMeaning) :=
  SoundModel.nonempty_forbidden_of_counterexample emptyVariableDerivation
    emptyVariableMeaning_false

#print axioms soundDefinition_valid
#print axioms unsoundDefinition_valid
#print axioms extendedVariableMeaning
#print axioms emptyVariableMeaning_false
#print axioms oslf_iff_intrinsicMeaning
#print axioms positive_oslf_and_intrinsic
#print axioms unsound_rule_has_no_intrinsic_model

end OSLFSyntacticModelCanary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
