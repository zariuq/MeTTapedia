import Mettapedia.GSLT.LanguageDef.CertificateGSLTRelationalInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTConversionElimination

/-!
# Canary: judgment-changing interpretation is a proper generalization

The source presentation below proves `A`; the target presentation proves `B`
and has no rule concluding `A`.  A retained relation witnesses that `A`
translates to `B`.  Consequently a proof-relevant relational interpretation
exists and maps the source proof, while the old judgment-preserving
interpretation type is empty.

The final theorem applies the same impossibility test to the independent
conversion-elimination fixture: an ordinary interpretation would produce the
uncast target judgment that that fixture proves uninhabited.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.RelationalInterpretationCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

private def judgmentA : Pattern := .apply "rel-canary-A" []
private def judgmentB : Pattern := .apply "rel-canary-B" []

private def sourceRule : RuleSchema :=
  { id := ⟨"rel-canary-source"⟩
    metavariables := []
    premises := []
    conclusion := judgmentA }

private def targetRule : RuleSchema :=
  { id := ⟨"rel-canary-target"⟩
    metavariables := []
    premises := []
    conclusion := judgmentB }

private def sourcePresentation : Presentation :=
  { language := LanguageDef.empty "relational-interpretation-source"
    calculus :=
      { judgments := [{ head := "rel-canary-A", arity := 0 }]
        rules := [sourceRule] } }

private def targetPresentation : Presentation :=
  { language := LanguageDef.empty "relational-interpretation-target"
    calculus :=
      { judgments := [{ head := "rel-canary-B", arity := 0 }]
        rules := [targetRule] } }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem sourcePresentation_valid :
    sourcePresentation.isValidV2 = true := by
  simp [sourcePresentation, Presentation.isValidV2,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.isValidV1, Presentation.ruleIds, emptyLanguage_validate,
    sourceRule, judgmentA, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private theorem targetPresentation_valid :
    targetPresentation.isValidV2 = true := by
  simp [targetPresentation, Presentation.isValidV2,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.isValidV1, Presentation.ruleIds, emptyLanguage_validate,
    targetRule, judgmentB, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def sourceValidated : ValidatedPresentation :=
  ⟨sourcePresentation, sourcePresentation_valid⟩

private def targetValidated : ValidatedPresentation :=
  ⟨targetPresentation, targetPresentation_valid⟩

private def sourceObject : Object := ⟨sourceValidated⟩
private def targetObject : Object := ⟨targetValidated⟩

private def sourceInstance : RuleInstance :=
  ⟨⟨"rel-canary-source"⟩, []⟩

private def targetInstance : RuleInstance :=
  ⟨⟨"rel-canary-target"⟩, []⟩

private theorem source_instantiates :
    instantiateRule? sourceValidated sourceInstance =
      some ([], judgmentA) := by
  simp [instantiateRule?, sourceValidated, sourcePresentation, sourceRule,
    sourceInstance, judgmentA, Presentation.lookupRule?, argumentsValidAt,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?]

private theorem target_instantiates :
    instantiateRule? targetValidated targetInstance =
      some ([], judgmentB) := by
  simp [instantiateRule?, targetValidated, targetPresentation, targetRule,
    targetInstance, judgmentB, Presentation.lookupRule?, argumentsValidAt,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?]

private def sourceDerivation : Derivation sourceValidated judgmentA :=
  .byRule sourceInstance
    (instantiateRule?_eq_some_iff_application.mp source_instantiates) .nil

private def targetDerivation : Derivation targetValidated judgmentB :=
  .byRule targetInstance
    (instantiateRule?_eq_some_iff_application.mp target_instantiates) .nil

private theorem source_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication sourceValidated ruleInstance
      premises conclusion) :
    premises = [] ∧ conclusion = judgmentA := by
  have executable :=
    instantiateRule?_eq_some_iff_application.mpr application
  rw [show ruleInstance = sourceInstance by
    rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
    cases application with
    | intro rule lookup argumentsValid sideConditions premisesInstantiate
        conclusionInstantiates =>
      simp [sourceValidated, sourcePresentation, sourceRule,
        Presentation.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      subst ruleId
      subst rule
      cases arguments with
      | nil => rfl
      | cons argument rest => simp [argumentsValidAt] at argumentsValid] at executable
  rw [source_instantiates] at executable
  simpa only [Prod.mk.injEq] using (Option.some.inj executable).symm

private theorem target_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication targetValidated ruleInstance
      premises conclusion) :
    premises = [] ∧ conclusion = judgmentB := by
  have executable :=
    instantiateRule?_eq_some_iff_application.mpr application
  rw [show ruleInstance = targetInstance by
    rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
    cases application with
    | intro rule lookup argumentsValid sideConditions premisesInstantiate
        conclusionInstantiates =>
      simp [targetValidated, targetPresentation, targetRule,
        Presentation.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      subst ruleId
      subst rule
      cases arguments with
      | nil => rfl
      | cons argument rest => simp [argumentsValidAt] at argumentsValid] at executable
  rw [target_instantiates] at executable
  simpa only [Prod.mk.injEq] using (Option.some.inj executable).symm

/-- The retained relation is intentionally inhabited at exactly one pair. -/
private inductive ChangesJudgment : Pattern → Pattern → Type where
  | here : ChangesJudgment judgmentA judgmentB

private theorem ChangesJudgment.target_eq :
    ∀ {source target}, ChangesJudgment source target → target = judgmentB
  | _, _, .here => rfl

/-- A genuine judgment-changing interpretation. -/
def sourceToTarget : RelationalInterpretation sourceObject targetObject where
  Related := ChangesJudgment
  onRule := by
    intro ruleInstance premises conclusion application premiseTargets
    obtain ⟨rfl, rfl⟩ := source_application_shape ruleInstance application
    cases premiseTargets
    exact ⟨judgmentB, ChangesJudgment.here,
      OpenDerivation.ofClosed targetDerivation⟩

/-- The source proof translates to a target proof while retaining evidence
that the conclusion changed. -/
theorem relational_translation_maps_proof :
    let translated := sourceToTarget.mapDerivation sourceDerivation
    translated.targetGoal = judgmentB ∧
      Nonempty (Derivation targetValidated translated.targetGoal) := by
  let translated := sourceToTarget.mapDerivation sourceDerivation
  have targetShape : translated.targetGoal = judgmentB :=
    ChangesJudgment.target_eq translated.related
  exact ⟨targetShape, ⟨translated.derivation⟩⟩

private theorem target_does_not_prove_source_judgment :
    ¬ Nonempty (Derivation targetValidated judgmentA) := by
  rintro ⟨derivation⟩
  cases derivation with
  | byRule ruleInstance application children =>
      have conclusionShape :=
        (target_application_shape ruleInstance application).2
      simp [judgmentA, judgmentB] at conclusionShape

/-- The old notion cannot express the fixture because it must preserve the
conclusion judgment literally. -/
theorem judgment_preserving_interpretation_is_empty :
    IsEmpty (Interpretation sourceObject targetObject) := by
  constructor
  intro interpretation
  exact target_does_not_prove_source_judgment
    ⟨interpretation.mapDerivation sourceDerivation⟩

/-- Positive and negative halves together show that the new notion is a
proper generalization on a compiled example. -/
theorem relational_interpretation_is_strictly_more_expressive :
    Nonempty (RelationalInterpretation.{0} sourceObject targetObject) ∧
      IsEmpty (Interpretation sourceObject targetObject) :=
  ⟨⟨sourceToTarget⟩, judgment_preserving_interpretation_is_empty⟩

/-- The independent conversion-elimination fixture fails for the same exact
reason: mapping its source derivation through an ordinary interpretation
would inhabit the target judgment already proved impossible. -/
theorem conversion_elimination_has_no_judgment_preserving_interpretation :
    IsEmpty
      (Interpretation
        ⟨ConversionElimination.extensionalValidated⟩
        ⟨ConversionElimination.intensionalValidated⟩) := by
  constructor
  intro interpretation
  rcases ConversionElimination.conversionElimination_needs_term_translation
    with ⟨⟨sourceProof⟩, targetCast, targetUncastImpossible⟩
  exact targetUncastImpossible ⟨interpretation.mapDerivation sourceProof⟩

#print axioms relational_translation_maps_proof
#print axioms relational_interpretation_is_strictly_more_expressive
#print axioms conversion_elimination_has_no_judgment_preserving_interpretation

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.RelationalInterpretationCanary
