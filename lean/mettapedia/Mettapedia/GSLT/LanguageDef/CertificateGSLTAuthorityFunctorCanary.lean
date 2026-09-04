import Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor

/-!
# A closed composite canary for functorial authority generation

The source proves `C` with one primitive axiom.  The target proves the same
claim only through the three-node path `A`, `A -> B`, `B -> C`.  A genuine
derivation-valued interpretation maps the source axiom to that target path.

Both calculi preserve an independently defined finite model in which exactly
`A`, `B`, and `C` are true.  Generated certificate transport therefore changes
proof structure without changing either the retained claim, semantic meaning,
or native checker result.  A fourth judgment `D` supplies the negative
semantic and wrong-claim controls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctorCanary

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor

private def judgmentA : Pattern := .apply "authority-functor-A" []
private def judgmentB : Pattern := .apply "authority-functor-B" []
private def judgmentC : Pattern := .apply "authority-functor-C" []
private def judgmentD : Pattern := .apply "authority-functor-D" []

private def sourceRuleC : RuleSchema :=
  { id := ⟨"authority-functor-source-c"⟩
    metavariables := []
    premises := []
    conclusion := judgmentC }

private def targetRuleA : RuleSchema :=
  { id := ⟨"authority-functor-target-a"⟩
    metavariables := []
    premises := []
    conclusion := judgmentA }

private def targetRuleAB : RuleSchema :=
  { id := ⟨"authority-functor-target-a-b"⟩
    metavariables := []
    premises := [judgmentA]
    conclusion := judgmentB }

private def targetRuleBC : RuleSchema :=
  { id := ⟨"authority-functor-target-b-c"⟩
    metavariables := []
    premises := [judgmentB]
    conclusion := judgmentC }

private def sourceDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "authority-functor-source")
    { judgments := [{ head := "authority-functor-C", arity := 0 }]
      rules := [sourceRuleC] }

private def targetDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "authority-functor-target")
    { judgments :=
        [{ head := "authority-functor-A", arity := 0 },
         { head := "authority-functor-B", arity := 0 },
         { head := "authority-functor-C", arity := 0 }]
      rules := [targetRuleA, targetRuleAB, targetRuleBC] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem emptyLanguage_terms (name : String) :
    (LanguageDef.empty name).terms = [] :=
  rfl

private theorem sourceDefinition_valid : sourceDefinition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [sourceDefinition, emptyLanguage_validate, emptyLanguage_terms,
    sourceRuleC, judgmentC,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

private theorem targetDefinition_valid : targetDefinition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [targetDefinition, emptyLanguage_validate, emptyLanguage_terms,
    targetRuleA, targetRuleAB, targetRuleBC,
    judgmentA, judgmentB, judgmentC,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    CalculusLanguageDef.conversionDeclarationValid]
  decide

private def sourceValidated : ValidatedCalculusLanguageDef :=
  ⟨sourceDefinition, sourceDefinition_valid⟩

private def targetValidated : ValidatedCalculusLanguageDef :=
  ⟨targetDefinition, targetDefinition_valid⟩

private def sourceObject : CertificateGSLT.Object := ⟨sourceValidated⟩
private def targetObject : CertificateGSLT.Object := ⟨targetValidated⟩

private def sourceInstanceC : RuleInstance :=
  ⟨⟨"authority-functor-source-c"⟩, []⟩

private def targetInstanceA : RuleInstance :=
  ⟨⟨"authority-functor-target-a"⟩, []⟩

private def targetInstanceAB : RuleInstance :=
  ⟨⟨"authority-functor-target-a-b"⟩, []⟩

private def targetInstanceBC : RuleInstance :=
  ⟨⟨"authority-functor-target-b-c"⟩, []⟩

private theorem source_c_instantiates :
    instantiateRule? sourceValidated sourceInstanceC =
      some ([], judgmentC) := by
  simp [instantiateRule?, sourceValidated, sourceDefinition, sourceRuleC,
    sourceInstanceC, judgmentC, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_a_instantiates :
    instantiateRule? targetValidated targetInstanceA =
      some ([], judgmentA) := by
  simp [instantiateRule?, targetValidated, targetDefinition, targetRuleA,
    targetRuleAB, targetRuleBC, targetInstanceA, judgmentA,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_ab_instantiates :
    instantiateRule? targetValidated targetInstanceAB =
      some ([judgmentA], judgmentB) := by
  simp [instantiateRule?, targetValidated, targetDefinition, targetRuleA,
    targetRuleAB, targetRuleBC, targetInstanceAB, judgmentA, judgmentB,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_bc_instantiates :
    instantiateRule? targetValidated targetInstanceBC =
      some ([judgmentB], judgmentC) := by
  simp [instantiateRule?, targetValidated, targetDefinition, targetRuleA,
    targetRuleAB, targetRuleBC, targetInstanceBC, judgmentB, judgmentC,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private def targetAOpen :
    OpenDerivation targetValidated [] judgmentA :=
  .byRule targetInstanceA
    (instantiateRule?_eq_some_iff_application.mp target_a_instantiates) .nil

private def targetBOpen :
    OpenDerivation targetValidated [] judgmentB :=
  .byRule targetInstanceAB
    (instantiateRule?_eq_some_iff_application.mp target_ab_instantiates)
    (.cons targetAOpen .nil)

private def targetCOpen :
    OpenDerivation targetValidated [] judgmentC :=
  .byRule targetInstanceBC
    (instantiateRule?_eq_some_iff_application.mp target_bc_instantiates)
    (.cons targetBOpen .nil)

private theorem source_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication sourceValidated ruleInstance premises
      conclusion) :
    ruleInstance = sourceInstanceC ∧ premises = [] ∧ conclusion = judgmentC := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [sourceValidated, sourceDefinition, sourceRuleC,
        CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      subst ruleId
      subst rule
      cases arguments with
      | cons argument arguments =>
          simp [argumentsValidAt] at argumentsValid
      | nil =>
          have reconstructed :
              RuleApplication sourceValidated sourceInstanceC premises
                conclusion :=
            .intro sourceRuleC (by rfl) argumentsValid sideConditions
              premisesInstantiate conclusionInstantiates
          have canonical :
              RuleApplication sourceValidated sourceInstanceC [] judgmentC :=
            instantiateRule?_eq_some_iff_application.mp source_c_instantiates
          have outputs := reconstructed.outputs_unique canonical
          exact ⟨rfl, outputs.1, outputs.2⟩

/-- The source axiom is implemented by the target's three-node derivation. -/
private def sourceToTarget : Interpretation sourceObject targetObject where
  onRule := fun ruleInstance {premises} {conclusion} application =>
    if shapes : premises = [] ∧ conclusion = judgmentC then by
      rw [shapes.1, shapes.2]
      exact targetCOpen
    else
      absurd
        ⟨(source_application_shape ruleInstance application).2.1,
          (source_application_shape ruleInstance application).2.2⟩
        shapes

/-! ## Independent semantics -/

private def Meaning (claim : Pattern) : Prop :=
  claim = judgmentA ∨ claim = judgmentB ∨ claim = judgmentC

private theorem source_rules_sound : RulesSound sourceObject Meaning := by
  intro ruleInstance premises conclusion application _premisesMeaning
  change RuleApplication sourceValidated ruleInstance premises conclusion at application
  have shape := source_application_shape ruleInstance application
  rw [shape.2.2]
  exact Or.inr (Or.inr rfl)

private theorem target_application_conclusion
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication targetValidated ruleInstance premises
      conclusion) :
    conclusion = judgmentA ∨ conclusion = judgmentB ∨
      conclusion = judgmentC := by
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [targetValidated, targetDefinition, targetRuleA, targetRuleAB,
        targetRuleBC, CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨_, rfl⟩ | ⟨_, remaining⟩
      · cases conclusionInstantiates with
        | apply items =>
            cases items
            exact Or.inl rfl
      · rcases remaining with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
        · cases conclusionInstantiates with
          | apply items =>
              cases items
              exact Or.inr (Or.inl rfl)
        · cases conclusionInstantiates with
          | apply items =>
              cases items
              exact Or.inr (Or.inr rfl)

private theorem target_rules_sound : RulesSound targetObject Meaning := by
  intro ruleInstance premises conclusion application _premisesMeaning
  change RuleApplication targetValidated ruleInstance premises conclusion at application
  exact target_application_conclusion ruleInstance application

private def sourcePresentation : SoundPresentation Meaning where
  object := sourceObject
  rulesSound := source_rules_sound

private def targetPresentation : SoundPresentation Meaning where
  object := targetObject
  rulesSound := target_rules_sound

/-! ## Functorial generation and controls -/

/-- A genuine non-identity arrow in the semantic presentation category. -/
def compositePresentationMorphism : sourcePresentation ⟶ targetPresentation :=
  sourceToTarget

/-- Its image is an exact native authority translation. -/
def generatedCompositeTranslation :
    generatedAuthority sourcePresentation ⟶
      generatedAuthority targetPresentation :=
  (generationFunctor Meaning).map compositePresentationMorphism

private def sourceClosed :
    (derivationClone sourceObject).Hom [] judgmentC :=
  .byRule sourceInstanceC
    (instantiateRule?_eq_some_iff_application.mp source_c_instantiates) .nil

private def sourceCertificate :
    (contract sourcePresentation).Certificate () :=
  ⟨judgmentC, sourceClosed⟩

/-- The source proof contains one primitive rule node. -/
theorem source_certificate_has_one_rule_node : sourceClosed.ruleCount = 1 :=
  rfl

/-- Transport is operationally nontrivial: the generated target certificate
contains the three authored target rule nodes. -/
theorem mapped_certificate_has_three_rule_nodes :
    ((generatedCompositeTranslation.mapCertificate () sourceCertificate).2).ruleCount =
      3 := by
  rfl

/-- Exact replay remains invariant despite the one-node-to-three-node
translation. -/
theorem composite_translation_check_commutes :
    ((contract targetPresentation).checker ()).check judgmentC
        (generatedCompositeTranslation.mapCertificate () sourceCertificate) =
      ((contract sourcePresentation).checker ()).check judgmentC
        sourceCertificate :=
  generatedCompositeTranslation.check_commutes () judgmentC sourceCertificate

/-- Both sides accept the retained claim. -/
theorem both_generated_checkers_accept :
    ((contract sourcePresentation).checker ()).check judgmentC
          sourceCertificate = true ∧
      ((contract targetPresentation).checker ()).check judgmentC
          (generatedCompositeTranslation.mapCertificate () sourceCertificate) =
        true := by
  constructor
  · exact generated_checker_accepts_exact_claim sourcePresentation sourceClosed
  · rw [composite_translation_check_commutes]
    exact generated_checker_accepts_exact_claim sourcePresentation sourceClosed

/-- The independent model has a true claim. -/
theorem judgmentC_has_meaning : Meaning judgmentC :=
  Or.inr (Or.inr rfl)

/-- The independent model also has a concrete false claim. -/
theorem judgmentD_lacks_meaning : ¬ Meaning judgmentD := by
  simp [Meaning, judgmentA, judgmentB, judgmentC, judgmentD]

/-- Submitting the transported proof at the false, different claim is rejected. -/
theorem transported_certificate_rejects_wrong_claim :
    ((contract targetPresentation).checker ()).check judgmentD
        (generatedCompositeTranslation.mapCertificate () sourceCertificate) =
      false := by
  change decide (judgmentC = judgmentD) = false
  decide

#print axioms compositePresentationMorphism
#print axioms generatedCompositeTranslation
#print axioms mapped_certificate_has_three_rule_nodes
#print axioms composite_translation_check_commutes
#print axioms both_generated_checkers_accept
#print axioms judgmentD_lacks_meaning
#print axioms transported_certificate_rejects_wrong_claim

end Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctorCanary
