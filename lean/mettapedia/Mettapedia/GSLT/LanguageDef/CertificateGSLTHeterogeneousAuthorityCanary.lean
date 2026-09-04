import Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority

/-!
# A syntax- and meaning-changing authority-generation canary

The source has one primitive axiom proving `C`.  Its judgment embedding wraps
every source claim in a new target constructor, so the source and target do
not share a claim spelling.  The wrapped `C` is proved in the target only by
the three-node path `A`, `A -> B`, `B -> C`.

The source meaning contains only source `C`; the target meaning contains the
three wrapped target judgments.  These predicates are deliberately unequal.
Nevertheless the semantic embedding preserves source meaning, transports the
one-node proof to the three-node proof, and makes both accepting and rejecting
checker observations commute exactly.  Thus heterogeneous generation is not
being validated by an identity claim map, a shared semantics, or a one-node
rule lookup.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthorityCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority

private def sourceA : Pattern := .apply "heterogeneous-source-A" []
private def sourceB : Pattern := .apply "heterogeneous-source-B" []
private def sourceC : Pattern := .apply "heterogeneous-source-C" []
private def sourceD : Pattern := .apply "heterogeneous-source-D" []

/-- A genuine representation change rather than a renaming theorem asserted
about the identity function. -/
private def embedClaim (claim : Pattern) : Pattern :=
  .apply "heterogeneous-target-claim" [claim]

private def targetA : Pattern := embedClaim sourceA
private def targetB : Pattern := embedClaim sourceB
private def targetC : Pattern := embedClaim sourceC

private theorem embedClaim_injective : Function.Injective embedClaim := by
  intro left right equality
  simp only [embedClaim] at equality
  have argumentsEqual : [left] = [right] := by
    injection equality
  exact List.cons.inj argumentsEqual |>.1

private theorem sourceC_not_targetC : sourceC ≠ targetC := by
  simp [sourceC, targetC, embedClaim]

private def sourceRuleC : RuleSchema :=
  { id := ⟨"heterogeneous-source-c"⟩
    metavariables := []
    premises := []
    conclusion := sourceC }

private def targetRuleA : RuleSchema :=
  { id := ⟨"heterogeneous-target-a"⟩
    metavariables := []
    premises := []
    conclusion := targetA }

private def targetRuleAB : RuleSchema :=
  { id := ⟨"heterogeneous-target-a-b"⟩
    metavariables := []
    premises := [targetA]
    conclusion := targetB }

private def targetRuleBC : RuleSchema :=
  { id := ⟨"heterogeneous-target-b-c"⟩
    metavariables := []
    premises := [targetB]
    conclusion := targetC }

private def sourceDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (LanguageDef.empty "heterogeneous-authority-source")
    { judgments :=
        [{ head := "heterogeneous-source-C", arity := 0 },
          { head := "heterogeneous-source-D", arity := 0 }]
      rules := [sourceRuleC] }

private def targetLanguage : LanguageDef :=
  { name := "heterogeneous-authority-target"
    types := [TypeDecl.plain "heterogeneous-embedded-source"]
    terms :=
      [{ label := "heterogeneous-source-A"
         category := "heterogeneous-embedded-source"
         params := []
         syntaxPattern := [] },
       { label := "heterogeneous-source-B"
         category := "heterogeneous-embedded-source"
         params := []
         syntaxPattern := [] },
       { label := "heterogeneous-source-C"
         category := "heterogeneous-embedded-source"
         params := []
         syntaxPattern := [] },
       { label := "heterogeneous-source-D"
         category := "heterogeneous-embedded-source"
         params := []
         syntaxPattern := [] }]
    equations := []
    rewrites := [] }

private def targetDefinition : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    targetLanguage
    { judgments :=
        [{ head := "heterogeneous-target-claim", arity := 1 }]
      rules := [targetRuleA, targetRuleAB, targetRuleBC] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem emptyLanguage_terms (name : String) :
    (LanguageDef.empty name).terms = [] :=
  rfl

private theorem targetLanguage_validate : targetLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly targetLanguage <;>
    simp [targetLanguage, LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr]

private theorem sourceDefinition_valid : sourceDefinition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [sourceDefinition, emptyLanguage_validate, emptyLanguage_terms,
    sourceRuleC, sourceC,
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
  have definitionLanguageValid :
      targetDefinition.toLanguageDef.validate = [] := by
    simpa [targetDefinition] using targetLanguage_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [definitionLanguageValid]
  simp [targetDefinition, targetLanguage,
    targetRuleA, targetRuleAB, targetRuleBC,
    targetA, targetB, targetC, embedClaim, sourceA, sourceB, sourceC,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.ruleIds,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
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
  ⟨⟨"heterogeneous-source-c"⟩, []⟩

private def targetInstanceA : RuleInstance :=
  ⟨⟨"heterogeneous-target-a"⟩, []⟩

private def targetInstanceAB : RuleInstance :=
  ⟨⟨"heterogeneous-target-a-b"⟩, []⟩

private def targetInstanceBC : RuleInstance :=
  ⟨⟨"heterogeneous-target-b-c"⟩, []⟩

private theorem source_c_instantiates :
    instantiateRule? sourceValidated sourceInstanceC =
      some ([], sourceC) := by
  simp [instantiateRule?, sourceValidated, sourceDefinition, sourceRuleC,
    sourceInstanceC, sourceC, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_a_instantiates :
    instantiateRule? targetValidated targetInstanceA =
      some ([], targetA) := by
  simp [instantiateRule?, targetValidated, targetDefinition, targetRuleA,
    targetRuleAB, targetRuleBC, targetInstanceA, targetA, embedClaim, sourceA,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_ab_instantiates :
    instantiateRule? targetValidated targetInstanceAB =
      some ([targetA], targetB) := by
  simp [instantiateRule?, targetValidated, targetDefinition, targetRuleA,
    targetRuleAB, targetRuleBC, targetInstanceAB, targetA, targetB,
    embedClaim, sourceA, sourceB,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_bc_instantiates :
    instantiateRule? targetValidated targetInstanceBC =
      some ([targetB], targetC) := by
  simp [instantiateRule?, targetValidated, targetDefinition, targetRuleA,
    targetRuleAB, targetRuleBC, targetInstanceBC, targetB, targetC,
    embedClaim, sourceB, sourceC,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private def targetAOpen : OpenDerivation targetValidated [] targetA :=
  .byRule targetInstanceA
    (instantiateRule?_eq_some_iff_application.mp target_a_instantiates) .nil

private def targetBOpen : OpenDerivation targetValidated [] targetB :=
  .byRule targetInstanceAB
    (instantiateRule?_eq_some_iff_application.mp target_ab_instantiates)
    (.cons targetAOpen .nil)

private def targetCOpen : OpenDerivation targetValidated [] targetC :=
  .byRule targetInstanceBC
    (instantiateRule?_eq_some_iff_application.mp target_bc_instantiates)
    (.cons targetBOpen .nil)

private theorem source_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication sourceValidated ruleInstance premises
      conclusion) :
    ruleInstance = sourceInstanceC ∧ premises = [] ∧ conclusion = sourceC := by
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
              RuleApplication sourceValidated sourceInstanceC [] sourceC :=
            instantiateRule?_eq_some_iff_application.mp source_c_instantiates
          have outputs := reconstructed.outputs_unique canonical
          exact ⟨rfl, outputs.1, outputs.2⟩

private def judgmentEmbedding : JudgmentEmbedding sourceObject targetObject where
  mapClaim := embedClaim
  mapClaim_injective := embedClaim_injective
  onRule := by
    intro ruleInstance premises conclusion application
    have shape := source_application_shape ruleInstance application
    rw [shape.2.1, shape.2.2]
    exact targetCOpen

/-! ## Genuinely different independent semantics -/

private def SourceMeaning (claim : Pattern) : Prop :=
  claim = sourceC

private def TargetMeaning (claim : Pattern) : Prop :=
  claim = targetA ∨ claim = targetB ∨ claim = targetC

private theorem source_rules_sound : RulesSound sourceObject SourceMeaning := by
  intro ruleInstance premises conclusion application _premisesMeaning
  change RuleApplication sourceValidated ruleInstance premises conclusion at application
  exact (source_application_shape ruleInstance application).2.2

private theorem target_application_conclusion
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication targetValidated ruleInstance premises
      conclusion) :
    conclusion = targetA ∨ conclusion = targetB ∨ conclusion = targetC := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [targetValidated, targetDefinition, targetRuleA, targetRuleAB,
        targetRuleBC, CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, rfl⟩ | ⟨_, remaining⟩
      · subst ruleId
        cases arguments with
        | cons argument arguments =>
            simp [argumentsValidAt] at argumentsValid
        | nil =>
            have reconstructed :
                RuleApplication targetValidated targetInstanceA premises
                  conclusion :=
              .intro targetRuleA (by rfl) argumentsValid sideConditions
                premisesInstantiate conclusionInstantiates
            have canonical :
                RuleApplication targetValidated targetInstanceA [] targetA :=
              instantiateRule?_eq_some_iff_application.mp target_a_instantiates
            exact Or.inl (reconstructed.outputs_unique canonical).2
      · rcases remaining with ⟨ruleIdShape, rfl⟩ | ⟨_, ruleIdShape, rfl⟩
        · subst ruleId
          cases arguments with
          | cons argument arguments =>
              simp [argumentsValidAt] at argumentsValid
          | nil =>
              have reconstructed :
                  RuleApplication targetValidated targetInstanceAB premises
                    conclusion :=
                .intro targetRuleAB (by rfl) argumentsValid sideConditions
                  premisesInstantiate conclusionInstantiates
              have canonical :
                  RuleApplication targetValidated targetInstanceAB [targetA]
                    targetB :=
                instantiateRule?_eq_some_iff_application.mp target_ab_instantiates
              exact Or.inr (Or.inl
                (reconstructed.outputs_unique canonical).2)
        · subst ruleId
          cases arguments with
          | cons argument arguments =>
              simp [argumentsValidAt] at argumentsValid
          | nil =>
              have reconstructed :
                  RuleApplication targetValidated targetInstanceBC premises
                    conclusion :=
                .intro targetRuleBC (by rfl) argumentsValid sideConditions
                  premisesInstantiate conclusionInstantiates
              have canonical :
                  RuleApplication targetValidated targetInstanceBC [targetB]
                    targetC :=
                instantiateRule?_eq_some_iff_application.mp target_bc_instantiates
              exact Or.inr (Or.inr
                (reconstructed.outputs_unique canonical).2)

private theorem target_rules_sound : RulesSound targetObject TargetMeaning := by
  intro ruleInstance premises conclusion application _premisesMeaning
  change RuleApplication targetValidated ruleInstance premises conclusion at application
  exact target_application_conclusion ruleInstance application

private def sourcePresentation : SemanticPresentation where
  object := sourceObject
  Meaning := SourceMeaning
  rulesSound := source_rules_sound

private def targetPresentation : SemanticPresentation where
  object := targetObject
  Meaning := TargetMeaning
  rulesSound := target_rules_sound

private def semanticEmbedding :
    SemanticEmbedding sourcePresentation targetPresentation where
  proof := judgmentEmbedding
  meaning_preserved := by
    intro claim meaningful
    change claim = sourceC at meaningful
    subst claim
    exact Or.inr (Or.inr rfl)

private def sourceClosed :
    (derivationClone sourceObject).Hom [] sourceC :=
  .byRule sourceInstanceC
    (instantiateRule?_eq_some_iff_application.mp source_c_instantiates) .nil

private def sourceCertificate :
    (contract sourcePresentation).Certificate () :=
  ⟨sourceC, sourceClosed⟩

private def generatedTranslation := map semanticEmbedding

/-! ## Positive and negative controls -/

/-- The claim representation genuinely changes. -/
theorem mapped_claim_is_targetC_and_not_sourceC :
    semanticEmbedding.proof.mapClaim sourceC = targetC ∧
      semanticEmbedding.proof.mapClaim sourceC ≠ sourceC := by
  constructor
  · rfl
  · exact sourceC_not_targetC.symm

/-- The two independently supplied meaning predicates are not extensionally
equal on the shared `Pattern` carrier. -/
theorem source_and_target_meanings_differ :
    SourceMeaning ≠ TargetMeaning := by
  intro equality
  have targetAtSourceC : TargetMeaning sourceC :=
    equality ▸ (show SourceMeaning sourceC from rfl)
  simp [TargetMeaning, targetA, targetB, targetC, embedClaim,
    sourceA, sourceB, sourceC] at targetAtSourceC

/-- The source certificate contains one primitive rule node. -/
theorem source_certificate_has_one_rule_node : sourceClosed.ruleCount = 1 :=
  rfl

/-- Heterogeneous transport expands it to the three target rule nodes. -/
theorem mapped_certificate_has_three_rule_nodes :
    ((generatedTranslation.mapCertificate () sourceCertificate).2).ruleCount =
      3 := by
  rfl

/-- Exact checker replay survives both the syntax change and proof expansion. -/
theorem generated_translation_check_commutes :
    ((contract targetPresentation).checker ()).check targetC
        (generatedTranslation.mapCertificate () sourceCertificate) =
      ((contract sourcePresentation).checker ()).check sourceC
        sourceCertificate :=
  generatedTranslation.check_commutes () sourceC sourceCertificate

/-- Both generated checkers accept their differently spelled exact claims. -/
theorem both_generated_checkers_accept :
    ((contract sourcePresentation).checker ()).check sourceC
          sourceCertificate = true ∧
      ((contract targetPresentation).checker ()).check targetC
          (generatedTranslation.mapCertificate () sourceCertificate) = true := by
  constructor
  · rfl
  · rfl

/-- A different source claim remains different after the embedding. -/
theorem mapped_sourceD_ne_targetC :
    semanticEmbedding.proof.mapClaim sourceD ≠ targetC := by
  exact no_collision_in_generated_map semanticEmbedding (by
    simp [sourceD, sourceC])

/-- Transport cannot turn submission at the wrong translated claim into
acceptance. -/
theorem transported_certificate_rejects_wrong_claim :
    ((contract targetPresentation).checker ()).check
        (semanticEmbedding.proof.mapClaim sourceD)
        (generatedTranslation.mapCertificate () sourceCertificate) = false :=
  mapped_certificate_rejects_wrong_claim semanticEmbedding (by
    simp [sourceC, sourceD]) sourceClosed

/-- The target has meaningful judgments which are not source meanings; meaning
preservation is directional rather than an asserted equivalence. -/
theorem targetA_meaning_but_not_source_meaning :
    TargetMeaning targetA ∧ ¬ SourceMeaning targetA := by
  constructor
  · exact Or.inl rfl
  · simp [SourceMeaning, targetA, embedClaim, sourceA, sourceC]

#print axioms mapped_claim_is_targetC_and_not_sourceC
#print axioms source_and_target_meanings_differ
#print axioms mapped_certificate_has_three_rule_nodes
#print axioms generated_translation_check_commutes
#print axioms both_generated_checkers_accept
#print axioms mapped_sourceD_ne_targetC
#print axioms transported_certificate_rejects_wrong_claim
#print axioms targetA_meaning_but_not_source_meaning

end Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthorityCanary
