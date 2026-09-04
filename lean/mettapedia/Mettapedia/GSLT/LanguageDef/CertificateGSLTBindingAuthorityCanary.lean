import Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthority

/-!
# A binder-bearing structural authority canary

This canary connects the complete binding-aware authority path rather than
testing its layers in isolation.  The source calculus contains an authored
single-binder constructor and a primitive closed judgment whose body refers to
that binder.  A structural morphism changes every language namespace, while
keeping constructor and judgment renaming deliberately distinct.  Its rule
implementation transports the source axiom into the differently named target
calculus.

The source and target meanings are independently supplied.  The target also
has one meaningful, target-only term which the source cannot express through
the structural map.  Positive controls cover binder naturality, semantic
preservation, proof transport, and exact checker replay.  Negative controls
cover wrong-claim rejection, namespace collapse, and the directional nature
of meaning preservation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthorityCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthority

/-! ## Two genuinely different calculus signatures -/

/-- Prefix a symbol by one namespace marker.  The list-level definition makes
injectivity independent of any assumptions about textual delimiters. -/
private def tag (marker : Char) (name : String) : String :=
  String.ofList (marker :: name.toList)

private theorem tag_injective (marker : Char) :
    Function.Injective (tag marker) := by
  intro left right equality
  have listEquality : marker :: left.toList = marker :: right.toList :=
    String.ofList_injective equality
  exact String.toList_injective (List.cons.inj listEquality).2

private def symbols : CalculusLanguageSymbols where
  sort := tag 's'
  constructor := tag 'c'
  relation := tag 'p'
  equation := tag 'e'
  rewrite := tag 'w'
  judgment := tag 'j'
  rule := tag 'r'

private def sourceExprName := "binding-source-expr"
private def sourceAtomName := "binding-source-atom"
private def sourceBinderName := "binding-source-bind"
private def sourceJudgmentName := "binding-source-holds"
private def sourceRuleName := "binding-source-axiom"

private def sourceExpr : TypeDecl := TypeDecl.plain sourceExprName

private def sourceAtomDeclaration : GrammarRule :=
  { label := sourceAtomName
    category := sourceExprName
    params := []
    syntaxPattern := [] }

/-- The authored source signature contains a real binding position. -/
private def sourceBinderDeclaration : GrammarRule :=
  { label := sourceBinderName
    category := sourceExprName
    params := [.abstraction "body" (.base sourceExprName)]
    syntaxPattern := [] }

private def sourceAtom : Pattern := .apply sourceAtomName []

private def sourceBoundTerm : Pattern :=
  .apply sourceBinderName [.lambda none (.bvar 0)]

def sourceClaim : Pattern :=
  .apply sourceJudgmentName [sourceBoundTerm]

private def sourceRule : RuleSchema :=
  { id := ⟨sourceRuleName⟩
    metavariables := []
    premises := []
    conclusion := sourceClaim }

private def sourceDefinition : CalculusLanguageDef :=
  { name := "binding-authority-source"
    types := [sourceExpr]
    terms := [sourceAtomDeclaration, sourceBinderDeclaration]
    equations := []
    rewrites := []
    judgments := [{ head := sourceJudgmentName, arity := 1 }]
    rules := [sourceRule]
    conversion := none }

/-- One target-only constructor witnesses that semantic preservation is
directional and that the target is not merely a renamed copy. -/
private def targetOnlyName := tag 'x' "binding-target-only"

private def targetOnlyDeclaration : GrammarRule :=
  { label := targetOnlyName
    category := symbols.sort sourceExprName
    params := []
    syntaxPattern := [] }

private def targetDefinition : CalculusLanguageDef :=
  { name := "binding-authority-target"
    types := sourceDefinition.types.map
      (mapTypeDecl symbols.toLanguageDefSymbolMap)
    terms :=
      sourceDefinition.terms.map
        (mapGrammarRule symbols.toLanguageDefSymbolMap) ++
        [targetOnlyDeclaration]
    equations := sourceDefinition.equations.map
      (mapEquation symbols.toLanguageDefSymbolMap)
    rewrites := sourceDefinition.rewrites.map
      (mapRewriteRule symbols.toLanguageDefSymbolMap)
    judgments := sourceDefinition.judgments.map (mapJudgmentDecl symbols)
    rules := sourceDefinition.rules.map (mapRuleSchema symbols)
    conversion := none }

private theorem sourceLanguage_validate :
    sourceDefinition.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sourceDefinition, sourceExpr, sourceAtomDeclaration,
      sourceBinderDeclaration, LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr, TypeExpr.baseNames, sourceAtomName,
      sourceBinderName]

private theorem targetLanguage_validate :
    targetDefinition.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [targetDefinition, sourceDefinition, sourceExpr,
      sourceAtomDeclaration, sourceBinderDeclaration, targetOnlyDeclaration,
      mapTypeDecl, mapGrammarRule, mapTermParam, mapTypeExpr,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames, symbols, sourceAtomName, sourceBinderName,
      targetOnlyName, tag]

private theorem sourceDefinition_valid : sourceDefinition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [sourceLanguage_validate]
  simp [sourceDefinition, sourceRule, sourceClaim, sourceBoundTerm,
    sourceExpr, sourceAtomDeclaration, sourceBinderDeclaration,
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

private theorem targetDefinition_valid : targetDefinition.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [targetLanguage_validate]
  simp [targetDefinition, sourceDefinition, sourceRule, sourceClaim,
    sourceBoundTerm, sourceExpr, sourceAtomDeclaration,
    sourceBinderDeclaration, targetOnlyDeclaration,
    mapTypeDecl, mapGrammarRule, mapTermParam, mapTypeExpr,
    mapJudgmentDecl, mapRuleSchema, mapJudgmentPattern, mapPattern,
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
    CalculusLanguageDef.conversionDeclarationValid, symbols]
  decide

private def sourceValidated : ValidatedCalculusLanguageDef :=
  ⟨sourceDefinition, sourceDefinition_valid⟩

private def targetValidated : ValidatedCalculusLanguageDef :=
  ⟨targetDefinition, targetDefinition_valid⟩

private def sourceObject : CertificateGSLT.Object := ⟨sourceValidated⟩
private def targetObject : CertificateGSLT.Object := ⟨targetValidated⟩

def targetClaim : Pattern :=
  mapJudgmentPattern symbols sourceClaim

private def targetOnlyTerm : Pattern := .apply targetOnlyName []

private def targetOnlyClaim : Pattern :=
  .apply (symbols.judgment sourceJudgmentName) [targetOnlyTerm]

/-! ## Complete structural and proof-relevant action -/

private def structural :
    CalculusStructuralMorphism sourceValidated targetValidated where
  symbols := symbols
  mapsTypes declaration membership := by
    change List.Mem declaration sourceDefinition.types at membership
    change List.Mem (mapTypeDecl symbols.toLanguageDefSymbolMap declaration)
      (sourceDefinition.types.map
        (mapTypeDecl symbols.toLanguageDefSymbolMap))
    exact List.mem_map.mpr ⟨declaration, membership, rfl⟩
  mapsTerms declaration membership := by
    change List.Mem declaration sourceDefinition.terms at membership
    change List.Mem
      (mapGrammarRule symbols.toLanguageDefSymbolMap declaration)
      (sourceDefinition.terms.map
          (mapGrammarRule symbols.toLanguageDefSymbolMap) ++
        [targetOnlyDeclaration])
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨declaration, membership, rfl⟩)
  mapsEquations declaration membership := by
    change List.Mem declaration sourceDefinition.equations at membership
    change List.Mem (mapEquation symbols.toLanguageDefSymbolMap declaration)
      (sourceDefinition.equations.map
        (mapEquation symbols.toLanguageDefSymbolMap))
    exact List.mem_map.mpr ⟨declaration, membership, rfl⟩
  mapsRewrites declaration membership := by
    change List.Mem declaration sourceDefinition.rewrites at membership
    change List.Mem
      (mapRewriteRule symbols.toLanguageDefSymbolMap declaration)
      (sourceDefinition.rewrites.map
        (mapRewriteRule symbols.toLanguageDefSymbolMap))
    exact List.mem_map.mpr ⟨declaration, membership, rfl⟩
  mapsJudgments declaration membership := by
    change List.Mem declaration sourceDefinition.judgments at membership
    change List.Mem (mapJudgmentDecl symbols declaration)
      (sourceDefinition.judgments.map (mapJudgmentDecl symbols))
    exact List.mem_map.mpr ⟨declaration, membership, rfl⟩
  mapsRules declaration membership := by
    change List.Mem declaration sourceDefinition.rules at membership
    change List.Mem (mapRuleSchema symbols declaration)
      (sourceDefinition.rules.map (mapRuleSchema symbols))
    exact List.mem_map.mpr ⟨declaration, membership, rfl⟩
  mapsConversion declaration equality := by
    change (none : Option ConversionDecl) = some declaration at equality
    simp at equality

private def sourceInstance : RuleInstance := ⟨⟨sourceRuleName⟩, []⟩

private def targetInstance : RuleInstance :=
  ⟨⟨symbols.rule sourceRuleName⟩, []⟩

private theorem source_instantiates :
    instantiateRule? sourceValidated sourceInstance =
      some ([], sourceClaim) := by
  simp [instantiateRule?, sourceValidated, sourceDefinition, sourceRule,
    sourceInstance, sourceClaim, sourceBoundTerm,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?]

private theorem target_instantiates :
    instantiateRule? targetValidated targetInstance =
      some ([], targetClaim) := by
  simp [instantiateRule?, targetValidated, targetDefinition,
    sourceDefinition, sourceRule, targetInstance, targetClaim, sourceClaim,
    sourceBoundTerm, mapRuleSchema, mapJudgmentPattern, mapPattern,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemasAt?, symbols]

private def targetOpen : OpenDerivation targetValidated [] targetClaim :=
  .byRule targetInstance
    (instantiateRule?_eq_some_iff_application.mp target_instantiates) .nil

private theorem source_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication sourceValidated ruleInstance premises
      conclusion) :
    ruleInstance = sourceInstance ∧ premises = [] ∧
      conclusion = sourceClaim := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [sourceValidated, sourceDefinition, sourceRule,
        CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      subst ruleId
      subst rule
      cases arguments with
      | cons argument arguments =>
          change argumentsValidAt [] (argument :: arguments) = true at argumentsValid
          simp [argumentsValidAt] at argumentsValid
      | nil =>
          have reconstructed :
              RuleApplication sourceValidated sourceInstance premises
                conclusion :=
            .intro sourceRule (by rfl) argumentsValid sideConditions
              premisesInstantiate conclusionInstantiates
          have canonical :
              RuleApplication sourceValidated sourceInstance [] sourceClaim :=
            instantiateRule?_eq_some_iff_application.mp source_instantiates
          have outputs := reconstructed.outputs_unique canonical
          exact ⟨rfl, outputs.1, outputs.2⟩

private theorem target_application_shape
    (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication targetValidated ruleInstance premises
      conclusion) :
    ruleInstance = targetInstance ∧ premises = [] ∧
      conclusion = targetClaim := by
  rcases ruleInstance with ⟨⟨ruleId⟩, arguments⟩
  cases application with
  | intro rule lookup argumentsValid sideConditions premisesInstantiate
      conclusionInstantiates =>
      simp [targetValidated, targetDefinition, sourceDefinition, sourceRule,
        CalculusLanguageDef.lookupRule?] at lookup
      rcases lookup with ⟨ruleIdShape, ruleShape⟩
      have ruleIdValue : symbols.rule sourceRuleName = ruleId :=
        congrArg RuleId.value ruleIdShape
      subst ruleId
      subst rule
      cases arguments with
      | cons argument arguments =>
          change argumentsValidAt [] (argument :: arguments) = true at argumentsValid
          simp [argumentsValidAt] at argumentsValid
      | nil =>
          have reconstructed :
              RuleApplication targetValidated targetInstance premises
                conclusion :=
            .intro (mapRuleSchema symbols sourceRule) (by rfl)
              argumentsValid sideConditions premisesInstantiate
              conclusionInstantiates
          have canonical :
              RuleApplication targetValidated targetInstance [] targetClaim :=
            instantiateRule?_eq_some_iff_application.mp target_instantiates
          have outputs := reconstructed.outputs_unique canonical
          exact ⟨rfl, outputs.1, outputs.2⟩

private def proofEmbedding :
    BindingJudgmentEmbedding sourceObject targetObject where
  structural := structural
  constructor_injective := tag_injective 'c'
  judgment_injective := tag_injective 'j'
  onRule := by
    intro ruleInstance premises conclusion application
    have shape := source_application_shape ruleInstance application
    rw [shape.2.1, shape.2.2]
    exact targetOpen

/-! ## Independent semantics and generated authority -/

private def SourceMeaning (claim : Pattern) : Prop :=
  claim = sourceClaim

private def TargetMeaning (claim : Pattern) : Prop :=
  claim = targetClaim ∨ claim = targetOnlyClaim

private theorem source_rules_sound : RulesSound sourceObject SourceMeaning := by
  intro ruleInstance premises conclusion application _premisesMeaning
  exact (source_application_shape ruleInstance application).2.2

private theorem target_rules_sound : RulesSound targetObject TargetMeaning := by
  intro ruleInstance premises conclusion application _premisesMeaning
  exact Or.inl (target_application_shape ruleInstance application).2.2

def sourcePresentation : SemanticPresentation where
  object := sourceObject
  Meaning := SourceMeaning
  rulesSound := source_rules_sound

def targetPresentation : SemanticPresentation where
  object := targetObject
  Meaning := TargetMeaning
  rulesSound := target_rules_sound

def semanticEmbedding :
    BindingSemanticEmbedding sourcePresentation targetPresentation where
  proof := proofEmbedding
  meaning_preserved := by
    intro claim meaningful
    change claim = sourceClaim at meaningful
    subst claim
    exact Or.inl rfl

private def sourceClosed :
    (derivationClone sourceObject).Hom [] sourceClaim :=
  .byRule sourceInstance
    (instantiateRule?_eq_some_iff_application.mp source_instantiates) .nil

def sourceCertificate :
    (contract sourcePresentation).Certificate () :=
  ⟨sourceClaim, sourceClosed⟩

private def generatedTranslation := BindingSemanticEmbedding.map semanticEmbedding

/-! ## Positive and negative controls -/

/-- The closed source theorem contains a genuine bound occurrence and changes
both its outer judgment head and its inner constructor namespace. -/
theorem mapped_bound_claim_is_exact_and_nontrivial :
    proofEmbedding.toJudgmentEmbedding.mapClaim sourceClaim = targetClaim ∧
      targetClaim ≠ sourceClaim := by
  constructor
  · rfl
  · intro equality
    have headEquality :
        symbols.judgment sourceJudgmentName = sourceJudgmentName := by
      change Pattern.apply (symbols.judgment sourceJudgmentName) _ =
          Pattern.apply sourceJudgmentName _ at equality
      injection equality
    have taggedHeadDifferent :
        symbols.judgment sourceJudgmentName ≠ sourceJudgmentName := by
      decide
    exact taggedHeadDifferent headEquality

/-- Opening an outer variable beneath the authored binder commutes with the
structural map.  The replacement travels through the constructor namespace,
while the outer judgment travels through the judgment namespace. -/
theorem open_binder_template_commutes :
    let template :=
      Pattern.apply sourceJudgmentName
        [.apply sourceBinderName [.lambda none (.bvar 1)]]
    proofEmbedding.toJudgmentEmbedding.mapClaim
        (openBVar 0 sourceAtom template) =
      openBVar 0
        (mapPattern symbols.toLanguageDefSymbolMap sourceAtom)
        (proofEmbedding.toJudgmentEmbedding.mapClaim template) := by
  dsimp only
  exact proofEmbedding.mapClaim_openBVar 0 sourceAtom sourceJudgmentName
    [.apply sourceBinderName [.lambda none (.bvar 1)]]

/-- The source certificate is replayed at the exact translated binder-bearing
claim. -/
theorem translated_certificate_accepts :
    ((contract targetPresentation).checker ()).check targetClaim
        (generatedTranslation.mapCertificate () sourceCertificate) = true := by
  rfl

/-- Exact checker replay is preserved by the binding-aware authority map. -/
theorem translated_checker_commutes :
    ((contract targetPresentation).checker ()).check targetClaim
        (generatedTranslation.mapCertificate () sourceCertificate) =
      ((contract sourcePresentation).checker ()).check sourceClaim
        sourceCertificate :=
  BindingSemanticEmbedding.map_check_commutes semanticEmbedding sourceClaim
    sourceCertificate

/-- Constructor and judgment namespaces cannot be interchanged merely because
both are represented by strings. -/
theorem constructor_and_judgment_images_differ :
    symbols.constructor sourceBinderName ≠
      symbols.judgment sourceBinderName := by
  simp [symbols, tag]

/-- A translated certificate submitted at another translated judgment remains
rejected. -/
theorem translated_certificate_rejects_wrong_claim :
    ((contract targetPresentation).checker ()).check
        (proofEmbedding.toJudgmentEmbedding.mapClaim
          (.apply sourceJudgmentName [sourceAtom]))
        (generatedTranslation.mapCertificate () sourceCertificate) = false := by
  apply mapped_certificate_rejects_wrong_claim
    semanticEmbedding.toSemanticEmbedding
  simp [sourceClaim, sourceBoundTerm, sourceAtom, sourceAtomName,
    sourceBinderName]

/-- Target meaning properly extends the transported source meaning; semantic
preservation is not silently strengthened to equivalence. -/
theorem target_only_meaning_has_no_source_preimage_at_same_claim :
    TargetMeaning targetOnlyClaim ∧ ¬ SourceMeaning targetOnlyClaim := by
  constructor
  · exact Or.inr rfl
  · intro equality
    have headEquality :
        symbols.judgment sourceJudgmentName = sourceJudgmentName := by
      change Pattern.apply (symbols.judgment sourceJudgmentName) _ =
          Pattern.apply sourceJudgmentName _ at equality
      injection equality
    have taggedHeadDifferent :
        symbols.judgment sourceJudgmentName ≠ sourceJudgmentName := by
      decide
    exact taggedHeadDifferent headEquality

#print axioms mapped_bound_claim_is_exact_and_nontrivial
#print axioms open_binder_template_commutes
#print axioms translated_certificate_accepts
#print axioms translated_checker_commutes
#print axioms constructor_and_judgment_images_differ
#print axioms translated_certificate_rejects_wrong_claim
#print axioms target_only_meaning_has_no_source_preimage_at_same_claim

end Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthorityCanary
