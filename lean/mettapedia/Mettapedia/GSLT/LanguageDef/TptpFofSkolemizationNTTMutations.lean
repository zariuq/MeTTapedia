import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNTT

/-!
# Load-bearing mutations for the FOF Skolemization NTT

These controls mutate an authored operational row while preserving a valid
source presentation.  The generated source-indexed rules must follow that
changed right-hand side.  Removing the row must leave its request inert; no
generated layer or unrelated source rule may replace the missing behavior.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNTTMutations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef

namespace Original

abbrev source :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand.source

abbrev rootTyping :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand.rootTyping

abbrev rootTyping_grounded :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand.rootTyping_grounded

end Original

/-- A same-carrier semantic mutation: the `matrix-verum` request now returns
the Skolem `falsum` constructor. -/
def mutatedMatrixVerum : RewriteRule :=
  mkRule "tptp-fof-skolemize:matrix-verum"
    [("environment", "TptpFofSkolemTerm:Env")] []
    (matrixRequest (v "environment")
      TptpFofPrenexLanguageDef.matrixVerum)
    (matrixResult (v "environment")
      TptpFofPrenexLanguageDef.matrixVerum TptpFofSkolemLanguageDef.falsum)

def mutatedMatrixRewrites : List RewriteRule :=
  mutatedMatrixVerum :: matrixRewrites.drop 1

def mutatedLanguage : LanguageDef :=
  { language with
    name := "TptpFofSkolemizationMutation"
    rewrites :=
      TptpFofSkolemTermLanguageDef.rewrites ++
        mutatedMatrixRewrites ++ formRewrites }

private theorem mutated_validateRewrite_eq_original (rewrite : RewriteRule) :
    mutatedLanguage.validateRewrite rewrite =
      language.validateRewrite rewrite := by
  rfl

@[simp] private theorem mutatedLanguage_typeNames :
    mutatedLanguage.typeNames = language.typeNames := by
  rfl

@[simp] private theorem mutatedLanguage_constructorSignatures :
    RewriteValidationCertificate.constructorSignatures mutatedLanguage =
      RewriteValidationCertificate.constructorSignatures language := by
  rfl

@[simp] private theorem mutatedLanguage_constructorLabels :
    RewriteValidationCertificate.constructorLabels mutatedLanguage =
      RewriteValidationCertificate.constructorLabels language := by
  rfl

private theorem mutatedLanguage_constructorLabels_nodup :
    (mutatedLanguage.terms.map (·.label)).Nodup := by
  change (language.terms.map (·.label)).Nodup
  decide +kernel

local macro "certify_mutated_skolemization_row" : tactic =>
  `(tactic|
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      mutatedMatrixRewrites, mutatedMatrixVerum,
      rewrites, matrixRewrites, formRewrites,
      TptpFofSkolemTermLanguageDef.rewrites, language_typeNames,
      language_constructorSignatures, language_constructorLabels,
      TptpFofSkolemTermLanguageDef.language_typeNames,
      TptpFofSkolemTermLanguageDef.language_constructorSignatures,
      TptpFofSkolemTermLanguageDef.language_constructorLabels,
      TptpFofSkolemTermLanguageDef.a,
      TptpFofSkolemTermLanguageDef.v,
      TptpFofSkolemTermLanguageDef.typed,
      TptpFofSkolemTermLanguageDef.mkRule,
      TptpFofSkolemTermLanguageDef.congruence,
      TptpFofSkolemTermLanguageDef.indexZero,
      TptpFofSkolemTermLanguageDef.indexSucc,
      TptpFofSkolemTermLanguageDef.sourceTermVariable,
      TptpFofSkolemTermLanguageDef.sourceTermFunction,
      TptpFofSkolemTermLanguageDef.sourceTermsNil,
      TptpFofSkolemTermLanguageDef.sourceTermsCons,
      TptpFofSkolemTermLanguageDef.targetTermVariable,
      TptpFofSkolemTermLanguageDef.targetTermOriginal,
      TptpFofSkolemTermLanguageDef.targetTermGenerated,
      TptpFofSkolemTermLanguageDef.targetTermsNil,
      TptpFofSkolemTermLanguageDef.targetTermsCons,
      TptpFofSkolemTermLanguageDef.envNil,
      TptpFofSkolemTermLanguageDef.envCons,
      TptpFofSkolemTermLanguageDef.termShiftRequest,
      TptpFofSkolemTermLanguageDef.termShiftResult,
      TptpFofSkolemTermLanguageDef.termsShiftRequest,
      TptpFofSkolemTermLanguageDef.termsShiftResult,
      TptpFofSkolemTermLanguageDef.envShiftRequest,
      TptpFofSkolemTermLanguageDef.envShiftResult,
      TptpFofSkolemTermLanguageDef.variablesRequest,
      TptpFofSkolemTermLanguageDef.variablesResult,
      TptpFofSkolemTermLanguageDef.lookupRequest,
      TptpFofSkolemTermLanguageDef.lookupResult,
      TptpFofSkolemTermLanguageDef.translateTermRequest,
      TptpFofSkolemTermLanguageDef.translateTermResult,
      TptpFofSkolemTermLanguageDef.translateTermsRequest,
      TptpFofSkolemTermLanguageDef.translateTermsResult,
      TptpFofPrenexLanguageDef.a, TptpFofSkolemLanguageDef.a,
      typed, mkRule, congruence, matrixRequest, matrixResult, formRequest,
      formResult, a, v,
      TptpFofPrenexLanguageDef.matrixVerum,
      TptpFofPrenexLanguageDef.matrixFalsum,
      TptpFofPrenexLanguageDef.matrixPositive,
      TptpFofPrenexLanguageDef.matrixNegative,
      TptpFofPrenexLanguageDef.matrixEqual,
      TptpFofPrenexLanguageDef.matrixNotEqual,
      TptpFofPrenexLanguageDef.matrixAnd,
      TptpFofPrenexLanguageDef.matrixOr,
      TptpFofPrenexLanguageDef.matrix,
      TptpFofPrenexLanguageDef.all, TptpFofPrenexLanguageDef.ex,
      TptpFofSkolemLanguageDef.verum, TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and, TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
      TptpFofSkolemLanguageDef.introducedSymbol,
      TptpFofSkolemLanguageDef.introducedNil,
      TptpFofSkolemLanguageDef.introducedCons,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead])

private theorem mutatedMatrixVerum_valid :
    mutatedLanguage.validateRewrite mutatedMatrixVerum = [] := by
  apply RewriteValidationCertificate.validateRewrite_eq_nil_of_check
  · exact mutatedLanguage_constructorLabels_nodup
  · certify_mutated_skolemization_row

private theorem every_mutated_rewrite_valid (rewrite : RewriteRule)
    (membership : rewrite ∈ mutatedLanguage.rewrites) :
    mutatedLanguage.validateRewrite rewrite = [] := by
  change rewrite ∈
    TptpFofSkolemTermLanguageDef.rewrites ++
      mutatedMatrixRewrites ++ formRewrites at membership
  rcases List.mem_append.mp membership with inheritedOrMutated | form
  · rcases List.mem_append.mp inheritedOrMutated with inherited | mutated
    · rw [mutated_validateRewrite_eq_original]
      apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
        language language_validate
      rw [language_rewrites]
      exact List.mem_append_left _ inherited
    · simp only [mutatedMatrixRewrites, List.mem_cons] at mutated
      rcases mutated with rfl | tail
      · exact mutatedMatrixVerum_valid
      · rw [mutated_validateRewrite_eq_original]
        apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
          language language_validate
        rw [language_rewrites, rewrites]
        exact List.mem_append_right _
          (List.mem_append_left _ (List.mem_of_mem_drop tail))
  · rw [mutated_validateRewrite_eq_original]
    apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
      language language_validate
    rw [language_rewrites, rewrites]
    exact List.mem_append_right _ (List.mem_append_right _ form)

set_option maxHeartbeats 1600000 in
theorem mutatedLanguage_validate : mutatedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  exact every_mutated_rewrite_valid

def mutatedSource : ValidatedLanguageDef :=
  ⟨mutatedLanguage, mutatedLanguage_validate⟩

/-- Deleting the same row preserves a structurally valid, deliberately
incomplete source presentation. -/
def deletedLanguage : LanguageDef :=
  { language with
    name := "TptpFofSkolemizationDeletion"
    rewrites :=
      TptpFofSkolemTermLanguageDef.rewrites ++
        matrixRewrites.drop 1 ++ formRewrites }

private theorem deleted_validateRewrite_eq_original (rewrite : RewriteRule) :
    deletedLanguage.validateRewrite rewrite =
      language.validateRewrite rewrite := by
  rfl

private theorem every_deleted_rewrite_valid (rewrite : RewriteRule)
    (membership : rewrite ∈ deletedLanguage.rewrites) :
    deletedLanguage.validateRewrite rewrite = [] := by
  change rewrite ∈
    TptpFofSkolemTermLanguageDef.rewrites ++
      matrixRewrites.drop 1 ++ formRewrites at membership
  rw [deleted_validateRewrite_eq_original]
  apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
    language language_validate
  rw [language_rewrites, rewrites]
  rcases List.mem_append.mp membership with inheritedOrMatrix | form
  · rcases List.mem_append.mp inheritedOrMatrix with inherited | matrix
    · exact List.mem_append_left _ inherited
    · exact List.mem_append_right _
        (List.mem_append_left _ (List.mem_of_mem_drop matrix))
  · exact List.mem_append_right _ (List.mem_append_right _ form)

set_option maxHeartbeats 1600000 in
theorem deletedLanguage_validate : deletedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  exact every_deleted_rewrite_valid

/-- Presentation-only control: changing the source language label leaves all
declarations and operational rows untouched. -/
def presentationRenamedLanguage : LanguageDef :=
  { language with name := "TptpFofSkolemizationPresentationRename" }

private theorem presentationRenamed_validateRewrite_eq_original
    (rewrite : RewriteRule) :
    presentationRenamedLanguage.validateRewrite rewrite =
      language.validateRewrite rewrite := by
  rfl

theorem presentationRenamedLanguage_validate :
    presentationRenamedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide +kernel
  intro rewrite membership
  rw [presentationRenamed_validateRewrite_eq_original]
  apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
    language language_validate
  exact membership

def presentationRenamedSource : ValidatedLanguageDef :=
  ⟨presentationRenamedLanguage, presentationRenamedLanguage_validate⟩

def groundVerumRequest : Pattern :=
  matrixRequest TptpFofSkolemTermLanguageDef.envNil
    TptpFofPrenexLanguageDef.matrixVerum

def originalVerumResult : Pattern :=
  matrixResult TptpFofSkolemTermLanguageDef.envNil
    TptpFofPrenexLanguageDef.matrixVerum TptpFofSkolemLanguageDef.verum

def mutatedVerumResult : Pattern :=
  matrixResult TptpFofSkolemTermLanguageDef.envNil
    TptpFofPrenexLanguageDef.matrixVerum TptpFofSkolemLanguageDef.falsum

/-- The baseline source gives the independently authored result. -/
theorem original_verum_step :
    rewriteStepNoPremises language groundVerumRequest =
      [originalVerumResult] := by
  decide +kernel

/-- A valid semantic body mutation changes operational behavior. -/
theorem semantic_mutation_moves_step :
    rewriteStepNoPremises mutatedLanguage groundVerumRequest =
      [mutatedVerumResult] := by
  decide +kernel

/-- Row deletion fails closed instead of finding a fallback implementation. -/
theorem deleted_row_has_no_step :
    rewriteStepNoPremises deletedLanguage groundVerumRequest = [] := by
  decide +kernel

/-- Changing only the source presentation label leaves its transition
relation unchanged. -/
theorem presentation_rename_preserves_step :
    rewriteStepNoPremises presentationRenamedLanguage groundVerumRequest =
      [originalVerumResult] := by
  decide +kernel

private abbrev originalIndex : Fin Original.source.language.rewrites.length :=
  ⟨15, by decide⟩

private abbrev mutatedIndex : Fin mutatedSource.language.rewrites.length :=
  ⟨15, by decide⟩

private abbrev presentationRenamedIndex :
    Fin presentationRenamedSource.language.rewrites.length :=
  ⟨15, by decide⟩

private def mutatedRootType : TypeExpr :=
  .base "TptpFofSkolemize:MatrixResult"

private theorem mutatedRootLeftTyped :
    HasType mutatedSource.language
      (FreeTypeContext.ofList
        (mutatedSource.language.rewrites.get mutatedIndex).typeContext) []
      (mutatedSource.language.rewrites.get mutatedIndex).left
      mutatedRootType := by
  apply checkHasType_sound
  decide +kernel

private theorem mutatedRootRightTyped :
    HasType mutatedSource.language
      (FreeTypeContext.ofList
        (mutatedSource.language.rewrites.get mutatedIndex).typeContext) []
      (mutatedSource.language.rewrites.get mutatedIndex).right
      mutatedRootType := by
  apply checkHasType_sound
  decide +kernel

private theorem mutatedRootSourceIsObject :
    isObjectPattern
      (mutatedSource.language.rewrites.get mutatedIndex).left = true := by
  decide +kernel

private def mutatedRootTyping : DisplayedRewriteTyping mutatedSource where
  site := DisplayedRewriteSite.root mutatedSource.language mutatedIndex
  rewriteType := mutatedRootType
  focusBoundPrefix := []
  focusType := mutatedRootType
  rewriteLeftTyped := mutatedRootLeftTyped
  rewriteRightTyped := mutatedRootRightTyped
  sourceIsObject := mutatedRootSourceIsObject
  focusTyped := mutatedRootLeftTyped

private theorem presentationRenamedRootLeftTyped :
    HasType presentationRenamedSource.language
      (FreeTypeContext.ofList
        (presentationRenamedSource.language.rewrites.get
          presentationRenamedIndex).typeContext) []
      (presentationRenamedSource.language.rewrites.get
        presentationRenamedIndex).left
      mutatedRootType := by
  apply checkHasType_sound
  decide +kernel

private theorem presentationRenamedRootRightTyped :
    HasType presentationRenamedSource.language
      (FreeTypeContext.ofList
        (presentationRenamedSource.language.rewrites.get
          presentationRenamedIndex).typeContext) []
      (presentationRenamedSource.language.rewrites.get
        presentationRenamedIndex).right
      mutatedRootType := by
  apply checkHasType_sound
  decide +kernel

private theorem presentationRenamedRootSourceIsObject :
    isObjectPattern
      (presentationRenamedSource.language.rewrites.get
        presentationRenamedIndex).left = true := by
  decide +kernel

private def presentationRenamedRootTyping :
    DisplayedRewriteTyping presentationRenamedSource where
  site := DisplayedRewriteSite.root presentationRenamedSource.language
    presentationRenamedIndex
  rewriteType := mutatedRootType
  focusBoundPrefix := []
  focusType := mutatedRootType
  rewriteLeftTyped := presentationRenamedRootLeftTyped
  rewriteRightTyped := presentationRenamedRootRightTyped
  sourceIsObject := presentationRenamedRootSourceIsObject
  focusTyped := presentationRenamedRootLeftTyped

private theorem mutatedRootTyping_grounded :
    SelectedNativeTypeFoundation.CarrierGrounded mutatedRootTyping := by
  intro object objectMembership name nameMembership
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots,
    DisplayedContextProfile.carrierTypes,
    DisplayedContextProfile.bindings,
    DisplayedContextProfile.variableNames,
    DisplayedContextProfile.externalFreeFvarNames,
    mutatedRootTyping, mutatedRootType,
    DisplayedRewriteSite.root] at objectMembership
  rcases objectMembership with rfl | rfl
  all_goals
    simp [TypeExpr.baseNames] at nameMembership
    subst name
    decide

private theorem presentationRenamedRootTyping_grounded :
    SelectedNativeTypeFoundation.CarrierGrounded
      presentationRenamedRootTyping := by
  intro object objectMembership name nameMembership
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots,
    DisplayedContextProfile.carrierTypes,
    DisplayedContextProfile.bindings,
    DisplayedContextProfile.variableNames,
    DisplayedContextProfile.externalFreeFvarNames,
    presentationRenamedRootTyping, mutatedRootType,
    DisplayedRewriteSite.root] at objectMembership
  rcases objectMembership with rfl | rfl
  all_goals
    simp [TypeExpr.baseNames] at nameMembership
    subst name
    decide

private def originalDemand : SelectedNativeTypeDemand Original.source :=
  ⟨[ProfiledRewriteOccurrence.constant
    (Original.rootTyping originalIndex)
    (Original.rootTyping_grounded originalIndex) .star]⟩

private def mutatedDemand : SelectedNativeTypeDemand mutatedSource :=
  ⟨[ProfiledRewriteOccurrence.constant mutatedRootTyping
    mutatedRootTyping_grounded .star]⟩

private def presentationRenamedDemand :
    SelectedNativeTypeDemand presentationRenamedSource :=
  ⟨[ProfiledRewriteOccurrence.constant presentationRenamedRootTyping
    presentationRenamedRootTyping_grounded .star]⟩

private abbrev originalSlot :
    SelectedNativeTypeContextualCalculus.Occurrence originalDemand :=
  ⟨0, by simp [originalDemand]⟩

private abbrev mutatedSlot :
    SelectedNativeTypeContextualCalculus.Occurrence mutatedDemand :=
  ⟨0, by simp [mutatedDemand]⟩

private abbrev presentationRenamedSlot :
    SelectedNativeTypeContextualCalculus.Occurrence
      presentationRenamedDemand :=
  ⟨0, by simp [presentationRenamedDemand]⟩

private theorem original_typing_right_exact :
    (SelectedNativeTypeContextualCalculus.typingAt
      originalDemand originalSlot).site.rewrite.right =
      matrixResult (.fvar "environment")
        TptpFofPrenexLanguageDef.matrixVerum
        TptpFofSkolemLanguageDef.verum := by
  rfl

private theorem mutated_typing_right_exact :
    (SelectedNativeTypeContextualCalculus.typingAt
      mutatedDemand mutatedSlot).site.rewrite.right =
      matrixResult (.fvar "environment")
        TptpFofPrenexLanguageDef.matrixVerum
        TptpFofSkolemLanguageDef.falsum := by
  rfl

private theorem original_typing_left_exact :
    (SelectedNativeTypeContextualCalculus.typingAt
      originalDemand originalSlot).site.rewrite.left =
      matrixRequest (.fvar "environment")
        TptpFofPrenexLanguageDef.matrixVerum := by
  rfl

private theorem mutated_typing_left_exact :
    (SelectedNativeTypeContextualCalculus.typingAt
      mutatedDemand mutatedSlot).site.rewrite.left =
      matrixRequest (.fvar "environment")
        TptpFofPrenexLanguageDef.matrixVerum := by
  rfl

private theorem original_endpointVariableNames_exact :
    endpointVariableNames originalDemand originalSlot = ["environment"] := by
  unfold endpointVariableNames
  rw [original_typing_left_exact, original_typing_right_exact]
  simp [matrixRequest, matrixResult, a,
    TptpFofPrenexLanguageDef.matrixVerum,
    TptpFofPrenexLanguageDef.a,
    TptpFofSkolemLanguageDef.verum,
    TptpFofSkolemLanguageDef.a, Pattern.freeFvarNames,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

private theorem mutated_endpointVariableNames_exact :
    endpointVariableNames mutatedDemand mutatedSlot = ["environment"] := by
  unfold endpointVariableNames
  rw [mutated_typing_left_exact, mutated_typing_right_exact]
  simp [matrixRequest, matrixResult, a,
    TptpFofPrenexLanguageDef.matrixVerum,
    TptpFofPrenexLanguageDef.a,
    TptpFofSkolemLanguageDef.falsum,
    TptpFofSkolemLanguageDef.a, Pattern.freeFvarNames,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

private theorem original_authoredTarget_exact :
    authoredTarget originalDemand originalSlot =
      matrixResult (.fvar (authoredVariableName 0 0))
        TptpFofPrenexLanguageDef.matrixVerum
        TptpFofSkolemLanguageDef.verum := by
  unfold authoredTarget authoredPattern
  rw [original_typing_right_exact]
  simp only [matrixResult, a, Pattern.renameFVars, List.map_cons,
    List.map_nil]
  unfold renameVariable
  rw [original_endpointVariableNames_exact]
  simp [TptpFofPrenexLanguageDef.matrixVerum,
    TptpFofPrenexLanguageDef.a,
    TptpFofSkolemLanguageDef.verum,
    TptpFofSkolemLanguageDef.a, Pattern.renameFVars]

private theorem mutated_authoredTarget_exact :
    authoredTarget mutatedDemand mutatedSlot =
      matrixResult (.fvar (authoredVariableName 0 0))
        TptpFofPrenexLanguageDef.matrixVerum
        TptpFofSkolemLanguageDef.falsum := by
  unfold authoredTarget authoredPattern
  rw [mutated_typing_right_exact]
  simp only [matrixResult, a, Pattern.renameFVars, List.map_cons,
    List.map_nil]
  unfold renameVariable
  rw [mutated_endpointVariableNames_exact]
  simp [TptpFofPrenexLanguageDef.matrixVerum,
    TptpFofPrenexLanguageDef.a,
    TptpFofSkolemLanguageDef.falsum,
    TptpFofSkolemLanguageDef.a, Pattern.renameFVars]

private theorem authoredTargets_ne :
    authoredTarget originalDemand originalSlot ≠
      authoredTarget mutatedDemand mutatedSlot := by
  rw [original_authoredTarget_exact, mutated_authoredTarget_exact]
  decide +kernel

private def typingClaimSubject? : Pattern → Option Pattern
  | .apply _ (subject :: _) => some subject
  | _ => none

/-- The source-indexed generator observes the valid authored body mutation.
This distinguishes generation from a validator followed by a hard-coded
canonical rule table. -/
theorem semantic_mutation_moves_generated_introduction :
    introductionRule originalDemand originalSlot ≠
      introductionRule mutatedDemand mutatedSlot := by
  intro equality
  have targets := congrArg
    (fun rule : ContextualInference.Rule =>
      rule.premises.getLast?.bind fun premise =>
        typingClaimSubject? premise.conclusion) equality
  have targetEquality :
      authoredTarget originalDemand originalSlot =
        authoredTarget mutatedDemand mutatedSlot := by
    simpa [introductionRule, introductionRuleCore,
      introductionBodyPremise, typingClaimSubject?,
      ContextualCarrierClaims.typingClaim] using targets
  exact authoredTargets_ne targetEquality

/-- A presentation-only source-language rename does not perturb the generated
source-indexed rule. -/
theorem presentation_rename_preserves_generated_introduction :
    introductionRule originalDemand originalSlot =
      introductionRule presentationRenamedDemand
        presentationRenamedSlot := by
  rfl

#print axioms mutatedLanguage_validate
#print axioms deletedLanguage_validate
#print axioms presentationRenamedLanguage_validate
#print axioms original_verum_step
#print axioms semantic_mutation_moves_step
#print axioms deleted_row_has_no_step
#print axioms presentation_rename_preserves_step
#print axioms semantic_mutation_moves_generated_introduction
#print axioms presentation_rename_preserves_generated_introduction

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNTTMutations
