import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedValidation

/-!
# Compositional validation of guarded source-indexed native types

Guarded introduction retains the exact authored variable and relation rows.
The finished constructor signature can therefore depend on proof-relevant
source occurrence evidence.  This module validates the generated calculus by
construction family rather than normalizing every finished rule against the
entire generated signature.

The object-language validator and the independent semantic interpretation are
separate obligations.  This file supplies only the ordinary V2 schema-
admission coordinate required between them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedValidation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedValidation

abbrev Target {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :=
  SelectedNativeTypeGuardedSourceIndexedCalculus.definition
    demand separated profile

def retainedCarrierNames {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List String :=
  SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
    additionalCarrierNames demand

/-! ## Target membership and lookup -/

theorem constructor_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (term : GrammarRule)
    (membership : term ∈ (Target demand separated profile).terms) :
    languageHasConstructorArity
      (Target demand separated profile).toLanguageDef
      term.label term.params.length = true := by
  unfold languageHasConstructorArity
  rw [LanguageDef.filter_terms_by_label_eq_singleton _ term
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ languageValid)
    membership]
  simp

private theorem universeTerm_mem_termsFor (names : List String)
    {carrier : String} (membership : carrier ∈ names)
    (code : CarrierUniverseSignature.Code) :
    CarrierUniverseSignature.rule code carrier ∈
      CarrierUniverseSignature.termsFor names := by
  rw [CarrierUniverseSignature.termsFor, List.mem_flatMap]
  refine ⟨carrier, membership, ?_⟩
  cases code <;> simp

private theorem claimTerm_mem_claimTermsFor (names : List String)
    {carrier : String} (carrierMembership : carrier ∈ names)
    {term : GrammarRule}
    (termMembership : term ∈ ContextualCarrierClaims.claimTerms carrier) :
    term ∈ ContextualCarrierClaims.claimTermsFor names := by
  rw [ContextualCarrierClaims.claimTermsFor, List.mem_flatMap]
  exact ⟨carrier, carrierMembership, termMembership⟩

theorem universeCodeTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand)
    (code : CarrierUniverseSignature.Code) :
    CarrierUniverseSignature.rule code carrier ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  rcases List.mem_append.mp membership with stable | additional
  · have grouped : CarrierUniverseSignature.rule code carrier ∈
        (ContextualModalExtension.language demand.foundation).terms := by
      rw [ContextualModalExtension.language_terms]
      apply List.mem_append_left
      rw [SelectedNativeTypeFoundation.definition_terms]
      exact universeTerm_mem_termsFor _ stable code
    have chronological : CarrierUniverseSignature.rule code carrier ∈
        (ContextualModalSignatureCompiler.definition demand.foundation).terms :=
      (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
        demand.foundation).terms.mem_iff.mpr grouped
    have signatureMembership : CarrierUniverseSignature.rule code carrier ∈
        (SelectedNativeTypeContextualCalculus.signature demand).terms := by
      unfold SelectedNativeTypeContextualCalculus.signature
      rw [ContextualCarrierClaims.apply_terms]
      exact List.mem_append_left _ chronological
    simp only [List.mem_append]
    aesop
  · have carrierMembership : CarrierUniverseSignature.rule code carrier ∈
        (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms := by
      rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_terms]
      exact List.mem_append_left _
        (universeTerm_mem_termsFor _ additional code)
    simp only [List.mem_append]
    aesop

theorem claimTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    {carrier : String} (carrierMembership : carrier ∈ retainedCarrierNames demand)
    {term : GrammarRule}
    (termMembership : term ∈ ContextualCarrierClaims.claimTerms carrier) :
    term ∈ (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  rcases List.mem_append.mp carrierMembership with stable | additional
  · have signatureMembership : term ∈
        (SelectedNativeTypeContextualCalculus.signature demand).terms := by
      unfold SelectedNativeTypeContextualCalculus.signature
      rw [ContextualCarrierClaims.apply_terms]
      apply List.mem_append_right
      apply List.mem_append_right
      exact claimTerm_mem_claimTermsFor _ stable termMembership
    simp only [List.mem_append]
    aesop
  · have extensionMembership : term ∈
        (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms := by
      rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_terms]
      apply List.mem_append_right
      exact claimTerm_mem_claimTermsFor _ additional termMembership
    simp only [List.mem_append]
    aesop

theorem typingJudgment_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand) :
    CarrierTypingLanguageDef.judgment carrier ∈
      (Target demand separated profile).judgments := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_judgments]
  rcases List.mem_append.mp membership with stable | additional
  · apply List.mem_append_left
    unfold SelectedNativeTypeContextualCalculus.signature
    rw [ContextualCarrierClaims.apply_judgments]
    apply List.mem_append_left
    have grouped : CarrierTypingLanguageDef.judgment carrier ∈
        (ContextualModalExtension.language demand.foundation).judgments := by
      rw [ContextualModalExtension.language_judgments,
        SelectedNativeTypeFoundation.definition_judgments]
      exact List.mem_map_of_mem stable
    rw [(ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      demand.foundation).judgments]
    exact grouped
  · apply List.mem_append_right
    rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_judgments]
    exact List.mem_map_of_mem additional

theorem typingJudgment_lookup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand) :
    (Target demand separated profile).lookupJudgment?
        (CarrierTypingLanguageDef.typingHead carrier) 2 =
      some (CarrierTypingLanguageDef.judgment carrier) := by
  exact CalculusLanguageDef.lookupJudgment?_eq_some_of_mem _ _ headsNodup
    (typingJudgment_mem demand separated profile membership)

theorem contextualJudgment_lookup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    (Target demand separated profile).lookupJudgment?
        ContextualInference.contextualJudgment.head 3 =
      some ContextualInference.contextualJudgment := by
  apply CalculusLanguageDef.lookupJudgment?_eq_some_of_mem _ _ headsNodup
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_judgments]
  apply List.mem_append_left
  simp [SelectedNativeTypeContextualCalculus.signature]

theorem emptyContextTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    ContextualInference.emptyContextTerm ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  simp [SelectedNativeTypeContextualCalculus.signature]

theorem extendContextTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    ContextualInference.extendContextTerm ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  simp [SelectedNativeTypeContextualCalculus.signature]

theorem familyApplicationTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) (slot : Occurrence demand) :
    familyApplicationTerm demand slot ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  simp [familyApplicationTerms]

theorem modalRuleAt_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) (slot : Occurrence demand) :
    ContextualModalExtension.modalRuleAt demand.foundation
        (SelectedNativeTypeSourceIndexedValidation.foundationSlot demand slot) ∈
      (Target demand separated profile).terms := by
  have grouped :
      ContextualModalExtension.modalRuleAt demand.foundation
          (SelectedNativeTypeSourceIndexedValidation.foundationSlot demand slot) ∈
        (ContextualModalExtension.language demand.foundation).terms := by
    rw [ContextualModalExtension.language_terms]
    apply List.mem_append_right
    exact List.mem_ofFn.mpr
      ⟨SelectedNativeTypeSourceIndexedValidation.foundationSlot demand slot, rfl⟩
  have chronological :
      ContextualModalExtension.modalRuleAt demand.foundation
          (SelectedNativeTypeSourceIndexedValidation.foundationSlot demand slot) ∈
        (ContextualModalSignatureCompiler.definition demand.foundation).terms :=
    (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      demand.foundation).terms.mem_iff.mpr grouped
  have signatureMembership :
      ContextualModalExtension.modalRuleAt demand.foundation
          (SelectedNativeTypeSourceIndexedValidation.foundationSlot demand slot) ∈
        (SelectedNativeTypeContextualCalculus.signature demand).terms := by
    simp only [SelectedNativeTypeContextualCalculus.signature,
      ContextualCarrierClaims.apply_terms, List.mem_append]
    exact Or.inl chronological
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  simp only [List.mem_append]
  aesop

theorem contextCodeTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    ContextualInferenceCanonicalContext.contextCodeTerm ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  simp [SelectedNativeTypeContextualCalculus.signature,
    ContextualInferenceCanonicalContext.extension]

theorem authoredVariableTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (binding : SelectedNativeTypeAuthoredVariableClaim.Binding demand slot) :
    SelectedNativeTypeAuthoredVariableClaim.termAt demand slot binding ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  have generatedMembership :
      SelectedNativeTypeAuthoredVariableClaim.termAt demand slot binding ∈
        SelectedNativeTypeAuthoredVariableClaim.terms demand :=
    List.mem_flatten.mpr
      ⟨SelectedNativeTypeAuthoredVariableClaim.termsAt demand slot,
        List.mem_ofFn.mpr ⟨slot, rfl⟩,
        List.mem_ofFn.mpr ⟨binding, rfl⟩⟩
  simp only [List.mem_append]
  aesop

theorem guardTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (premise : Fin
      (SelectedNativeTypeBoundRelationClaim.viewsAt profile slot).length) :
    SelectedNativeTypeBoundRelationClaim.termAt profile slot premise ∈
      (Target demand separated profile).terms := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_terms]
  have generatedMembership :
      SelectedNativeTypeBoundRelationClaim.termAt profile slot premise ∈
        SelectedNativeTypeBoundRelationClaim.terms profile :=
    List.mem_flatten.mpr
    ⟨SelectedNativeTypeBoundRelationClaim.termsAt profile slot,
      List.mem_ofFn.mpr ⟨slot, rfl⟩,
      List.mem_ofFn.mpr ⟨premise, rfl⟩⟩
  simp only [List.mem_append]
  aesop

/-! ## Constructor arities -/

theorem universeCode_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand)
    (code : CarrierUniverseSignature.Code) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (CarrierUniverseSignature.label code carrier) 0 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (CarrierUniverseSignature.rule code carrier)
    (universeCodeTerm_mem demand separated profile membership code)
  simpa [CarrierUniverseSignature.rule] using admitted

theorem variableClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (ContextualCarrierClaims.claimLabel .variable carrier) 1 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (ContextualCarrierClaims.variableClaimTerm carrier)
    (claimTerm_mem demand separated profile membership (by
      simp [ContextualCarrierClaims.claimTerms]))
  simpa [ContextualCarrierClaims.variableClaimTerm] using admitted

theorem typingClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (ContextualCarrierClaims.claimLabel .typing carrier) 2 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (ContextualCarrierClaims.typingClaimTerm carrier)
    (claimTerm_mem demand separated profile membership (by
      simp [ContextualCarrierClaims.claimTerms]))
  simpa [ContextualCarrierClaims.typingClaimTerm] using admitted

theorem emptyContext_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = []) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      ContextualInference.emptyContextTerm.label 0 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    ContextualInference.emptyContextTerm
    (emptyContextTerm_mem demand separated profile)
  simpa [ContextualInference.emptyContextTerm] using admitted

theorem extendContext_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = []) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      ContextualInference.extendContextTerm.label 2 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    ContextualInference.extendContextTerm
    (extendContextTerm_mem demand separated profile)
  simpa [ContextualInference.extendContextTerm] using admitted

theorem familyApplication_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (auxiliaryLabel .familyApplication slot.val)
      ((bindingsAt demand slot).length + 1) = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (familyApplicationTerm demand slot)
    (familyApplicationTerm_mem demand separated profile slot)
  simpa [familyApplicationTerm] using admitted

theorem modal_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (SelectedModalNaming.label slot.val)
      ((bindingsAt demand slot).length + 1) = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (ContextualModalExtension.modalRuleAt demand.foundation
      (SelectedNativeTypeSourceIndexedValidation.foundationSlot demand slot))
    (modalRuleAt_mem demand separated profile slot)
  simpa [ContextualModalExtension.modalRuleAt,
    ContextualModalSignature.modalRule,
    ContextualModalSignature.parameters,
    ContextualModalSignature.parametersFor,
    ContextualModalSignature.relyParametersFor,
    ContextualModalSignature.relyBindings,
    SelectedNativeTypeSourceIndexedValidation.foundationSlot_typing,
    bindingsAt, DisplayedContextProfile.bindings] using admitted

theorem contextCode_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = []) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      ContextualInferenceCanonicalContext.contextCodeTerm.label 1 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    ContextualInferenceCanonicalContext.contextCodeTerm
    (contextCodeTerm_mem demand separated profile)
  simpa [ContextualInferenceCanonicalContext.contextCodeTerm] using admitted

theorem authoredVariableClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand)
    (binding : SelectedNativeTypeAuthoredVariableClaim.Binding demand slot) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (SelectedNativeTypeAuthoredVariableClaim.Naming.label
        slot.val binding.val) 1 = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (SelectedNativeTypeAuthoredVariableClaim.termAt demand slot binding)
    (authoredVariableTerm_mem demand separated profile slot binding)
  simpa [SelectedNativeTypeAuthoredVariableClaim.termAt] using admitted

theorem guardClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand)
    (premise : Fin
      (SelectedNativeTypeBoundRelationClaim.viewsAt profile slot).length) :
    languageHasConstructorArity (Target demand separated profile).toLanguageDef
      (SelectedNativeTypeBoundRelationClaim.Naming.label slot.val premise.val)
      (SelectedNativeTypeBoundRelationClaim.authoredArguments
        profile slot premise).length = true := by
  have admitted := constructor_has_arity demand separated profile languageValid
    (SelectedNativeTypeBoundRelationClaim.termAt profile slot premise)
    (guardTerm_mem demand separated profile slot premise)
  simpa [SelectedNativeTypeBoundRelationClaim.termAt,
    SelectedNativeTypeBoundRelationClaim.authoredArguments,
    SelectedNativeTypeBoundRelationClaim.sourceView_argument_length_eq_types]
      using admitted

/-! ## Fixed-pattern admission -/

theorem sortCode_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand)
    (code : CarrierUniverseSignature.Code) :
    FixedPatternAdmission (Target demand separated profile).toLanguageDef
      (sortCode carrier code) := by
  apply FixedPatternAdmission.apply
  · simpa [sortCode] using
      universeCode_has_arity demand separated profile languageValid membership
        code
  · intro argument impossible
    simp at impossible

theorem modalType_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) (family : Pattern)
    (familyFixed : FixedPatternAdmission
      (Target demand separated profile).toLanguageDef family) :
    FixedPatternAdmission (Target demand separated profile).toLanguageDef
      (modalType demand slot family) := by
  apply FixedPatternAdmission.apply
  · simpa [modalType, relyTypes] using
      modal_has_arity demand separated profile languageValid slot
  · intro argument membership
    rw [List.mem_append] at membership
    rcases membership with rely | familyMember
    · rw [relyTypes, List.mem_ofFn] at rely
      obtain ⟨index, rfl⟩ := rely
      exact FixedPatternAdmission.fvar _ _
    · simp only [List.mem_singleton] at familyMember
      subst argument
      exact familyFixed

theorem authoredFamilyApplication_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) (family : Pattern)
    (familyFixed : FixedPatternAdmission
      (Target demand separated profile).toLanguageDef family) :
    FixedPatternAdmission (Target demand separated profile).toLanguageDef
      (authoredFamilyApplication demand slot family) := by
  apply FixedPatternAdmission.apply
  · simpa [authoredFamilyApplication, authoredRelyValues,
      ContextualFamilyApplication.applyFamily] using
        familyApplication_has_arity demand separated profile languageValid slot
  · intro argument membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | rely
    · exact familyFixed
    · rw [authoredRelyValues, List.mem_ofFn] at rely
      obtain ⟨index, rfl⟩ := rely
      exact FixedPatternAdmission.fvar _ _

theorem guardedAuthoredVariableClaims_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ formula ∈ guardedAuthoredVariableClaims demand slot,
      FixedPatternAdmission (Target demand separated profile).toLanguageDef
        formula := by
  intro formula membership
  rw [guardedAuthoredVariableClaims,
    SelectedNativeTypeAuthoredVariableClaim.authoredClaims,
    List.mem_ofFn] at membership
  obtain ⟨binding, rfl⟩ := membership
  apply FixedPatternAdmission.apply
  · exact authoredVariableClaim_has_arity demand separated profile
      languageValid slot binding
  · intro argument argumentMembership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at argumentMembership
    subst argument
    exact FixedPatternAdmission.fvar _ _

theorem authoredRelyVariableClaims_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ formula ∈ authoredRelyVariableClaims demand slot,
      FixedPatternAdmission (Target demand separated profile).toLanguageDef
        formula := by
  intro formula membership
  rw [authoredRelyVariableClaims, List.mem_ofFn] at membership
  obtain ⟨index, rfl⟩ := membership
  apply FixedPatternAdmission.variableClaim
  · exact variableClaim_has_arity demand separated profile languageValid
      (SelectedNativeTypeSourceIndexedValidation.relyBindingCarrier_mem
        demand slot (List.get_mem _ index))
  · exact FixedPatternAdmission.fvar _ _

theorem authoredRelyTypingClaims_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ formula ∈ authoredRelyTypingClaims demand slot,
      FixedPatternAdmission (Target demand separated profile).toLanguageDef
        formula := by
  intro formula membership
  rw [authoredRelyTypingClaims, List.mem_ofFn] at membership
  obtain ⟨index, rfl⟩ := membership
  apply FixedPatternAdmission.typingClaim
  · exact typingClaim_has_arity demand separated profile languageValid
      (SelectedNativeTypeSourceIndexedValidation.relyBindingCarrier_mem
        demand slot (List.get_mem _ index))
  · exact FixedPatternAdmission.fvar _ _
  · exact FixedPatternAdmission.fvar _ _

theorem relySortPremises_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ sequent ∈
        SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot,
      FixedSequentAdmission (Target demand separated profile) sequent := by
  intro sequent membership
  rw [SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
    List.mem_ofFn] at membership
  obtain ⟨index, rfl⟩ := membership
  let binding := (bindingsAt demand slot).get index
  let carrier := sourceCarrierAt demand binding.2
  have carrierMembership : carrier ∈ retainedCarrierNames demand :=
    SelectedNativeTypeSourceIndexedValidation.relyBindingCarrier_mem
      demand slot (List.get_mem _ index)
  refine
    { variableContext := FixedPatternAdmission.fvar _ _
      relationContext := FixedPatternAdmission.fvar _ _
      conclusion := ?_ }
  apply FixedPatternAdmission.typingClaim
  · exact typingClaim_has_arity demand separated profile languageValid
      carrierMembership
  · exact FixedPatternAdmission.fvar _ _
  · exact sortCode_fixed demand separated profile languageValid
      carrierMembership _

theorem authoredResultSortPremise_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    FixedSequentAdmission (Target demand separated profile)
      (authoredResultSortPremise demand slot) := by
  have carrierMembership :=
    SelectedNativeTypeSourceIndexedValidation.rewriteCarrier_mem demand slot
  have familyFixed := authoredFamilyApplication_fixed demand separated profile
    languageValid slot (.fvar "result-family")
      (FixedPatternAdmission.fvar _ _)
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated profile languageValid
    · exact authoredRelyVariableClaims_fixed demand separated profile
        languageValid slot
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated profile languageValid
    · exact authoredRelyTypingClaims_fixed demand separated profile
        languageValid slot
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated profile languageValid
        carrierMembership
    · exact familyFixed
    · exact sortCode_fixed demand separated profile languageValid
        carrierMembership _

structure TargetOccurrenceAdmission {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Prop where
  source : FixedPatternAdmission (Target demand separated profile).toLanguageDef
    (authoredSource demand slot)
  target : FixedPatternAdmission (Target demand separated profile).toLanguageDef
    (authoredTarget demand slot)
  focus : FixedPatternAdmission (Target demand separated profile).toLanguageDef
    (authoredFocus demand slot)

/-- One coherent target admission for the complete ordered authored guard
row.  The row may not be assembled from claims belonging to other occurrence
activations. -/
structure TargetGuardAdmission {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Prop where
  claim : ∀ premise : Fin
      (SelectedNativeTypeBoundRelationClaim.viewsAt profile slot).length,
    FixedPatternAdmission (Target demand separated profile).toLanguageDef
      (SelectedNativeTypeBoundRelationClaim.authoredClaim profile slot premise)

theorem authoredGuardClaims_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (admission : TargetGuardAdmission demand separated profile slot) :
    ∀ formula ∈ authoredGuardClaims profile slot,
      FixedPatternAdmission (Target demand separated profile).toLanguageDef
        formula := by
  intro formula membership
  unfold authoredGuardClaims
    SelectedNativeTypeBoundRelationClaim.authoredClaims at membership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp membership
  exact admission.claim premise

theorem emptyContext_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = []) :
    FixedPatternAdmission (Target demand separated profile).toLanguageDef
      (ContextualInference.encodeContext .empty) := by
  apply FixedPatternAdmission.apply
  · simpa [ContextualInference.encodeContext] using
      emptyContext_has_arity demand separated profile languageValid
  · intro argument impossible
    simp at impossible

theorem canonicalContextPremise_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (name : String) :
    FixedSequentAdmission (Target demand separated profile)
      (ContextualInferenceCanonicalContext.premise name) := by
  refine
    { variableContext := emptyContext_fixed demand separated profile languageValid
      relationContext := emptyContext_fixed demand separated profile languageValid
      conclusion := ?_ }
  apply FixedPatternAdmission.apply
  · simpa [ContextualInferenceCanonicalContext.claim] using
      contextCode_has_arity demand separated profile languageValid
  · intro argument membership
    simp only [List.mem_singleton] at membership
    subst argument
    exact FixedPatternAdmission.fvar _ _

theorem formationConclusion_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    FixedSequentAdmission (Target demand separated profile)
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
        demand slot).conclusion := by
  have carrierMembership :=
    SelectedNativeTypeSourceIndexedValidation.focusCarrier_mem demand slot
  refine
    { variableContext := FixedPatternAdmission.fvar _ _
      relationContext := FixedPatternAdmission.fvar _ _
      conclusion := ?_ }
  apply FixedPatternAdmission.typingClaim
  · exact typingClaim_has_arity demand separated profile languageValid
      carrierMembership
  · exact modalType_fixed demand separated profile languageValid slot
      (.fvar "result-family") (FixedPatternAdmission.fvar _ _)
  · exact sortCode_fixed demand separated profile languageValid
      carrierMembership _

theorem guardedIntroductionBody_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand)
    (target : TargetOccurrenceAdmission demand separated profile slot)
    (guard : TargetGuardAdmission demand separated profile slot) :
    FixedSequentAdmission (Target demand separated profile)
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionBodyPremise
        profile slot) := by
  have carrierMembership :=
    SelectedNativeTypeSourceIndexedValidation.rewriteCarrier_mem demand slot
  have familyFixed := authoredFamilyApplication_fixed demand separated profile
    languageValid slot (.fvar "result-family")
      (FixedPatternAdmission.fvar _ _)
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated profile languageValid
    · exact guardedAuthoredVariableClaims_fixed demand separated profile
        languageValid slot
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated profile languageValid
    · intro formula membership
      rw [List.mem_append] at membership
      rcases membership with guardMembership | relyMembership
      · exact authoredGuardClaims_fixed demand separated profile slot guard
          formula guardMembership
      · exact authoredRelyTypingClaims_fixed demand separated profile
          languageValid slot formula relyMembership
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated profile languageValid
        carrierMembership
    · exact target.target
    · exact familyFixed

theorem guardedIntroductionConclusion_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (slot : Occurrence demand)
    (target : TargetOccurrenceAdmission demand separated profile slot)
    (guard : TargetGuardAdmission demand separated profile slot) :
    FixedSequentAdmission (Target demand separated profile)
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
        profile slot) := by
  have carrierMembership :=
    SelectedNativeTypeSourceIndexedValidation.focusCarrier_mem demand slot
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated profile languageValid
    · exact guardedAuthoredVariableClaims_fixed demand separated profile
        languageValid slot
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated profile languageValid
    · exact authoredGuardClaims_fixed demand separated profile slot guard
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated profile languageValid
        carrierMembership
    · exact target.focus
    · exact modalType_fixed demand separated profile languageValid slot
        (.fvar "result-family") (FixedPatternAdmission.fvar _ _)

/-! ## Source-independent generated rule families -/

theorem universeAxiom_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand) :
    RuleSchema.isValidIn (Target demand separated profile)
      (CarrierTypingLanguageDef.universeAxiom carrier) = true := by
  unfold RuleSchema.isValidIn
  rw [CarrierTypingLanguageDef.universeAxiom_isValidV1]
  simp only [Bool.true_and, RuleSchema.patterns,
    CarrierTypingLanguageDef.universeAxiom, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true]
  simp only [CalculusLanguageDef.judgmentSchemaValid, List.length_cons,
    List.length_nil, Nat.reduceAdd]
  rw [typingJudgment_lookup demand separated profile headsNodup membership]
  simp only [Option.isSome_some, Bool.true_and, fixedConstructorListsValid,
    fixedConstructorsValid, List.length_nil, Bool.and_true]
  rw [Bool.and_eq_true]
  exact
    ⟨universeCode_has_arity demand separated profile languageValid membership
        .star,
      universeCode_has_arity demand separated profile languageValid membership
        .box⟩

theorem canonicalContextSequent_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (wire : Pattern)
    (wireFixed : FixedPatternAdmission
      (Target demand separated profile).toLanguageDef wire) :
    FixedSequentAdmission (Target demand separated profile)
      (ContextualInferenceCanonicalContext.sequent wire) := by
  refine
    { variableContext := emptyContext_fixed demand separated profile languageValid
      relationContext := emptyContext_fixed demand separated profile languageValid
      conclusion := ?_ }
  apply FixedPatternAdmission.apply
  · simpa [ContextualInferenceCanonicalContext.claim] using
      contextCode_has_arity demand separated profile languageValid
  · intro argument membership
    simp only [List.mem_singleton] at membership
    subst argument
    exact wireFixed

theorem liftTypingRule_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    {carrier : String} (membership : carrier ∈ retainedCarrierNames demand) :
    RuleSchema.isValidIn (Target demand separated profile)
      (ContextualCarrierClaims.liftTypingRule carrier) = true := by
  have contextualLookup :=
    contextualJudgment_lookup demand separated profile headsNodup
  have gammaValid := FixedSequentAdmission.judgmentSchemaValid _ _
    contextualLookup
    (canonicalContextSequent_fixed demand separated profile languageValid
      (.fvar "Gamma") (FixedPatternAdmission.fvar _ _))
  have deltaValid := FixedSequentAdmission.judgmentSchemaValid _ _
    contextualLookup
    (canonicalContextSequent_fixed demand separated profile languageValid
      (.fvar "Delta") (FixedPatternAdmission.fvar _ _))
  have typingValid :
      (Target demand separated profile).judgmentSchemaValid
        (.apply (CarrierTypingLanguageDef.typingHead carrier)
          [.fvar "term", .fvar "type"]) = true := by
    simp only [CalculusLanguageDef.judgmentSchemaValid, List.length_cons,
      List.length_nil, Nat.reduceAdd]
    rw [typingJudgment_lookup demand separated profile headsNodup membership]
    simp [fixedConstructorListsValid, fixedConstructorsValid]
  have claimFixed := FixedPatternAdmission.typingClaim
    (Target demand separated profile).toLanguageDef carrier
    (.fvar "term") (.fvar "type")
    (typingClaim_has_arity demand separated profile languageValid membership)
    (FixedPatternAdmission.fvar _ _)
    (FixedPatternAdmission.fvar _ _)
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _
    contextualLookup
    ({ variableContext := FixedPatternAdmission.fvar _ "Gamma"
       relationContext := FixedPatternAdmission.fvar _ "Delta"
       conclusion := claimFixed } :
      FixedSequentAdmission (Target demand separated profile)
        { variableContext := .hole "Gamma"
          relationContext := .hole "Delta"
          conclusion := ContextualCarrierClaims.typingClaim carrier
            (.fvar "term") (.fvar "type") })
  unfold RuleSchema.isValidIn
  rw [ContextualCarrierClaims.liftTypingRule_locallyValid]
  simp only [Bool.true_and]
  rw [ContextualCarrierClaims.liftTypingRule_patterns]
  simp only [List.all_cons, List.all_nil, Bool.and_true, typingValid,
    Bool.true_and, Bool.and_eq_true]
  constructor
  · constructor
    · simpa [ContextualInferenceCanonicalContext.premise] using gammaValid
    · constructor
      · simpa [ContextualInferenceCanonicalContext.premise] using deltaValid
      · simpa [ContextualInference.lowerSequent,
          ContextualInference.encodeContext] using conclusionValid
  · simp [ContextualCarrierClaims.liftTypingRule]

theorem universeAxioms_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (carriers : List String)
    (covered : ∀ carrier ∈ carriers, carrier ∈ retainedCarrierNames demand) :
    (carriers.map CarrierTypingLanguageDef.universeAxiom).all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  apply List.all_eq_true.mpr
  intro rule membership
  obtain ⟨carrier, carrierMembership, rfl⟩ := List.mem_map.mp membership
  exact universeAxiom_validIn demand separated profile languageValid headsNodup
    (covered carrier carrierMembership)

theorem bridgeRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (carriers : List String)
    (covered : ∀ carrier ∈ carriers, carrier ∈ retainedCarrierNames demand) :
    (ContextualCarrierClaims.bridgeRules carriers).all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  unfold ContextualCarrierClaims.bridgeRules
  apply List.all_eq_true.mpr
  intro rule membership
  obtain ⟨carrier, carrierMembership, rfl⟩ := List.mem_map.mp membership
  exact liftTypingRule_validIn demand separated profile languageValid headsNodup
    (covered carrier carrierMembership)

/-! ## Canonical-context certificate rules -/

private theorem nilRule_locallyValid :
    RuleSchema.isLocallyValid
      ContextualInferenceCanonicalContext.nilRule = true := by
  decide +kernel

private theorem consRule_locallyValid :
    RuleSchema.isLocallyValid
      ContextualInferenceCanonicalContext.consRule = true := by
  decide +kernel

theorem canonicalContextNil_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    RuleSchema.isValidIn (Target demand separated profile)
      ContextualInferenceCanonicalContext.nilRule = true := by
  have lookup := contextualJudgment_lookup demand separated profile headsNodup
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (canonicalContextSequent_fixed demand separated profile languageValid
      (ContextualInference.encodeContext .empty)
      (emptyContext_fixed demand separated profile languageValid))
  unfold RuleSchema.isValidIn
  rw [nilRule_locallyValid]
  simp [ContextualInferenceCanonicalContext.nilRule, RuleSchema.patterns,
    conclusionValid]

theorem canonicalContextCons_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    RuleSchema.isValidIn (Target demand separated profile)
      ContextualInferenceCanonicalContext.consRule = true := by
  have lookup := contextualJudgment_lookup demand separated profile headsNodup
  have premiseValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (canonicalContextPremise_fixed demand separated profile languageValid
      "tail")
  have extendedFixed : FixedPatternAdmission
      (Target demand separated profile).toLanguageDef
      (.apply ContextualInference.extendContextTerm.label
        [.fvar "formula", .fvar "tail"]) := by
    apply FixedPatternAdmission.apply
    · exact extendContext_has_arity demand separated profile languageValid
    · intro argument membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl <;>
        exact FixedPatternAdmission.fvar _ _
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (canonicalContextSequent_fixed demand separated profile languageValid _
      extendedFixed)
  unfold RuleSchema.isValidIn
  rw [consRule_locallyValid]
  simp [ContextualInferenceCanonicalContext.consRule, RuleSchema.patterns,
    premiseValid, conclusionValid]

theorem canonicalContextRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    ContextualInferenceCanonicalContext.extension.newRules.all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  simp [ContextualInferenceCanonicalContext.extension,
    canonicalContextNil_validIn demand separated profile languageValid
      headsNodup,
    canonicalContextCons_validIn demand separated profile languageValid
      headsNodup]

theorem signatureRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    (SelectedNativeTypeContextualCalculus.signature demand).rules.all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  rw [SelectedNativeTypeSourceIndexedValidation.signature_rules,
    List.all_append, Bool.and_eq_true]
  constructor
  · rw [List.all_append, Bool.and_eq_true]
    constructor
    · exact universeAxioms_validIn demand separated profile languageValid
        headsNodup _ (by
          intro carrier membership
          exact List.mem_append_left _ membership)
    · exact canonicalContextRules_validIn demand separated profile
        languageValid headsNodup
  · exact bridgeRules_validIn demand separated profile languageValid
      headsNodup _ (by
        intro carrier membership
        exact List.mem_append_left _ membership)

theorem carrierExtensionRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newRules.all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_rules,
    List.all_append, Bool.and_eq_true]
  constructor
  · exact universeAxioms_validIn demand separated profile languageValid
      headsNodup _ (by
        intro carrier membership
        exact List.mem_append_right _ membership)
  · exact bridgeRules_validIn demand separated profile languageValid
      headsNodup _ (by
        intro carrier membership
        exact List.mem_append_right _ membership)

/-! ## Guarded occurrence rule family -/

theorem formationRule_patterns {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    RuleSchema.patterns
        (lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
            demand slot)) =
      ambientContextPremises.map lowerSequent ++
        (SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent ++
          [ lowerSequent (authoredResultSortPremise demand slot)
          , lowerSequent
              (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
                demand slot).conclusion ] := by
  simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
    inferMetavariables,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
    SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore,
    lowerRule, RuleSchema.patterns, List.map_append, List.append_assoc]

theorem introductionRule_patterns {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : PremiseProfile demand) (slot : Occurrence demand) :
    RuleSchema.patterns
        (lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            profile slot)) =
      ambientContextPremises.map lowerSequent ++
        (SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent ++
          [ lowerSequent (authoredResultSortPremise demand slot)
          , lowerSequent
              (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionBodyPremise
                profile slot)
          , lowerSequent
              (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
                profile slot) ] := by
  simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule,
    inferMetavariables,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRuleCore,
    lowerRule, RuleSchema.patterns, List.map_append, List.append_assoc]

theorem ambientContextPremises_valid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup) :
    (ambientContextPremises.map lowerSequent).all
      (Target demand separated profile).judgmentSchemaValid = true := by
  have lookup := contextualJudgment_lookup demand separated profile headsNodup
  apply List.all_eq_true.mpr
  intro judgment membership
  obtain ⟨sequent, sequentMembership, rfl⟩ := List.mem_map.mp membership
  simp only [ambientContextPremises, List.mem_cons, List.not_mem_nil,
    or_false] at sequentMembership
  rcases sequentMembership with rfl | rfl
  · exact FixedSequentAdmission.judgmentSchemaValid _ _ lookup
      (canonicalContextPremise_fixed demand separated profile languageValid
        "Gamma")
  · exact FixedSequentAdmission.judgmentSchemaValid _ _ lookup
      (canonicalContextPremise_fixed demand separated profile languageValid
        "Delta")

theorem formationRule_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (slot : Occurrence demand)
    (occurrence : OccurrenceAdmission demand profile slot) :
    RuleSchema.isValidIn (Target demand separated profile)
      (lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot)) = true := by
  have lookup := contextualJudgment_lookup demand separated profile headsNodup
  have contextsValid := ambientContextPremises_valid demand separated profile
    languageValid headsNodup
  have relyValid :
      ((SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent).all
        (Target demand separated profile).judgmentSchemaValid = true := by
    apply List.all_eq_true.mpr
    intro judgment membership
    obtain ⟨sequent, sequentMembership, rfl⟩ := List.mem_map.mp membership
    exact FixedSequentAdmission.judgmentSchemaValid _ _ lookup
      (relySortPremises_fixed demand separated profile languageValid slot
        sequent sequentMembership)
  have resultValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (authoredResultSortPremise_fixed demand separated profile languageValid
      slot)
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (formationConclusion_fixed demand separated profile languageValid slot)
  unfold RuleSchema.isValidIn
  rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule_locallyValid
    demand slot occurrence.formation]
  simp only [Bool.true_and]
  rw [formationRule_patterns]
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    contextsValid, relyValid, resultValid, conclusionValid, Bool.true_and]
  rfl

theorem introductionRule_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (slot : Occurrence demand)
    (occurrence : OccurrenceAdmission demand profile slot)
    (target : TargetOccurrenceAdmission demand separated profile slot)
    (guard : TargetGuardAdmission demand separated profile slot) :
    RuleSchema.isValidIn (Target demand separated profile)
      (lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          profile slot)) = true := by
  have lookup := contextualJudgment_lookup demand separated profile headsNodup
  have contextsValid := ambientContextPremises_valid demand separated profile
    languageValid headsNodup
  have relyValid :
      ((SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent).all
        (Target demand separated profile).judgmentSchemaValid = true := by
    apply List.all_eq_true.mpr
    intro judgment membership
    obtain ⟨sequent, sequentMembership, rfl⟩ := List.mem_map.mp membership
    exact FixedSequentAdmission.judgmentSchemaValid _ _ lookup
      (relySortPremises_fixed demand separated profile languageValid slot
        sequent sequentMembership)
  have resultValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (authoredResultSortPremise_fixed demand separated profile languageValid
      slot)
  have bodyValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (guardedIntroductionBody_fixed demand separated profile languageValid slot
      target guard)
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (guardedIntroductionConclusion_fixed demand separated profile languageValid
      slot target guard)
  unfold RuleSchema.isValidIn
  rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule_locallyValid
    profile slot occurrence.introduction]
  simp only [Bool.true_and]
  rw [introductionRule_patterns]
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    contextsValid, relyValid, resultValid, bodyValid, conclusionValid,
    Bool.true_and]
  rfl

theorem rulesAt_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (slot : Occurrence demand)
    (occurrence : OccurrenceAdmission demand profile slot)
    (target : TargetOccurrenceAdmission demand separated profile slot)
    (guard : TargetGuardAdmission demand separated profile slot) :
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt
      demand profile slot).all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt,
    formationRule_validIn demand separated profile languageValid headsNodup
      slot occurrence,
    introductionRule_validIn demand separated profile languageValid headsNodup
      slot occurrence target guard]

theorem profiledRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (occurrence : ∀ slot, OccurrenceAdmission demand profile slot)
    (target : ∀ slot, TargetOccurrenceAdmission demand separated profile slot)
    (guard : ∀ slot, TargetGuardAdmission demand separated profile slot) :
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules
      demand profile).all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules,
    List.all_flatten]
  apply List.all_eq_true.mpr
  intro row membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp membership
  exact rulesAt_validIn demand separated profile languageValid headsNodup slot
    (occurrence slot) (target slot) (guard slot)

/-! ## Whole flat calculus -/

theorem rules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (occurrence : ∀ slot, OccurrenceAdmission demand profile slot)
    (target : ∀ slot, TargetOccurrenceAdmission demand separated profile slot)
    (guard : ∀ slot, TargetGuardAdmission demand separated profile slot) :
    (Target demand separated profile).rules.all
      (RuleSchema.isValidIn (Target demand separated profile)) = true := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_rules,
    List.all_append, List.all_append]
  simp only [Bool.and_eq_true]
  exact
    ⟨⟨signatureRules_validIn demand separated profile languageValid headsNodup,
        carrierExtensionRules_validIn demand separated profile languageValid
          headsNodup⟩,
      profiledRules_validIn demand separated profile languageValid headsNodup
        occurrence target guard⟩

theorem definition_isValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    (languageValid :
      (Target demand separated profile).toLanguageDef.validate = [])
    (headsNodup :
      ((Target demand separated profile).judgments.map JudgmentDecl.head).Nodup)
    (ruleIdsNodup : (Target demand separated profile).ruleIds.Nodup)
    (judgmentValid :
      (Target demand separated profile).judgmentSignatureValid = true)
    (conversionValid :
      (Target demand separated profile).conversionDeclarationValid = true)
    (occurrence : ∀ slot, OccurrenceAdmission demand profile slot)
    (target : ∀ slot, TargetOccurrenceAdmission demand separated profile slot)
    (guard : ∀ slot, TargetGuardAdmission demand separated profile slot) :
    (Target demand separated profile).isValid = true := by
  have allValid := rules_validIn demand separated profile languageValid
    headsNodup occurrence target guard
  have localRules :
      (Target demand separated profile).rules.all
        RuleSchema.isLocallyValid = true := by
    apply List.all_eq_true.mpr
    intro rule membership
    have valid := List.all_eq_true.mp allValid rule membership
    unfold RuleSchema.isValidIn at valid
    rw [Bool.and_eq_true] at valid
    exact valid.1
  have ruleIdsValid :
      (((Target demand separated profile).ruleIds.eraseDups.length ==
        (Target demand separated profile).ruleIds.length) = true) :=
    (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr
      ruleIdsNodup
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [languageValid, localRules, ruleIdsValid, judgmentValid, allValid,
    conversionValid]
  rfl

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedValidation
