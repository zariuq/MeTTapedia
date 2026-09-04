import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus

/-!
# Compositional validation of source-indexed selected native types

The source-indexed generator emits rules that mention both literal authored
constructors and generated carrier, context, claim, modal, and family
constructors.  Re-running the complete Boolean checker on every finished rule
repeats the same constructor lookup many times.  This module instead exposes
the reusable signature facts once and composes fixed-constructor validity from
the rule constructors.

The result is a generator-family boundary: concrete clients prove language
validation, judgment-head uniqueness, authored-pattern validity, and the
selected occurrence admission.  Formation and introduction then validate for
every selected occurrence without enumerating emitted rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedValidation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus

/-! ## Definition-independent fixed-pattern algebra -/

/-- Proof-relevant admission of every fixed constructor in one pattern against
one concrete target signature. -/
structure FixedPatternAdmission (language : LanguageDef)
    (pattern : Pattern) : Prop where
  valid : fixedConstructorsValid language pattern = true

protected theorem FixedPatternAdmission.fvar (language : LanguageDef)
    (name : String) : FixedPatternAdmission language (.fvar name) := by
  exact ⟨by simp [fixedConstructorsValid]⟩

private theorem fixedConstructorListsValid_of_forall
    (language : LanguageDef) :
    (patterns : List Pattern) →
      (∀ pattern ∈ patterns,
        fixedConstructorsValid language pattern = true) →
      fixedConstructorListsValid language patterns = true
  | [], _ => by simp [fixedConstructorListsValid]
  | pattern :: patterns, valid => by
      simp only [fixedConstructorListsValid, Bool.and_eq_true]
      exact
        ⟨valid pattern (by simp),
          fixedConstructorListsValid_of_forall language patterns (by
            intro tail tailMembership
            exact valid tail (by simp [tailMembership]))⟩

protected theorem FixedPatternAdmission.apply
    (language : LanguageDef) (head : String) (arguments : List Pattern)
    (headValid :
      languageHasConstructorArity language head arguments.length = true)
    (argumentsValid :
      ∀ argument ∈ arguments, FixedPatternAdmission language argument) :
    FixedPatternAdmission language (.apply head arguments) := by
  refine ⟨?_⟩
  simp only [fixedConstructorsValid, Bool.and_eq_true]
  exact
    ⟨headValid,
      fixedConstructorListsValid_of_forall language arguments fun argument
        membership => (argumentsValid argument membership).valid⟩

protected theorem FixedPatternAdmission.variableClaim
    (language : LanguageDef) (carrier : String) (value : Pattern)
    (headValid : languageHasConstructorArity language
      (ContextualCarrierClaims.claimLabel .variable carrier) 1 = true)
    (valueValid : FixedPatternAdmission language value) :
    FixedPatternAdmission language
      (ContextualCarrierClaims.variableClaim carrier value) := by
  apply FixedPatternAdmission.apply language
  · simpa [ContextualCarrierClaims.variableClaim] using headValid
  · intro argument membership
    simp only [List.mem_singleton] at membership
    subst argument
    exact valueValid

protected theorem FixedPatternAdmission.typingClaim
    (language : LanguageDef) (carrier : String) (subject type : Pattern)
    (headValid : languageHasConstructorArity language
      (ContextualCarrierClaims.claimLabel .typing carrier) 2 = true)
    (subjectValid : FixedPatternAdmission language subject)
    (typeValid : FixedPatternAdmission language type) :
    FixedPatternAdmission language
      (ContextualCarrierClaims.typingClaim carrier subject type) := by
  apply FixedPatternAdmission.apply language
  · simpa [ContextualCarrierClaims.typingClaim] using headValid
  · intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact subjectValid
    · exact typeValid

protected theorem FixedPatternAdmission.reductionClaim
    (language : LanguageDef) (carrier : String) (source target : Pattern)
    (headValid : languageHasConstructorArity language
      (ContextualCarrierClaims.claimLabel .reduction carrier) 2 = true)
    (sourceValid : FixedPatternAdmission language source)
    (targetValid : FixedPatternAdmission language target) :
    FixedPatternAdmission language
      (ContextualCarrierClaims.reductionClaim carrier source target) := by
  apply FixedPatternAdmission.apply language
  · simpa [ContextualCarrierClaims.reductionClaim] using headValid
  · intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact sourceValid
    · exact targetValid

/-- Prefixing fixed-valid formulas to a context hole uses only the shared
binary context constructor. -/
protected theorem FixedPatternAdmission.encodeContext_prepend
    (language : LanguageDef) (formulas : List Pattern) (tailName : String)
    (extendValid : languageHasConstructorArity language
      ContextualInference.extendContextTerm.label 2 = true)
    (formulasValid :
      ∀ formula ∈ formulas, FixedPatternAdmission language formula) :
    FixedPatternAdmission language
      (ContextualInference.encodeContext
        (ContextSchema.prepend formulas (.hole tailName))) := by
  induction formulas with
  | nil =>
      simpa [ContextSchema.prepend, ContextualInference.encodeContext] using
        FixedPatternAdmission.fvar language tailName
  | cons formula formulas inductionHypothesis =>
      have tailValid := inductionHypothesis fun other membership =>
        formulasValid other (by simp [membership])
      have combined := FixedPatternAdmission.apply language
        ContextualInference.extendContextTerm.label
        [formula, ContextualInference.encodeContext
          (ContextSchema.prepend formulas (.hole tailName))]
        extendValid
        (by
          intro argument membership
          simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
          rcases membership with rfl | rfl
          · exact formulasValid _ (by simp)
          · exact tailValid)
      simpa [ContextSchema.prepend, ContextualInference.encodeContext] using
        combined

/-- A lowered sequent is a valid judgment whenever its shared outer judgment
is declared and its three arguments are fixed-constructor valid. -/
theorem lowerSequent_judgmentSchemaValid
    (definition : CalculusLanguageDef) (sequent : Sequent)
    (lookup : definition.lookupJudgment?
      ContextualInference.contextualJudgment.head 3 =
        some ContextualInference.contextualJudgment)
    (variableContext : FixedPatternAdmission definition.toLanguageDef
      (ContextualInference.encodeContext sequent.variableContext))
    (relationContext : FixedPatternAdmission definition.toLanguageDef
      (ContextualInference.encodeContext sequent.relationContext))
    (conclusion : FixedPatternAdmission definition.toLanguageDef
      sequent.conclusion) :
    definition.judgmentSchemaValid
      (ContextualInference.lowerSequent sequent) = true := by
  simp only [ContextualInference.lowerSequent,
    CalculusLanguageDef.judgmentSchemaValid, List.length_cons,
    List.length_nil, Nat.reduceAdd, lookup, Option.isSome_some,
    Bool.true_and, fixedConstructorListsValid, Bool.and_eq_true]
  exact
    ⟨variableContext.valid,
      ⟨relationContext.valid, ⟨conclusion.valid, True.intro⟩⟩⟩

/-- Compositional fixed-constructor evidence for one authored contextual
sequent in a concrete target signature. -/
structure FixedSequentAdmission (definition : CalculusLanguageDef)
    (sequent : Sequent) : Prop where
  variableContext : FixedPatternAdmission definition.toLanguageDef
    (ContextualInference.encodeContext sequent.variableContext)
  relationContext : FixedPatternAdmission definition.toLanguageDef
    (ContextualInference.encodeContext sequent.relationContext)
  conclusion : FixedPatternAdmission definition.toLanguageDef
    sequent.conclusion

theorem FixedSequentAdmission.judgmentSchemaValid
    (definition : CalculusLanguageDef) (sequent : Sequent)
    (lookup : definition.lookupJudgment?
      ContextualInference.contextualJudgment.head 3 =
        some ContextualInference.contextualJudgment)
    (admission : FixedSequentAdmission definition sequent) :
    definition.judgmentSchemaValid
      (ContextualInference.lowerSequent sequent) = true :=
  lowerSequent_judgmentSchemaValid definition sequent lookup
    admission.variableContext admission.relationContext admission.conclusion

/-! ## Exact generated-signature membership -/

/-- The occurrence slot viewed in the foundation's erased profile stream. -/
def foundationSlot {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Fin demand.foundation.typings.length :=
  ⟨slot.val, by
    rw [SelectedNativeTypeDemand.foundation_typings, List.length_map]
    exact slot.isLt⟩

@[simp] theorem foundationSlot_val {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (foundationSlot demand slot).val = slot.val :=
  rfl

@[simp] theorem foundationSlot_typing {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualModalExtension.typingAt demand.foundation
        (foundationSlot demand slot) =
      typingAt demand slot := by
  simp [foundationSlot, ContextualModalExtension.typingAt,
    SelectedNativeTypeContextualCalculus.typingAt,
    SelectedNativeTypeContextualCalculus.occurrenceAt,
    SelectedNativeTypeDemand.foundation]

/-- Any actual target term is selected at its authored arity.  Constructor
uniqueness is obtained once from structural language validation. -/
theorem constructor_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (term : GrammarRule) (membership : term ∈
      (definition demand separated).terms) :
    languageHasConstructorArity
      (definition demand separated).toLanguageDef
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

private theorem claimTerms_mem_claimTermsFor (names : List String)
    {carrier : String} (carrierMembership : carrier ∈ names)
    {term : GrammarRule}
    (termMembership : term ∈ ContextualCarrierClaims.claimTerms carrier) :
    term ∈ ContextualCarrierClaims.claimTermsFor names := by
  rw [ContextualCarrierClaims.claimTermsFor, List.mem_flatMap]
  exact ⟨carrier, carrierMembership, termMembership⟩

/-- Every universe code for a retained carrier occurs in the flat target,
whether the carrier belongs to the original modal foundation or to the exact
authored-endpoint suffix. -/
theorem universeCodeTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand)
    (code : CarrierUniverseSignature.Code) :
    CarrierUniverseSignature.rule code carrier ∈
      (definition demand separated).terms := by
  rw [definition_terms]
  simp only [List.mem_append]
  rcases List.mem_append.mp membership with stable | additional
  · apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    have grouped : CarrierUniverseSignature.rule code carrier ∈
        (ContextualModalExtension.language demand.foundation).terms := by
      rw [ContextualModalExtension.language_terms]
      apply List.mem_append_left
      rw [SelectedNativeTypeFoundation.definition_terms]
      exact universeTerm_mem_termsFor _ stable code
    have chronological : CarrierUniverseSignature.rule code carrier ∈
        (ContextualModalSignatureCompiler.definition
          demand.foundation).terms :=
      (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
        demand.foundation).terms.mem_iff.mpr grouped
    unfold SelectedNativeTypeContextualCalculus.signature
    rw [ContextualCarrierClaims.apply_terms]
    exact List.mem_append_left _ chronological
  · apply Or.inl
    apply Or.inl
    apply Or.inr
    rw [extension_terms]
    exact List.mem_append_left _
      (universeTerm_mem_termsFor _ additional code)

/-- The three contextual-claim rows for every retained carrier occur in the
same flat target as that carrier's universe codes. -/
theorem claimTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand)
    {term : GrammarRule}
    (termMembership : term ∈ ContextualCarrierClaims.claimTerms carrier) :
    term ∈ (definition demand separated).terms := by
  rw [definition_terms]
  simp only [List.mem_append]
  rcases List.mem_append.mp membership with stable | additional
  · apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    unfold SelectedNativeTypeContextualCalculus.signature
    rw [ContextualCarrierClaims.apply_terms]
    apply List.mem_append_right
    apply List.mem_append_right
    exact claimTerms_mem_claimTermsFor _ stable termMembership
  · apply Or.inl
    apply Or.inl
    apply Or.inr
    rw [extension_terms]
    apply List.mem_append_right
    exact claimTerms_mem_claimTermsFor _ additional termMembership

/-- Constructor lookup for a retained universe code is discharged once from
membership and target-language validation. -/
theorem universeCode_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand)
    (code : CarrierUniverseSignature.Code) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (CarrierUniverseSignature.label code carrier) 0 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (CarrierUniverseSignature.rule code carrier)
    (universeCodeTerm_mem demand separated membership code)
  simpa [CarrierUniverseSignature.rule] using admitted

theorem variableClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (ContextualCarrierClaims.claimLabel .variable carrier) 1 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (ContextualCarrierClaims.variableClaimTerm carrier)
    (claimTerm_mem demand separated membership (by
      simp [ContextualCarrierClaims.claimTerms]))
  simpa [ContextualCarrierClaims.variableClaimTerm] using admitted

theorem typingClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (ContextualCarrierClaims.claimLabel .typing carrier) 2 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (ContextualCarrierClaims.typingClaimTerm carrier)
    (claimTerm_mem demand separated membership (by
      simp [ContextualCarrierClaims.claimTerms]))
  simpa [ContextualCarrierClaims.typingClaimTerm] using admitted

theorem reductionClaim_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (ContextualCarrierClaims.claimLabel .reduction carrier) 2 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (ContextualCarrierClaims.reductionClaimTerm carrier)
    (claimTerm_mem demand separated membership (by
      simp [ContextualCarrierClaims.claimTerms]))
  simpa [ContextualCarrierClaims.reductionClaimTerm] using admitted

private theorem ofList_eq_some_snd_mem
    (context : List (String × TypeExpr)) (name : String) {type : TypeExpr}
    (lookup : FreeTypeContext.ofList context name = some type) :
    type ∈ context.map Prod.snd := by
  induction context with
  | nil => simp [FreeTypeContext.ofList] at lookup
  | cons entry context inductionHypothesis =>
      rcases entry with ⟨entryName, entryType⟩
      by_cases equality : entryName = name
      · subst name
        simp [FreeTypeContext.ofList] at lookup
        subst type
        simp
      · simp only [FreeTypeContext.ofList, equality, if_false] at lookup
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (inductionHypothesis lookup)

/-- Every row produced by `authoredBindings` gets its carrier from the exact
authored rewrite type context.  `filterMap` cannot manufacture a carrier. -/
theorem authoredBindingCarrier_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {binding : String × TypeExpr}
    (membership : binding ∈ authoredBindings demand slot) :
    binding.2 ∈ SelectedNativeTypeFoundation.authoredVariableCarrierTypes
      (typingAt demand slot) := by
  unfold authoredBindings DisplayedRewriteVariableProfile.typedBindings at membership
  rw [List.mem_filterMap] at membership
  obtain ⟨name, _nameMembership, mapped⟩ := membership
  unfold DisplayedRewriteVariableProfile.variableType? at mapped
  cases lookup : FreeTypeContext.ofList
      (typingAt demand slot).site.rewrite.typeContext name with
  | none => simp [lookup] at mapped
  | some type =>
      simp only [lookup, Option.map_some] at mapped
      cases mapped
      unfold SelectedNativeTypeFoundation.authoredVariableCarrierTypes
      exact ofList_eq_some_snd_mem _ _ lookup

/-- Required modal carriers retain their exact names inside the augmented
source-indexed carrier namespace. -/
theorem sourceCarrierAt_mem_of_required {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {object : TypeExpr}
    (required : object ∈ SelectedNativeTypeFoundation.requiredCarrierRoots
      (typingAt demand slot)) :
    sourceCarrierAt demand object ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand := by
  have retained : object ∈ demand.foundation.carrierObjects.objects :=
    demand.foundation.requiredCarrier_mem_objects
      (selectedTyping_mem_foundation demand slot) required
  have augmented : object ∈ (augmentedRequest demand).objects :=
    (demand.foundation.carrierObjects.objects_prefix_append
      (authoredRequest demand)).subset retained
  exact resolve_mem_carrierNames demand augmented

theorem rewriteCarrier_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    sourceCarrierAt demand (typingAt demand slot).rewriteType ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand := by
  apply sourceCarrierAt_mem_of_required demand slot
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

theorem focusCarrier_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    sourceCarrierAt demand (typingAt demand slot).focusType ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand := by
  apply sourceCarrierAt_mem_of_required demand slot
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

theorem relyBindingCarrier_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {binding : String × TypeExpr}
    (membership : binding ∈ bindingsAt demand slot) :
    sourceCarrierAt demand binding.2 ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand := by
  apply sourceCarrierAt_mem_of_required demand slot
  simp only [SelectedNativeTypeFoundation.requiredCarrierRoots,
    List.mem_append]
  apply Or.inr
  unfold DisplayedContextProfile.carrierTypes
  change binding ∈ DisplayedContextProfile.bindings
    (typingAt demand slot) at membership
  exact List.mem_map.mpr ⟨binding, membership, rfl⟩

theorem authoredBindingCarrierName_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {binding : String × TypeExpr}
    (membership : binding ∈ authoredBindings demand slot) :
    sourceCarrierAt demand binding.2 ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand := by
  apply resolve_mem_carrierNames demand
  exact authoredCarrier_mem_augmented demand slot
    (authoredBindingCarrier_mem demand slot membership)

/-- The carrier-indexed typing judgment is present for both the original
modal carrier prefix and the authored-endpoint suffix. -/
theorem typingJudgment_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    CarrierTypingLanguageDef.judgment carrier ∈
      (definition demand separated).judgments := by
  rw [definition_judgments]
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
    rw [extension_judgments]
    exact List.mem_map_of_mem additional

/-- Judgment-head uniqueness upgrades carrier-row membership to exact
fail-closed lookup. -/
theorem typingJudgment_lookup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    (definition demand separated).lookupJudgment?
        (CarrierTypingLanguageDef.typingHead carrier) 2 =
      some (CarrierTypingLanguageDef.judgment carrier) := by
  exact CalculusLanguageDef.lookupJudgment?_eq_some_of_mem _ _ headsNodup
    (typingJudgment_mem demand separated membership)

/-! ## Generator-family V2 validity -/

/-- Every carrier-universe axiom remains valid in the final mixed source and
generated signature.  The proof uses exact target lookup rather than
rechecking a concrete generated list. -/
theorem universeAxiom_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    RuleSchema.isValidIn (definition demand separated)
      (CarrierTypingLanguageDef.universeAxiom carrier) = true := by
  unfold RuleSchema.isValidIn
  rw [CarrierTypingLanguageDef.universeAxiom_isValidV1]
  simp only [Bool.true_and, RuleSchema.patterns,
    CarrierTypingLanguageDef.universeAxiom, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true]
  simp only [CalculusLanguageDef.judgmentSchemaValid, List.length_cons,
    List.length_nil, Nat.reduceAdd]
  rw [typingJudgment_lookup demand separated headsNodup membership]
  simp only [Option.isSome_some, Bool.true_and, fixedConstructorListsValid,
    fixedConstructorsValid, List.length_nil, Bool.and_true]
  rw [Bool.and_eq_true]
  exact
    ⟨universeCode_has_arity demand separated languageValid membership .star,
      universeCode_has_arity demand separated languageValid membership .box⟩

/-- The shared contextual judgment is present exactly once in every generated
source-indexed target. -/
theorem contextualJudgment_lookup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup) :
    (definition demand separated).lookupJudgment?
        ContextualInference.contextualJudgment.head 3 =
      some ContextualInference.contextualJudgment := by
  apply CalculusLanguageDef.lookupJudgment?_eq_some_of_mem _ _ headsNodup
  rw [definition_judgments]
  apply List.mem_append_left
  simp [SelectedNativeTypeContextualCalculus.signature]

/-- Shared context constructors are literal members of the generated
signature prefix. -/
theorem emptyContextTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    ContextualInference.emptyContextTerm ∈
      (definition demand separated).terms := by
  rw [definition_terms]
  simp [SelectedNativeTypeContextualCalculus.signature]

theorem extendContextTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    ContextualInference.extendContextTerm ∈
      (definition demand separated).terms := by
  rw [definition_terms]
  simp [SelectedNativeTypeContextualCalculus.signature]

theorem contextCodeTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    ContextualInferenceCanonicalContext.contextCodeTerm ∈
      (definition demand separated).terms := by
  rw [definition_terms]
  simp [SelectedNativeTypeContextualCalculus.signature,
    ContextualInferenceCanonicalContext.extension]

/-- The exact occurrence-indexed result-family constructor is a literal target
row. -/
theorem familyApplicationTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) (slot : Occurrence demand) :
    familyApplicationTerm demand slot ∈
      (definition demand separated).terms := by
  rw [definition_terms]
  simp [familyApplicationTerms]

/-- The private step-claim constructor for one exact authored occurrence is
a literal row of the flat target. -/
theorem occurrenceStepTerm_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) (slot : Occurrence demand) :
    SelectedNativeTypeOccurrenceStepClaim.termAt demand slot ∈
      (definition demand separated).terms := by
  rw [definition_terms]
  simp [SelectedNativeTypeOccurrenceStepClaim.terms]

/-- Chronological modal generation and its grouped specification contain the
same exact occurrence-indexed modal row. -/
theorem modalRuleAt_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) (slot : Occurrence demand) :
    ContextualModalExtension.modalRuleAt demand.foundation
        (foundationSlot demand slot) ∈
      (definition demand separated).terms := by
  have grouped :
      ContextualModalExtension.modalRuleAt demand.foundation
          (foundationSlot demand slot) ∈
        (ContextualModalExtension.language demand.foundation).terms := by
    rw [ContextualModalExtension.language_terms]
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨foundationSlot demand slot, rfl⟩
  have chronological :
      ContextualModalExtension.modalRuleAt demand.foundation
          (foundationSlot demand slot) ∈
        (ContextualModalSignatureCompiler.definition
          demand.foundation).terms :=
    (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      demand.foundation).terms.mem_iff.mpr grouped
  have signatureMembership :
      ContextualModalExtension.modalRuleAt demand.foundation
          (foundationSlot demand slot) ∈
        (SelectedNativeTypeContextualCalculus.signature demand).terms := by
    simp only [SelectedNativeTypeContextualCalculus.signature,
      ContextualCarrierClaims.apply_terms, List.mem_append]
    exact Or.inl chronological
  rw [definition_terms]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr signatureMembership)))

/-- Exact arities of the shared context constructors in every admitted
source-indexed target. -/
theorem emptyContext_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = []) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      ContextualInference.emptyContextTerm.label 0 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    ContextualInference.emptyContextTerm
    (emptyContextTerm_mem demand separated)
  simpa [ContextualInference.emptyContextTerm] using admitted

theorem extendContext_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = []) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      ContextualInference.extendContextTerm.label 2 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    ContextualInference.extendContextTerm
    (extendContextTerm_mem demand separated)
  simpa [ContextualInference.extendContextTerm] using admitted

theorem contextCode_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = []) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      ContextualInferenceCanonicalContext.contextCodeTerm.label 1 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    ContextualInferenceCanonicalContext.contextCodeTerm
    (contextCodeTerm_mem demand separated)
  simpa [ContextualInferenceCanonicalContext.contextCodeTerm] using admitted

theorem emptyContext_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = []) :
    FixedPatternAdmission (definition demand separated).toLanguageDef
      (ContextualInference.encodeContext .empty) := by
  apply FixedPatternAdmission.apply
  · simpa [ContextualInference.encodeContext] using
      emptyContext_has_arity demand separated languageValid
  · simp

/-- A canonical-context claim over any fixed wire is itself a fixed contextual
sequent in the generated signature. -/
theorem canonicalContextSequent_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (wire : Pattern)
    (wireFixed : FixedPatternAdmission
      (definition demand separated).toLanguageDef wire) :
    FixedSequentAdmission (definition demand separated)
      (ContextualInferenceCanonicalContext.sequent wire) := by
  have emptyFixed := emptyContext_fixed demand separated languageValid
  refine
    { variableContext := emptyFixed
      relationContext := emptyFixed
      conclusion := ?_ }
  apply FixedPatternAdmission.apply
  · simpa [ContextualInferenceCanonicalContext.claim] using
      contextCode_has_arity demand separated languageValid
  · intro argument membership
    simp only [List.mem_singleton] at membership
    subst argument
    exact wireFixed

/-- The carrier-to-contextual bridge is valid only after both ambient
arguments have supplied canonical-context certificates. -/
theorem liftTypingRule_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand) :
    RuleSchema.isValidIn (definition demand separated)
      (ContextualCarrierClaims.liftTypingRule carrier) = true := by
  have contextualLookup :=
    contextualJudgment_lookup demand separated headsNodup
  have gammaValid := FixedSequentAdmission.judgmentSchemaValid _ _
    contextualLookup
    (canonicalContextSequent_fixed demand separated languageValid
      (.fvar "Gamma") (FixedPatternAdmission.fvar _ _))
  have deltaValid := FixedSequentAdmission.judgmentSchemaValid _ _
    contextualLookup
    (canonicalContextSequent_fixed demand separated languageValid
      (.fvar "Delta") (FixedPatternAdmission.fvar _ _))
  have typingValid :
      (definition demand separated).judgmentSchemaValid
        (.apply (CarrierTypingLanguageDef.typingHead carrier)
          [.fvar "term", .fvar "type"]) = true := by
    simp only [CalculusLanguageDef.judgmentSchemaValid, List.length_cons,
      List.length_nil, Nat.reduceAdd]
    rw [typingJudgment_lookup demand separated headsNodup membership]
    simp [fixedConstructorListsValid, fixedConstructorsValid]
  have claimFixed := FixedPatternAdmission.typingClaim
    (definition demand separated).toLanguageDef carrier
    (.fvar "term") (.fvar "type")
    (typingClaim_has_arity demand separated languageValid membership)
    (FixedPatternAdmission.fvar _ _)
    (FixedPatternAdmission.fvar _ _)
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _
    contextualLookup
    ({ variableContext := FixedPatternAdmission.fvar _ "Gamma"
       relationContext := FixedPatternAdmission.fvar _ "Delta"
       conclusion := claimFixed } :
      FixedSequentAdmission (definition demand separated)
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

/-- The family and modal arities are derived from the exact authored rely
telescope; no generated row carries a separately supplied arity. -/
theorem familyApplication_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (auxiliaryLabel .familyApplication slot.val)
      ((bindingsAt demand slot).length + 1) = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (familyApplicationTerm demand slot)
    (familyApplicationTerm_mem demand separated slot)
  simpa [familyApplicationTerm] using admitted

/-- Occurrence-step formulas always retain their two ordered endpoints. -/
theorem occurrenceStep_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (SelectedNativeTypeOccurrenceStepClaim.Naming.label slot.val) 2 = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (SelectedNativeTypeOccurrenceStepClaim.termAt demand slot)
    (occurrenceStepTerm_mem demand separated slot)
  simpa [SelectedNativeTypeOccurrenceStepClaim.termAt] using admitted

theorem modal_has_arity {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    languageHasConstructorArity (definition demand separated).toLanguageDef
      (SelectedModalNaming.label slot.val)
      ((bindingsAt demand slot).length + 1) = true := by
  have admitted := constructor_has_arity demand separated languageValid
    (ContextualModalExtension.modalRuleAt demand.foundation
      (foundationSlot demand slot))
    (modalRuleAt_mem demand separated slot)
  simpa [ContextualModalExtension.modalRuleAt,
    ContextualModalSignature.modalRule,
    ContextualModalSignature.parameters,
    ContextualModalSignature.parametersFor,
    ContextualModalSignature.relyParametersFor,
    ContextualModalSignature.relyBindings,
    foundationSlot_typing,
    SelectedNativeTypeContextualCalculus.bindingsAt,
    DisplayedContextProfile.bindings] using admitted

/-! ## Fixed-pattern admissions for generated source-indexed syntax -/

theorem sortCode_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    {carrier : String}
    (membership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand)
    (code : CarrierUniverseSignature.Code) :
    FixedPatternAdmission (definition demand separated).toLanguageDef
      (sortCode carrier code) := by
  apply FixedPatternAdmission.apply
  · simpa [sortCode] using
      universeCode_has_arity demand separated languageValid membership code
  · intro argument impossible
    simp at impossible

theorem modalType_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) (family : Pattern)
    (familyFixed : FixedPatternAdmission
      (definition demand separated).toLanguageDef family) :
    FixedPatternAdmission (definition demand separated).toLanguageDef
      (modalType demand slot family) := by
  apply FixedPatternAdmission.apply
  · simpa [modalType, relyTypes] using
      modal_has_arity demand separated languageValid slot
  · intro argument membership
    rw [List.mem_append] at membership
    rcases membership with rely | familyMember
    · rw [relyTypes, List.mem_ofFn] at rely
      obtain ⟨index, rfl⟩ := rely
      exact FixedPatternAdmission.fvar _ _
    · simp only [List.mem_singleton] at familyMember
      subst argument
      exact familyFixed

theorem authoredFamilyApplication_fixed
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) (family : Pattern)
    (familyFixed : FixedPatternAdmission
      (definition demand separated).toLanguageDef family) :
    FixedPatternAdmission (definition demand separated).toLanguageDef
      (authoredFamilyApplication demand slot family) := by
  apply FixedPatternAdmission.apply
  · simpa [authoredFamilyApplication, authoredRelyValues,
      ContextualFamilyApplication.applyFamily] using
        familyApplication_has_arity demand separated languageValid slot
  · intro argument membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | rely
    · exact familyFixed
    · rw [authoredRelyValues, List.mem_ofFn] at rely
      obtain ⟨index, rfl⟩ := rely
      exact FixedPatternAdmission.fvar _ _

theorem authoredVariableClaims_fixed
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ formula ∈ authoredVariableClaims demand slot,
      FixedPatternAdmission (definition demand separated).toLanguageDef
        formula := by
  intro formula membership
  unfold authoredVariableClaims at membership
  obtain ⟨binding, bindingMembership, rfl⟩ := List.mem_map.mp membership
  apply FixedPatternAdmission.variableClaim
  · exact variableClaim_has_arity demand separated languageValid
      (authoredBindingCarrierName_mem demand slot bindingMembership)
  · exact FixedPatternAdmission.fvar _ _

theorem authoredRelyVariableClaims_fixed
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ formula ∈ authoredRelyVariableClaims demand slot,
      FixedPatternAdmission (definition demand separated).toLanguageDef
        formula := by
  intro formula membership
  rw [authoredRelyVariableClaims, List.mem_ofFn] at membership
  obtain ⟨index, rfl⟩ := membership
  let binding := (bindingsAt demand slot).get index
  apply FixedPatternAdmission.variableClaim
  · exact variableClaim_has_arity demand separated languageValid
      (relyBindingCarrier_mem demand slot (List.get_mem _ index))
  · exact FixedPatternAdmission.fvar _ _

theorem authoredRelyTypingClaims_fixed
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ formula ∈ authoredRelyTypingClaims demand slot,
      FixedPatternAdmission (definition demand separated).toLanguageDef
        formula := by
  intro formula membership
  rw [authoredRelyTypingClaims, List.mem_ofFn] at membership
  obtain ⟨index, rfl⟩ := membership
  let binding := (bindingsAt demand slot).get index
  apply FixedPatternAdmission.typingClaim
  · exact typingClaim_has_arity demand separated languageValid
      (relyBindingCarrier_mem demand slot (List.get_mem _ index))
  · exact FixedPatternAdmission.fvar _ _
  · exact FixedPatternAdmission.fvar _ _

/-- Every rely-sort premise is admitted from the exact fixed-context binding
that generated it. -/
theorem relySortPremises_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    ∀ sequent ∈
        SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot,
      FixedSequentAdmission (definition demand separated) sequent := by
  intro sequent membership
  rw [SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
    List.mem_ofFn] at membership
  obtain ⟨index, rfl⟩ := membership
  let binding := (bindingsAt demand slot).get index
  let carrier := sourceCarrierAt demand binding.2
  have carrierMembership : carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        additionalCarrierNames demand :=
    relyBindingCarrier_mem demand slot (List.get_mem _ index)
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · exact FixedPatternAdmission.fvar _ _
  · exact FixedPatternAdmission.fvar _ _
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated languageValid
        carrierMembership
    · exact FixedPatternAdmission.fvar _ _
    · apply sortCode_fixed demand separated languageValid carrierMembership

/-- The paper's result-family sort premise validates without rechecking its
finished nested pattern against the entire generated constructor table. -/
theorem authoredResultSortPremise_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    FixedSequentAdmission (definition demand separated)
      (authoredResultSortPremise demand slot) := by
  have carrierMembership := rewriteCarrier_mem demand slot
  have familyFixed := authoredFamilyApplication_fixed demand separated
    languageValid slot (.fvar "result-family")
    (FixedPatternAdmission.fvar _ _)
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated languageValid
    · exact authoredRelyVariableClaims_fixed demand separated languageValid
        slot
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated languageValid
    · exact authoredRelyTypingClaims_fixed demand separated languageValid slot
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated languageValid
        carrierMembership
    · exact familyFixed
    · exact sortCode_fixed demand separated languageValid carrierMembership _

/-- Target-signature admission of the three literal authored patterns used by
paper-faithful introduction.  This is deliberately distinct from local schema
admission: these proofs say the constructors really occur in the final flat
language. -/
structure TargetOccurrenceAdmission {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (slot : Occurrence demand) : Prop where
  source : FixedPatternAdmission (definition demand separated).toLanguageDef
    (authoredSource demand slot)
  target : FixedPatternAdmission (definition demand separated).toLanguageDef
    (authoredTarget demand slot)
  focus : FixedPatternAdmission (definition demand separated).toLanguageDef
    (authoredFocus demand slot)

theorem formationConclusion_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand) :
    FixedSequentAdmission (definition demand separated)
      (SelectedNativeTypeSourceIndexedIntroduction.formationRule
        demand slot).conclusion := by
  have carrierMembership := focusCarrier_mem demand slot
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · exact FixedPatternAdmission.fvar _ _
  · exact FixedPatternAdmission.fvar _ _
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated languageValid
        carrierMembership
    · exact modalType_fixed demand separated languageValid slot
        (.fvar "result-family") (FixedPatternAdmission.fvar _ _)
    · exact sortCode_fixed demand separated languageValid carrierMembership _

theorem introductionBodyPremise_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand)
    (admission : TargetOccurrenceAdmission demand separated slot) :
    FixedSequentAdmission (definition demand separated)
      (introductionBodyPremise demand slot) := by
  have carrierMembership := rewriteCarrier_mem demand slot
  have familyFixed := authoredFamilyApplication_fixed demand separated
    languageValid slot (.fvar "result-family")
      (FixedPatternAdmission.fvar _ _)
  have occurrenceStepFixed : FixedPatternAdmission
      (definition demand separated).toLanguageDef
      (SelectedNativeTypeOccurrenceStepClaim.claim slot
        (authoredSource demand slot) (authoredTarget demand slot)) := by
    apply FixedPatternAdmission.apply
    · exact occurrenceStep_has_arity demand separated languageValid slot
    · intro argument membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · exact admission.source
      · exact admission.target
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated languageValid
    · exact authoredVariableClaims_fixed demand separated languageValid slot
  · apply FixedPatternAdmission.encodeContext_prepend
    · exact extendContext_has_arity demand separated languageValid
    · intro formula membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | rely
      · exact occurrenceStepFixed
      · exact authoredRelyTypingClaims_fixed demand separated languageValid
          slot formula rely
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated languageValid
        carrierMembership
    · exact admission.target
    · exact familyFixed

theorem introductionConclusion_fixed {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (slot : Occurrence demand)
    (admission : TargetOccurrenceAdmission demand separated slot) :
    FixedSequentAdmission (definition demand separated)
      (introductionConclusion demand slot) := by
  have carrierMembership := focusCarrier_mem demand slot
  refine
    { variableContext := ?_
      relationContext := ?_
      conclusion := ?_ }
  · exact FixedPatternAdmission.fvar _ _
  · exact FixedPatternAdmission.fvar _ _
  · apply FixedPatternAdmission.typingClaim
    · exact typingClaim_has_arity demand separated languageValid
        carrierMembership
    · exact admission.focus
    · exact modalType_fixed demand separated languageValid slot
        (.fvar "result-family") (FixedPatternAdmission.fvar _ _)

/-! ## Whole generated-rule validity -/

/-- Exact pattern inventory of a generated formation rule.  The theorem
exposes the compositional validation boundary without unfolding the target
signature or its constructor lookup for every emitted occurrence. -/
theorem formationRule_patterns {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    RuleSchema.patterns
        (lowerRule
          (SelectedNativeTypeSourceIndexedIntroduction.formationRule
            demand slot)) =
      (SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent ++
        [ lowerSequent (authoredResultSortPremise demand slot)
        , lowerSequent
            (SelectedNativeTypeSourceIndexedIntroduction.formationRule
              demand slot).conclusion ] := by
  simp [SelectedNativeTypeSourceIndexedIntroduction.formationRule,
    inferMetavariables,
    SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore,
    lowerRule, RuleSchema.patterns]

/-- Exact pattern inventory of a generated introduction rule. -/
theorem introductionRule_patterns {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    RuleSchema.patterns
        (lowerRule
          (SelectedNativeTypeSourceIndexedIntroduction.introductionRule
            demand slot)) =
      (SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent ++
        [ lowerSequent (authoredResultSortPremise demand slot)
        , lowerSequent (introductionBodyPremise demand slot)
        , lowerSequent (introductionConclusion demand slot) ] := by
  simp [SelectedNativeTypeSourceIndexedIntroduction.introductionRule,
    inferMetavariables,
    SelectedNativeTypeSourceIndexedIntroduction.introductionRuleCore,
    lowerRule, RuleSchema.patterns]

/-- Every admitted formation row passes the complete target rule checker.
The proof composes occurrence-local syntax admission with exact target
signature membership; it does not normalize the completed generated rule. -/
theorem formationRule_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (slot : Occurrence demand)
    (occurrence : OccurrenceAdmission demand slot) :
    RuleSchema.isValidIn (definition demand separated)
      (lowerRule
        (SelectedNativeTypeSourceIndexedIntroduction.formationRule
          demand slot)) = true := by
  have lookup := contextualJudgment_lookup demand separated headsNodup
  have relyValid :
      ((SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent).all
        (definition demand separated).judgmentSchemaValid = true := by
    apply List.all_eq_true.mpr
    intro sequent membership
    obtain ⟨sourceSequent, sourceMembership, rfl⟩ :=
      List.mem_map.mp membership
    exact FixedSequentAdmission.judgmentSchemaValid _ _ lookup
      (relySortPremises_fixed demand separated languageValid slot
        sourceSequent sourceMembership)
  have resultValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (authoredResultSortPremise_fixed demand separated languageValid slot)
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (formationConclusion_fixed demand separated languageValid slot)
  unfold RuleSchema.isValidIn
  rw [SelectedNativeTypeSourceIndexedIntroduction.formationRule_locallyValid
    demand slot occurrence.formation]
  simp only [Bool.true_and]
  rw [formationRule_patterns]
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    relyValid, resultValid, conclusionValid, Bool.true_and]
  rfl

/-- Every admitted paper-faithful introduction row passes the complete target
rule checker.  Literal authored source, target, and focus patterns enter only
through the independent target occurrence admission. -/
theorem introductionRule_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (slot : Occurrence demand)
    (occurrence : OccurrenceAdmission demand slot)
    (target : TargetOccurrenceAdmission demand separated slot) :
    RuleSchema.isValidIn (definition demand separated)
      (lowerRule
        (SelectedNativeTypeSourceIndexedIntroduction.introductionRule
          demand slot)) = true := by
  have lookup := contextualJudgment_lookup demand separated headsNodup
  have relyValid :
      ((SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot).map lowerSequent).all
        (definition demand separated).judgmentSchemaValid = true := by
    apply List.all_eq_true.mpr
    intro sequent membership
    obtain ⟨sourceSequent, sourceMembership, rfl⟩ :=
      List.mem_map.mp membership
    exact FixedSequentAdmission.judgmentSchemaValid _ _ lookup
      (relySortPremises_fixed demand separated languageValid slot
        sourceSequent sourceMembership)
  have resultValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (authoredResultSortPremise_fixed demand separated languageValid slot)
  have bodyValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (introductionBodyPremise_fixed demand separated languageValid slot target)
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (introductionConclusion_fixed demand separated languageValid slot target)
  unfold RuleSchema.isValidIn
  rw [SelectedNativeTypeSourceIndexedIntroduction.introductionRule_locallyValid
    demand slot occurrence.introduction]
  simp only [Bool.true_and]
  rw [introductionRule_patterns]
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    relyValid, resultValid, bodyValid, conclusionValid, Bool.true_and]
  rfl

/-- The pair of rules at one authored occurrence passes the complete target
checker from one structural occurrence admission and one literal-pattern
target admission. -/
theorem rulesAt_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (slot : Occurrence demand)
    (occurrence : OccurrenceAdmission demand slot)
    (target : TargetOccurrenceAdmission demand separated slot) :
    (SelectedNativeTypeSourceIndexedIntroduction.rulesAt demand slot).all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  simp [SelectedNativeTypeSourceIndexedIntroduction.rulesAt,
    formationRule_validIn demand separated languageValid headsNodup slot
      occurrence,
    introductionRule_validIn demand separated languageValid headsNodup slot
      occurrence target]

/-- All paper-faithful rows generated from a selected profile pass the target
checker.  The proof ranges over source occurrences, so regenerating a profile
does not create a parallel list of per-row proof obligations. -/
theorem profiledRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (occurrence : ∀ slot, OccurrenceAdmission demand slot)
    (target : ∀ slot, TargetOccurrenceAdmission demand separated slot) :
    (SelectedNativeTypeSourceIndexedIntroduction.profiledRules demand).all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  rw [SelectedNativeTypeSourceIndexedIntroduction.profiledRules,
    List.all_flatten]
  apply List.all_eq_true.mpr
  intro row membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp membership
  exact rulesAt_validIn demand separated languageValid headsNodup slot
    (occurrence slot) (target slot)

/-! ## Whole flat-calculus rule validity -/

/-- Exact decomposition of the source-independent signature rules.  The
chronological modal compiler may permute constructor rows, but it preserves
the proof rows exactly. -/
theorem signature_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (SelectedNativeTypeContextualCalculus.signature demand).rules =
      (SelectedNativeTypeFoundation.stableCarrierNames demand.foundation).map
          CarrierTypingLanguageDef.universeAxiom ++
        ContextualInferenceCanonicalContext.extension.newRules ++
          ContextualCarrierClaims.bridgeRules
            (SelectedNativeTypeFoundation.stableCarrierNames
              demand.foundation) := by
  rw [SelectedNativeTypeContextualCalculus.signature,
    ContextualCarrierClaims.apply_rules]
  rw [(ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
    demand.foundation).rules]
  rw [ContextualModalExtension.language_rules,
    SelectedNativeTypeFoundation.definition_rules]

/-- Universe axioms for any covered carrier subinventory remain valid in the
final flat target. -/
theorem universeAxioms_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (carriers : List String)
    (covered : ∀ carrier ∈ carriers,
      carrier ∈
        SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
          additionalCarrierNames demand) :
    (carriers.map CarrierTypingLanguageDef.universeAxiom).all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  apply List.all_eq_true.mpr
  intro rule membership
  obtain ⟨carrier, carrierMembership, rfl⟩ := List.mem_map.mp membership
  exact universeAxiom_validIn demand separated languageValid headsNodup
    (covered carrier carrierMembership)

/-- Contextual bridges for any covered carrier subinventory remain valid in
the final flat target. -/
theorem bridgeRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (carriers : List String)
    (covered : ∀ carrier ∈ carriers,
      carrier ∈
        SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
          additionalCarrierNames demand) :
    (ContextualCarrierClaims.bridgeRules carriers).all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  unfold ContextualCarrierClaims.bridgeRules
  apply List.all_eq_true.mpr
  intro rule membership
  obtain ⟨carrier, carrierMembership, rfl⟩ := List.mem_map.mp membership
  exact liftTypingRule_validIn demand separated languageValid headsNodup
    (covered carrier carrierMembership)

private theorem canonicalNil_locallyValid :
    RuleSchema.isLocallyValid
      ContextualInferenceCanonicalContext.nilRule = true := by
  decide +kernel

private theorem canonicalCons_locallyValid :
    RuleSchema.isLocallyValid
      ContextualInferenceCanonicalContext.consRule = true := by
  decide +kernel

theorem canonicalContextNil_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup) :
    RuleSchema.isValidIn (definition demand separated)
      ContextualInferenceCanonicalContext.nilRule = true := by
  have lookup := contextualJudgment_lookup demand separated headsNodup
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (canonicalContextSequent_fixed demand separated languageValid
      (ContextualInference.encodeContext .empty)
      (emptyContext_fixed demand separated languageValid))
  unfold RuleSchema.isValidIn
  rw [canonicalNil_locallyValid]
  simp [ContextualInferenceCanonicalContext.nilRule, RuleSchema.patterns,
    conclusionValid]

theorem canonicalContextCons_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup) :
    RuleSchema.isValidIn (definition demand separated)
      ContextualInferenceCanonicalContext.consRule = true := by
  have lookup := contextualJudgment_lookup demand separated headsNodup
  have premiseValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (canonicalContextSequent_fixed demand separated languageValid
      (.fvar "tail") (FixedPatternAdmission.fvar _ _))
  have extendedFixed : FixedPatternAdmission
      (definition demand separated).toLanguageDef
      (.apply ContextualInference.extendContextTerm.label
        [.fvar "formula", .fvar "tail"]) := by
    apply FixedPatternAdmission.apply
    · exact extendContext_has_arity demand separated languageValid
    · intro argument membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl <;>
        exact FixedPatternAdmission.fvar _ _
  have conclusionValid := FixedSequentAdmission.judgmentSchemaValid _ _ lookup
    (canonicalContextSequent_fixed demand separated languageValid _
      extendedFixed)
  unfold RuleSchema.isValidIn
  rw [canonicalCons_locallyValid]
  simp [ContextualInferenceCanonicalContext.consRule,
    ContextualInferenceCanonicalContext.premise, RuleSchema.patterns,
    premiseValid, conclusionValid]

theorem canonicalContextRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup) :
    ContextualInferenceCanonicalContext.extension.newRules.all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  simp [ContextualInferenceCanonicalContext.extension,
    canonicalContextNil_validIn demand separated languageValid headsNodup,
    canonicalContextCons_validIn demand separated languageValid headsNodup]

/-- Every source-independent generated signature rule validates in the final
source-indexed target. -/
theorem signatureRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup) :
    (SelectedNativeTypeContextualCalculus.signature demand).rules.all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  rw [signature_rules, List.all_append, Bool.and_eq_true]
  constructor
  · rw [List.all_append, Bool.and_eq_true]
    constructor
    · exact universeAxioms_validIn demand separated languageValid headsNodup _
        (by
          intro carrier membership
          exact List.mem_append_left _ membership)
    · exact canonicalContextRules_validIn demand separated languageValid
        headsNodup
  · exact bridgeRules_validIn demand separated languageValid headsNodup _
      (by
        intro carrier membership
        exact List.mem_append_left _ membership)

/-- Every endpoint-carrier support rule validates in the final source-indexed
target. -/
theorem carrierExtensionRules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup) :
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newRules.all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_rules,
    List.all_append, Bool.and_eq_true]
  constructor
  · exact universeAxioms_validIn demand separated languageValid headsNodup _
      (by
        intro carrier membership
        exact List.mem_append_right _ membership)
  · exact bridgeRules_validIn demand separated languageValid headsNodup _
      (by
        intro carrier membership
        exact List.mem_append_right _ membership)

/-- Complete rule validity for the flat source-indexed calculus.  This is the
central compositional replacement for normalizing the finished rule array:
signature, carrier support, and occurrence-indexed rows are checked by their
independent generator-family theorems and then combined exactly once. -/
theorem rules_validIn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (occurrence : ∀ slot, OccurrenceAdmission demand slot)
    (target : ∀ slot, TargetOccurrenceAdmission demand separated slot) :
    (definition demand separated).rules.all
      (RuleSchema.isValidIn (definition demand separated)) = true := by
  rw [SelectedNativeTypeSourceIndexedCalculus.definition_rules,
    List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact
    ⟨⟨signatureRules_validIn demand separated languageValid headsNodup,
        carrierExtensionRules_validIn demand separated languageValid
          headsNodup⟩,
      profiledRules_validIn demand separated languageValid headsNodup
        occurrence target⟩

/-- Admit the complete flat calculus from small, explicit structural gates.
The expensive rule coordinate is supplied compositionally by `rules_validIn`;
the remaining finite namespace checks stay visible to concrete clients. -/
theorem definition_isValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (languageValid :
      (definition demand separated).toLanguageDef.validate = [])
    (headsNodup :
      ((definition demand separated).judgments.map JudgmentDecl.head).Nodup)
    (ruleIdsNodup : (definition demand separated).ruleIds.Nodup)
    (judgmentValid :
      (definition demand separated).judgmentSignatureValid = true)
    (conversionValid :
      (definition demand separated).conversionDeclarationValid = true)
    (occurrence : ∀ slot, OccurrenceAdmission demand slot)
    (target : ∀ slot, TargetOccurrenceAdmission demand separated slot) :
    (definition demand separated).isValid = true := by
  have allValid := rules_validIn demand separated languageValid headsNodup
    occurrence target
  have localRules :
      (definition demand separated).rules.all RuleSchema.isLocallyValid = true := by
    apply List.all_eq_true.mpr
    intro rule membership
    have valid := List.all_eq_true.mp allValid rule membership
    unfold RuleSchema.isValidIn at valid
    rw [Bool.and_eq_true] at valid
    exact valid.1
  have ruleIdsValid :
      ((definition demand separated).ruleIds.eraseDups.length ==
        (definition demand separated).ruleIds.length) = true :=
    (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr
      ruleIdsNodup
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [languageValid, localRules, ruleIdsValid, judgmentValid, allValid,
    conversionValid]
  rfl

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedValidation
