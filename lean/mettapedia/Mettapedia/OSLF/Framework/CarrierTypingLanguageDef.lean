import Mettapedia.OSLF.Framework.CarrierUniverseSignatureFunctor
import Mettapedia.GSLT.LanguageDef.InferenceSignatureLookup

/-!
# Per-carrier typing language definition

The Stay--Wells per-object enrichment adds, for every carrier `X`, two closed
codes `∗X` and `□X`, a binary judgment `::X`, and the axiom
`∗X ::X □X`.  `CarrierUniverseSignature` supplies the term constructors.
This module attaches the judgment and zero-premise inference rule through the
generic proof-calculus extension.

The result is a validated calculus language, not merely a list of names.
It is still only the per-carrier foundation: contextual modalities and their
formation/introduction/elimination rules are generated in later layers.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker

namespace CarrierTypingLanguageDef

/-- Carrier-indexed typing-judgment head. -/
def typingHead (carrier : String) : String :=
  String.ofList
    ('$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' :: 't' :: ':' ::
      carrier.toList)

/-- Decode exactly the carrier-indexed typing-judgment namespace. -/
def typingCarrier? (head : String) : Option String :=
  match head.toList with
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' :: 't' :: ':' :: carrier =>
      some (String.ofList carrier)
  | _ => none

@[simp]
theorem typingCarrier?_typingHead (carrier : String) :
    typingCarrier? (typingHead carrier) = some carrier := by
  simp [typingCarrier?, typingHead]

/-- A successfully decoded typing head is exactly the generated head of its
reconstructed carrier name. -/
theorem typingHead_of_typingCarrier?_eq_some {head carrier : String}
    (decoded : typingCarrier? head = some carrier) :
    typingHead carrier = head := by
  unfold typingCarrier? at decoded
  split at decoded
  next suffix equation =>
    cases decoded
    rw [← String.ofList_toList (s := head), equation]
    unfold typingHead
    simp only [String.toList_ofList]
  all_goals simp at decoded

/-- Stable identifier of the per-carrier universe axiom. -/
def axiomName (carrier : String) : String :=
  String.ofList
    ('$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' :: 'a' :: ':' ::
      carrier.toList)

theorem typingHead_injective : Function.Injective typingHead := by
  intro first second equality
  apply String.toList_injective
  have lists := congrArg String.toList equality
  simpa [typingHead] using lists

theorem axiomName_injective : Function.Injective axiomName := by
  intro first second equality
  apply String.toList_injective
  have lists := congrArg String.toList equality
  simpa [axiomName] using lists

/-- Judgment declaration for `::X`. -/
def judgment (carrier : String) : JudgmentDecl where
  head := typingHead carrier
  arity := 2

/-- The closed judgment `∗X ::X □X`. -/
def universeAxiom (carrier : String) : RuleSchema where
  id := ⟨axiomName carrier⟩
  metavariables := []
  premises := []
  conclusion := .apply (typingHead carrier)
    [ .apply (CarrierUniverseSignature.label .star carrier) []
    , .apply (CarrierUniverseSignature.label .box carrier) [] ]
  sideConditions := []

/-- One judgment declaration per authored carrier. -/
def judgments (source : ValidatedLanguageDef) : List JudgmentDecl :=
  source.language.typeNames.map judgment

/-- One universe axiom per authored carrier. -/
def axioms (source : ValidatedLanguageDef) : List RuleSchema :=
  source.language.typeNames.map universeAxiom

/-- The exact per-carrier proof calculus. -/
def calculus (source : ValidatedLanguageDef) : ProofCalculus where
  judgments := judgments source
  rules := axioms source
  conversion := none

/-- Flat calculus language before the generic V2 gate is discharged. -/
def definition (source : ValidatedLanguageDef) : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    (CarrierUniverseSignature.language source) (calculus source)

@[simp]
theorem length_judgments (source : ValidatedLanguageDef) :
    (judgments source).length = source.language.types.length := by
  simp [judgments, LanguageDef.typeNames]

@[simp]
theorem length_axioms (source : ValidatedLanguageDef) :
    (axioms source).length = source.language.types.length := by
  simp [axioms, LanguageDef.typeNames]

theorem judgmentHeads (source : ValidatedLanguageDef) :
    (judgments source).map JudgmentDecl.head =
      source.language.typeNames.map typingHead := by
  simp [judgments, judgment, List.map_map]

theorem ruleIds (source : ValidatedLanguageDef) :
    (axioms source).map RuleSchema.id =
      source.language.typeNames.map (fun carrier => ⟨axiomName carrier⟩) := by
  simp [axioms, universeAxiom, List.map_map]

theorem judgmentHeads_nodup (source : ValidatedLanguageDef) :
    ((judgments source).map JudgmentDecl.head).Nodup := by
  rw [judgmentHeads]
  exact (LanguageDef.typeNames_nodup_of_validate_eq_nil
    source.language source.valid).map typingHead_injective

theorem ruleIds_nodup (source : ValidatedLanguageDef) :
    ((axioms source).map RuleSchema.id).Nodup := by
  rw [ruleIds]
  apply (LanguageDef.typeNames_nodup_of_validate_eq_nil
    source.language source.valid).map
  intro first second equality
  exact axiomName_injective (congrArg RuleId.value equality)

/-- Each declared carrier contributes both fixed constructors used by its
universe axiom. -/
theorem universeRule_mem (source : ValidatedLanguageDef)
    (code : CarrierUniverseSignature.Code) {carrier : String}
    (carrierMembership : carrier ∈ source.language.typeNames) :
    CarrierUniverseSignature.rule code carrier ∈
      (CarrierUniverseSignature.language source).terms := by
  change CarrierUniverseSignature.rule code carrier ∈
    CarrierUniverseSignature.terms source
  unfold CarrierUniverseSignature.terms CarrierUniverseSignature.termsFor
  apply List.mem_flatMap.mpr
  refine ⟨carrier, carrierMembership, ?_⟩
  cases code <;> simp

/-- The checker sees each generated universe code as one nullary constructor. -/
theorem universeCode_has_arity_zero (source : ValidatedLanguageDef)
    (code : CarrierUniverseSignature.Code) {carrier : String}
    (carrierMembership : carrier ∈ source.language.typeNames) :
    languageHasConstructorArity
      (CarrierUniverseSignature.language source)
      (CarrierUniverseSignature.label code carrier) 0 = true := by
  unfold languageHasConstructorArity
  have filtered :
      (CarrierUniverseSignature.language source).terms.filter
          (fun candidate => candidate.label ==
            CarrierUniverseSignature.label code carrier) =
        [CarrierUniverseSignature.rule code carrier] := by
    simpa [CarrierUniverseSignature.rule] using
      LanguageDef.filter_terms_by_label_eq_singleton
        (CarrierUniverseSignature.language source).terms
        (CarrierUniverseSignature.rule code carrier)
        (by simpa [CarrierUniverseSignature.language] using
          CarrierUniverseSignature.termLabels_nodup source)
        (universeRule_mem source code carrierMembership)
  rw [filtered]
  simp [CarrierUniverseSignature.rule]

/-- Exact lookup of the carrier-indexed typing judgment. -/
theorem lookupJudgment (source : ValidatedLanguageDef) {carrier : String}
    (carrierMembership : carrier ∈ source.language.typeNames) :
    (definition source).lookupJudgment? (typingHead carrier) 2 =
      some (judgment carrier) := by
  exact CalculusLanguageDef.lookupJudgment?_eq_some_of_mem
    (definition source) (judgment carrier)
    (judgmentHeads_nodup source)
    (List.mem_map_of_mem carrierMembership)

theorem universeAxiom_isValidV1 (carrier : String) :
    RuleSchema.isLocallyValid (universeAxiom carrier) = true := by
  simp [universeAxiom, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, axiomName]

/-- Every generated axiom passes contextual V2 schema validation. -/
theorem universeAxiom_isValidIn (source : ValidatedLanguageDef)
    {carrier : String}
    (carrierMembership : carrier ∈ source.language.typeNames) :
    RuleSchema.isValidIn (definition source) (universeAxiom carrier) = true := by
  unfold RuleSchema.isValidIn
  rw [universeAxiom_isValidV1]
  simp only [Bool.true_and]
  simp only [RuleSchema.patterns, universeAxiom, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true]
  simp only [CalculusLanguageDef.judgmentSchemaValid, List.length_cons,
    List.length_nil, Nat.reduceAdd]
  rw [lookupJudgment source carrierMembership]
  simp only [Option.isSome_some, Bool.true_and]
  simp only [fixedConstructorListsValid, fixedConstructorsValid,
    List.length_nil, Bool.and_true]
  rw [Bool.and_eq_true]
  constructor
  · simpa [definition] using
      universeCode_has_arity_zero source .star carrierMembership
  · simpa [definition] using
      universeCode_has_arity_zero source .box carrierMembership

/-- Generated typing heads are disjoint from generated universe-code
constructor labels. -/
theorem typingHead_not_mem_constructorLabels
    (source : ValidatedLanguageDef) (carrier : String) :
    typingHead carrier ∉
      (CarrierUniverseSignature.language source).terms.map (·.label) := by
  change typingHead carrier ∉
    (CarrierUniverseSignature.terms source).map (·.label)
  rw [CarrierUniverseSignature.termLabels]
  rw [List.mem_flatMap]
  rintro ⟨other, _, localMembership⟩
  have localCases : typingHead carrier =
      CarrierUniverseSignature.label .star other ∨
      typingHead carrier = CarrierUniverseSignature.label .box other := by
    simpa using localMembership
  rcases localCases with equality | equality
  ·
    have decoded := congrArg CarrierUniverseSignature.decode? equality
    simp [typingHead, CarrierUniverseSignature.decode?,
      CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag] at decoded
  ·
    have decoded := congrArg CarrierUniverseSignature.decode? equality
    simp [typingHead, CarrierUniverseSignature.decode?,
      CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag] at decoded

/-- The generated judgment namespace is disjoint from the checker's three
reserved metasyntax heads. -/
theorem typingHead_ne_reserved (carrier : String) :
    typingHead carrier ≠ Pattern.zipHead ∧
      typingHead carrier ≠ Pattern.mapHead ∧
        typingHead carrier ≠ Pattern.evalHead := by
  constructor
  · intro equality
    have lists := congrArg String.toList equality
    simp [typingHead, Pattern.zipHead] at lists
  · constructor
    · intro equality
      have lists := congrArg String.toList equality
      simp [typingHead, Pattern.mapHead] at lists
    · intro equality
      have lists := congrArg String.toList equality
      simp [typingHead, Pattern.evalHead] at lists

/-- The generated per-carrier calculus language passes the generic V2
inference gate for every validated source language. -/
theorem definition_valid (source : ValidatedLanguageDef) :
    (definition source).isValid = true := by
  have baseValid : (definition source).toLanguageDef.validate = [] := by
    exact CarrierUniverseSignature.language_validate source
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [baseValid]
  simp only [List.isEmpty_nil, Bool.true_and]
  have allV1 : (definition source).rules.all RuleSchema.isLocallyValid = true := by
    apply List.all_eq_true.mpr
    intro rule ruleMembership
    change rule ∈ axioms source at ruleMembership
    obtain ⟨carrier, _, rfl⟩ := List.mem_map.mp ruleMembership
    exact universeAxiom_isValidV1 carrier
  rw [allV1]
  simp only [Bool.true_and]
  have uniqueRules :
      (((definition source).ruleIds.eraseDups.length ==
        (definition source).ruleIds.length) = true) := by
    apply (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup
      (definition source).ruleIds).2
    simpa [definition, calculus, CalculusLanguageDef.ruleIds] using
      ruleIds_nodup source
  rw [uniqueRules]
  simp only [Bool.true_and]
  have signatureValid : (definition source).judgmentSignatureValid = true := by
    unfold CalculusLanguageDef.judgmentSignatureValid
    have headsNodup : (definition source).judgmentHeads.Nodup := by
      simpa [definition, calculus, CalculusLanguageDef.judgmentHeads] using
        judgmentHeads_nodup source
    have headsUnique :
        (((definition source).judgmentHeads.eraseDups.length ==
          (definition source).judgmentHeads.length) = true) :=
      (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup
        (definition source).judgmentHeads).2 headsNodup
    rw [Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · apply List.all_eq_true.mpr
        intro declaration declarationMembership
        change declaration ∈ judgments source at declarationMembership
        obtain ⟨carrier, _, rfl⟩ := List.mem_map.mp declarationMembership
        simp [judgment, typingHead]
      · exact headsUnique
    · apply List.all_eq_true.mpr
      intro head headMembership
      have headMembership' : head ∈
          (judgments source).map JudgmentDecl.head := by
        simpa [definition, calculus, CalculusLanguageDef.judgmentHeads] using
          headMembership
      rw [judgmentHeads] at headMembership'
      obtain ⟨carrier, _, rfl⟩ := List.mem_map.mp headMembership'
      have absent := typingHead_not_mem_constructorLabels source carrier
      rw [Bool.and_eq_true]
      constructor
      · rw [Bool.not_eq_true_eq_eq_false, List.any_eq_false]
        intro term termMembership labelsEqualBool
        have labelsEqual : term.label = typingHead carrier := by
          simpa only [beq_iff_eq] using labelsEqualBool
        exact absent (List.mem_map.mpr
          ⟨term, by simpa [definition] using termMembership, labelsEqual⟩)
      · simpa only [List.contains_cons, List.contains_nil, Bool.or_false,
          Bool.not_eq_true_eq_eq_false, Bool.or_eq_false_iff,
          beq_eq_false_iff_ne, ne_eq] using
          typingHead_ne_reserved carrier
  rw [signatureValid]
  simp only [Bool.true_and]
  rw [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro rule ruleMembership
    change rule ∈ axioms source at ruleMembership
    obtain ⟨carrier, carrierMembership, rfl⟩ :=
      List.mem_map.mp ruleMembership
    exact universeAxiom_isValidIn source carrierMembership
  · rfl

/-- Validated per-carrier typing language definition. -/
def validated (source : ValidatedLanguageDef) : ValidatedCalculusLanguageDef :=
  ⟨definition source, definition_valid source⟩

/-! ## Positive and negative controls -/

namespace Canary

private def carrier : TypeDecl :=
  TypeDecl.plain "carrier-typing-canary:Term"

private def sourceLanguage : LanguageDef :=
  { name := "carrier-typing-canary"
    types := [carrier]
    terms := []
    equations := []
    rewrites := [] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sourceLanguage, LanguageDef.typeNames, carrier, TypeDecl.plain]

private def source : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

/-- One carrier contributes one binary typing judgment and one axiom. -/
theorem singleton_counts :
    (definition source).judgments.length = 1 ∧
      (definition source).rules.length = 1 := by
  decide

/-- The generated universe axiom is accepted at its exact stored judgment. -/
theorem singleton_axiom_valid :
    RuleSchema.isValidIn (definition source) (universeAxiom carrier.name) = true := by
  apply universeAxiom_isValidIn (source := source)
  simp [source, sourceLanguage, LanguageDef.typeNames]

/-- A foreign carrier name has no generated typing judgment. -/
theorem foreign_carrier_lookup_fails :
    (definition source).lookupJudgment? (typingHead "foreign") 2 = none := by
  decide

end Canary

#print axioms typingHead_injective
#print axioms typingCarrier?_typingHead
#print axioms typingHead_of_typingCarrier?_eq_some
#print axioms universeCode_has_arity_zero
#print axioms lookupJudgment
#print axioms universeAxiom_isValidIn
#print axioms typingHead_not_mem_constructorLabels
#print axioms definition_valid
#print axioms Canary.singleton_axiom_valid
#print axioms Canary.foreign_carrier_lookup_fails

end CarrierTypingLanguageDef

end Mettapedia.OSLF.Framework
