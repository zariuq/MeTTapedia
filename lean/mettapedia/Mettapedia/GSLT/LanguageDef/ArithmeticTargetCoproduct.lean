import Mettapedia.GSLT.LanguageDef.ExternalCallMachine
import Mettapedia.GSLT.LanguageDef.RadixDigitLanguageDef
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCoproductTyping
import Mettapedia.GSLT.LanguageDef.StructuralPresentationCategory
import Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational

/-!
# Conservative composition of the arithmetic target machines

The external-call and radix-digit machines are independent target languages.
This file constructs their tagged sum, proves it passes the ordinary language
validation gate, and instantiates the semantic coproduct laws.  The result is
the common target object used when legalization selects different target
machines for different operations.
-/

namespace Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproduct

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct

private def tag (prefixText source : String) : String := prefixText ++ source

private theorem tag_injective (prefixText : String) :
    Function.Injective (tag prefixText) := by
  intro left right equality
  apply String.toList_inj.mp
  have listEquality := congrArg String.toList equality
  simp only [tag, String.toList_append] at listEquality
  exact (List.append_right_inj prefixText.toList).mp listEquality

private theorem external_radix_disjoint :
    ∀ externalName radixName,
      tag "E:" externalName ≠ tag "R:" radixName := by
  intro externalName radixName equality
  have listEquality := congrArg String.toList equality
  simp [tag] at listEquality

def externalSymbols : PresentationSymbols where
  sort := tag "E:"
  constructor := tag "E:"
  relation := tag "E:"
  equation := tag "E:"
  rewrite := tag "E:"

def radixSymbols : PresentationSymbols where
  sort := tag "R:"
  constructor := tag "R:"
  relation := tag "R:"
  equation := tag "R:"
  rewrite := tag "R:"

def externalValidated : ValidatedLanguageDef where
  language := ExternalCallMachine.externalCallLanguage
  valid := ExternalCallMachine.externalCallLanguage_validate

def radixValidated : ValidatedLanguageDef where
  language := RadixDigitLanguageDef.language
  valid := RadixDigitLanguageDef.language_validate

def combinedLanguage : LanguageDef :=
  rawCoproduct "ArithmeticTargetMachines" externalSymbols radixSymbols
    ExternalCallMachine.externalCallLanguage RadixDigitLanguageDef.language

@[simp] private theorem combined_constructorLabels :
    combinedLanguage.terms.map (·.label) =
      (ExternalCallMachine.externalCallLanguage.terms.map (·.label)).map
          externalSymbols.constructor ++
        (RadixDigitLanguageDef.language.terms.map (·.label)).map
          radixSymbols.constructor :=
  rawCoproduct_constructorLabels "ArithmeticTargetMachines"
    externalSymbols radixSymbols ExternalCallMachine.externalCallLanguage
    RadixDigitLanguageDef.language

private theorem mappedExternalRewrite_validate_of
    (rewrite : RewriteRule)
    (sourceClean :
      ExternalCallMachine.externalCallLanguage.validateRewrite rewrite = [])
    (leftReferences :
      (mapPattern externalSymbols rewrite.left).constructorRefs =
        rewrite.left.constructorRefs.map fun reference =>
          (externalSymbols.constructor reference.1, reference.2))
    (rightReferences :
      (mapPattern externalSymbols rewrite.right).constructorRefs =
        rewrite.right.constructorRefs.map fun reference =>
          (externalSymbols.constructor reference.1, reference.2))
    (premiseReferences : ∀ pattern ∈
      rewrite.premises.flatMap LanguageDef.premisePatterns,
      (mapPattern externalSymbols pattern).constructorRefs =
        pattern.constructorRefs.map fun reference =>
          (externalSymbols.constructor reference.1, reference.2))
    (wildcardClean :
      LanguageDef.validateRulePatterns
        s!"rewrite {(mapRewriteRule externalSymbols rewrite).name}"
        (combinedLanguage.terms.map (·.label))
        (mapTypeContext externalSymbols rewrite.typeContext)
        (rewrite.premises.map (mapPremise externalSymbols))
        (mapPattern externalSymbols rewrite.left)
        (mapPattern externalSymbols rewrite.right) = []) :
    combinedLanguage.validateRewrite
      (mapRewriteRule externalSymbols rewrite) = [] := by
  unfold LanguageDef.validateRewrite at sourceClean ⊢
  simp only [List.append_eq_nil_iff] at sourceClean ⊢
  rcases sourceClean with
    ⟨⟨⟨⟨sourceTypesClean, sourceLeftClean⟩, sourceRightClean⟩,
      sourcePremisesClean⟩, sourceWildcardClean⟩
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, wildcardClean⟩
  · rw [List.flatMap_eq_nil_iff]
    intro mappedEntry mappedMembership
    obtain ⟨entry, entryMembership, rfl⟩ := List.mem_map.mp mappedMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro mappedName mappedNameMembership
    rw [mapTypeExpr_baseNames] at mappedNameMembership
    obtain ⟨sourceName, sourceNameMembership, rfl⟩ :=
      List.mem_map.mp mappedNameMembership
    rw [show combinedLanguage.typeNames =
        ExternalCallMachine.externalCallLanguage.typeNames.map
            externalSymbols.sort ++
          RadixDigitLanguageDef.language.typeNames.map radixSymbols.sort from
      rawCoproduct_typeNames "ArithmeticTargetMachines" externalSymbols
        radixSymbols ExternalCallMachine.externalCallLanguage
        RadixDigitLanguageDef.language]
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨sourceName, ?_, rfl⟩
    apply LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
      ExternalCallMachine.externalCallLanguage.typeNames
      s!"rewrite {rewrite.name}" entry.2
      ((List.flatMap_eq_nil_iff.mp sourceTypesClean) entry entryMembership)
      sourceNameMembership
  · exact validatePatternConstructors_left_eq_nil
      "ArithmeticTargetMachines" s!"rewrite {rewrite.name} lhs"
      s!"rewrite {(mapRewriteRule externalSymbols rewrite).name} lhs"
      externalSymbols radixSymbols (tag_injective _)
      external_radix_disjoint ExternalCallMachine.externalCallLanguage
      RadixDigitLanguageDef.language rewrite.left leftReferences sourceLeftClean
  · exact validatePatternConstructors_left_eq_nil
      "ArithmeticTargetMachines" s!"rewrite {rewrite.name} rhs"
      s!"rewrite {(mapRewriteRule externalSymbols rewrite).name} rhs"
      externalSymbols radixSymbols (tag_injective _)
      external_radix_disjoint ExternalCallMachine.externalCallLanguage
      RadixDigitLanguageDef.language rewrite.right rightReferences sourceRightClean
  · change
      ((rewrite.premises.map (mapPremise externalSymbols)).flatMap
          LanguageDef.premisePatterns).flatMap
          (LanguageDef.validatePatternConstructors
            s!"rewrite {(mapRewriteRule externalSymbols rewrite).name} premise"
            combinedLanguage.terms) = []
    rw [premisePatterns_mapPremises, List.flatMap_eq_nil_iff]
    intro pattern patternMembership
    obtain ⟨sourcePattern, sourceMembership, rfl⟩ :=
      List.mem_map.mp patternMembership
    exact validatePatternConstructors_left_eq_nil
      "ArithmeticTargetMachines" s!"rewrite {rewrite.name} premise"
      s!"rewrite {(mapRewriteRule externalSymbols rewrite).name} premise"
      externalSymbols radixSymbols (tag_injective _)
      external_radix_disjoint ExternalCallMachine.externalCallLanguage
      RadixDigitLanguageDef.language sourcePattern
      (premiseReferences sourcePattern sourceMembership)
      ((List.flatMap_eq_nil_iff.mp sourcePremisesClean) sourcePattern
        sourceMembership)

private theorem mappedRadixRewrite_validate_of
    (rewrite : RewriteRule)
    (sourceClean : RadixDigitLanguageDef.language.validateRewrite rewrite = [])
    (leftReferences :
      (mapPattern radixSymbols rewrite.left).constructorRefs =
        rewrite.left.constructorRefs.map fun reference =>
          (radixSymbols.constructor reference.1, reference.2))
    (rightReferences :
      (mapPattern radixSymbols rewrite.right).constructorRefs =
        rewrite.right.constructorRefs.map fun reference =>
          (radixSymbols.constructor reference.1, reference.2))
    (premiseReferences : ∀ pattern ∈
      rewrite.premises.flatMap LanguageDef.premisePatterns,
      (mapPattern radixSymbols pattern).constructorRefs =
        pattern.constructorRefs.map fun reference =>
          (radixSymbols.constructor reference.1, reference.2))
    (wildcardClean :
      LanguageDef.validateRulePatterns
        s!"rewrite {(mapRewriteRule radixSymbols rewrite).name}"
        (combinedLanguage.terms.map (·.label))
        (mapTypeContext radixSymbols rewrite.typeContext)
        (rewrite.premises.map (mapPremise radixSymbols))
        (mapPattern radixSymbols rewrite.left)
        (mapPattern radixSymbols rewrite.right) = []) :
    combinedLanguage.validateRewrite (mapRewriteRule radixSymbols rewrite) = [] := by
  unfold LanguageDef.validateRewrite at sourceClean ⊢
  simp only [List.append_eq_nil_iff] at sourceClean ⊢
  rcases sourceClean with
    ⟨⟨⟨⟨sourceTypesClean, sourceLeftClean⟩, sourceRightClean⟩,
      sourcePremisesClean⟩, sourceWildcardClean⟩
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, wildcardClean⟩
  · rw [List.flatMap_eq_nil_iff]
    intro mappedEntry mappedMembership
    obtain ⟨entry, entryMembership, rfl⟩ := List.mem_map.mp mappedMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro mappedName mappedNameMembership
    rw [mapTypeExpr_baseNames] at mappedNameMembership
    obtain ⟨sourceName, sourceNameMembership, rfl⟩ :=
      List.mem_map.mp mappedNameMembership
    rw [show combinedLanguage.typeNames =
        ExternalCallMachine.externalCallLanguage.typeNames.map
            externalSymbols.sort ++
          RadixDigitLanguageDef.language.typeNames.map radixSymbols.sort from
      rawCoproduct_typeNames "ArithmeticTargetMachines" externalSymbols
        radixSymbols ExternalCallMachine.externalCallLanguage
        RadixDigitLanguageDef.language]
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨sourceName, ?_, rfl⟩
    apply LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
      RadixDigitLanguageDef.language.typeNames s!"rewrite {rewrite.name}"
      entry.2 ((List.flatMap_eq_nil_iff.mp sourceTypesClean) entry entryMembership)
      sourceNameMembership
  · exact validatePatternConstructors_right_eq_nil
      "ArithmeticTargetMachines" s!"rewrite {rewrite.name} lhs"
      s!"rewrite {(mapRewriteRule radixSymbols rewrite).name} lhs"
      externalSymbols radixSymbols (tag_injective _)
      external_radix_disjoint ExternalCallMachine.externalCallLanguage
      RadixDigitLanguageDef.language rewrite.left leftReferences sourceLeftClean
  · exact validatePatternConstructors_right_eq_nil
      "ArithmeticTargetMachines" s!"rewrite {rewrite.name} rhs"
      s!"rewrite {(mapRewriteRule radixSymbols rewrite).name} rhs"
      externalSymbols radixSymbols (tag_injective _)
      external_radix_disjoint ExternalCallMachine.externalCallLanguage
      RadixDigitLanguageDef.language rewrite.right rightReferences sourceRightClean
  · change
      ((rewrite.premises.map (mapPremise radixSymbols)).flatMap
          LanguageDef.premisePatterns).flatMap
          (LanguageDef.validatePatternConstructors
            s!"rewrite {(mapRewriteRule radixSymbols rewrite).name} premise"
            combinedLanguage.terms) = []
    rw [premisePatterns_mapPremises, List.flatMap_eq_nil_iff]
    intro pattern patternMembership
    obtain ⟨sourcePattern, sourceMembership, rfl⟩ :=
      List.mem_map.mp patternMembership
    exact validatePatternConstructors_right_eq_nil
      "ArithmeticTargetMachines" s!"rewrite {rewrite.name} premise"
      s!"rewrite {(mapRewriteRule radixSymbols rewrite).name} premise"
      externalSymbols radixSymbols (tag_injective _)
      external_radix_disjoint ExternalCallMachine.externalCallLanguage
      RadixDigitLanguageDef.language sourcePattern
      (premiseReferences sourcePattern sourceMembership)
      ((List.flatMap_eq_nil_iff.mp sourcePremisesClean) sourcePattern
        sourceMembership)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
private theorem mappedExternalRewrites_validate :
    ∀ rewrite ∈ ExternalCallMachine.externalCallLanguage.rewrites,
      combinedLanguage.validateRewrite
        (mapRewriteRule externalSymbols rewrite) = [] := by
  intro rewrite membership
  have sourceClean :=
    LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
      ExternalCallMachine.externalCallLanguage
      ExternalCallMachine.externalCallLanguage_validate rewrite membership
  change rewrite ∈ ExternalCallMachine.externalCallLanguageTransitions at membership
  simp only [ExternalCallMachine.externalCallLanguageTransitions,
    List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply mappedExternalRewrite_validate_of
    · exact sourceClean
    all_goals
      simp [combined_constructorLabels, externalSymbols, radixSymbols, tag,
        mapRewriteRule, mapTypeContext, mapPremise, mapPattern,
        mapPatternList,
        ExternalCallMachine.externalCallLanguage,
        ExternalCallMachine.externalCallLanguageTransitions,
        ExternalCallMachine.ctor, ExternalCallMachine.typed,
        ExternalCallMachine.v, ExternalCallMachine.a,
        ExternalCallMachine.query, ExternalCallMachine.run,
        ExternalCallMachine.halted, ExternalCallMachine.stepReceipt,
        ExternalCallMachine.externalReceipt,
        ExternalCallMachine.commonContext,
        ExternalCallMachine.consumeFuel, ExternalCallMachine.fetch,
        ExternalCallMachine.branchRule, ExternalCallMachine.callRule,
        ExternalCallMachine.returnFaultRule,
        ExternalCallMachine.fuelExhaustedRule,
        ExternalCallMachine.branchZeroTransition,
        ExternalCallMachine.branchNonzeroTransition,
        ExternalCallMachine.callValueTransition,
        ExternalCallMachine.callLanguageFaultTransition,
        ExternalCallMachine.callEngineFaultTransition,
        ExternalCallMachine.callResourceFaultTransition,
        ExternalCallMachine.returnValueTransition,
        ExternalCallMachine.returnDeclinedTransition,
        ExternalCallMachine.returnLanguageFaultTransition,
        ExternalCallMachine.returnEngineFaultTransition,
        ExternalCallMachine.returnResourceFaultTransition,
        RadixDigitLanguageDef.language, RadixDigitLanguageDef.terms,
        RadixDigitLanguageDef.instructionTerms, RadixDigitLanguageDef.ctor,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
        LanguageDef.premiseFvarNames,
        LanguageDef.premiseProducedFvarNames,
        LanguageDef.premiseForAllParams, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
private theorem mappedRadixRewrites_validate :
    ∀ rewrite ∈ RadixDigitLanguageDef.language.rewrites,
      combinedLanguage.validateRewrite
        (mapRewriteRule radixSymbols rewrite) = [] := by
  intro rewrite membership
  have sourceClean :=
    LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
      RadixDigitLanguageDef.language RadixDigitLanguageDef.language_validate
      rewrite membership
  change rewrite ∈ RadixDigitLanguageDef.transitions at membership
  simp only [RadixDigitLanguageDef.transitions, List.mem_cons,
    List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply mappedRadixRewrite_validate_of
    · exact sourceClean
    all_goals
      simp [combined_constructorLabels, externalSymbols, radixSymbols, tag,
        mapRewriteRule, mapTypeContext, mapPremise, mapPattern,
        mapPatternList,
        ExternalCallMachine.externalCallLanguage, ExternalCallMachine.ctor,
        RadixDigitLanguageDef.language, RadixDigitLanguageDef.transitions,
        RadixDigitLanguageDef.terms, RadixDigitLanguageDef.instructionTerms,
        RadixDigitLanguageDef.ctor, RadixDigitLanguageDef.typed,
        RadixDigitLanguageDef.v, RadixDigitLanguageDef.a,
        RadixDigitLanguageDef.query, RadixDigitLanguageDef.run,
        RadixDigitLanguageDef.halted, RadixDigitLanguageDef.commonContext,
        RadixDigitLanguageDef.executeReceipt,
        RadixDigitLanguageDef.fetchedPremises,
        RadixDigitLanguageDef.nextTransition,
        RadixDigitLanguageDef.valueTransition,
        RadixDigitLanguageDef.faultTransition,
        RadixDigitLanguageDef.languageFaultTransition,
        RadixDigitLanguageDef.engineFaultTransition,
        RadixDigitLanguageDef.resourceFaultTransition,
        RadixDigitLanguageDef.missingProgramCounterTransition,
        RadixDigitLanguageDef.fuelExhaustedTransition,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
        LanguageDef.premiseFvarNames,
        LanguageDef.premiseProducedFvarNames,
        LanguageDef.premiseForAllParams, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem combinedLanguage_validate : combinedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndCertifiedRewrites
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold combinedLanguage rawCoproduct renameLanguage externalSymbols radixSymbols tag
    decide +kernel
  · unfold LanguageDef.rewriteRowsValid
    simp only [List.all_eq_true]
    intro rewrite membership
    apply List.isEmpty_iff.mpr
    change rewrite ∈
      (ExternalCallMachine.externalCallLanguage.rewrites.map
        (mapRewriteRule externalSymbols) ++
       RadixDigitLanguageDef.language.rewrites.map
        (mapRewriteRule radixSymbols)) at membership
    rcases List.mem_append.mp membership with leftMembership | rightMembership
    · obtain ⟨source, sourceMembership, rfl⟩ := List.mem_map.mp leftMembership
      exact mappedExternalRewrites_validate source sourceMembership
    · obtain ⟨source, sourceMembership, rfl⟩ := List.mem_map.mp rightMembership
      exact mappedRadixRewrites_validate source sourceMembership

private theorem externalRewritesRooted :
    ∀ rewrite ∈ externalValidated.language.rewrites,
      ConstructorRooted rewrite := by
  intro rewrite membership
  change rewrite ∈ ExternalCallMachine.externalCallLanguageTransitions at membership
  simp only [ExternalCallMachine.externalCallLanguageTransitions, List.mem_cons,
    List.mem_nil_iff, or_false] at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [ConstructorRooted, ExternalCallMachine.fuelExhaustedRule,
      ExternalCallMachine.branchZeroTransition,
      ExternalCallMachine.branchNonzeroTransition,
      ExternalCallMachine.callValueTransition,
      ExternalCallMachine.callLanguageFaultTransition,
      ExternalCallMachine.callEngineFaultTransition,
      ExternalCallMachine.callResourceFaultTransition,
      ExternalCallMachine.returnValueTransition,
      ExternalCallMachine.returnDeclinedTransition,
      ExternalCallMachine.returnLanguageFaultTransition,
      ExternalCallMachine.returnEngineFaultTransition,
      ExternalCallMachine.returnResourceFaultTransition,
      ExternalCallMachine.branchRule, ExternalCallMachine.callRule,
      ExternalCallMachine.returnFaultRule, ExternalCallMachine.run,
      ExternalCallMachine.a]

private theorem radixRewritesRooted :
    ∀ rewrite ∈ radixValidated.language.rewrites,
      ConstructorRooted rewrite := by
  intro rewrite membership
  change rewrite ∈ RadixDigitLanguageDef.transitions at membership
  simp only [RadixDigitLanguageDef.transitions, List.mem_cons,
    List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [ConstructorRooted, RadixDigitLanguageDef.fuelExhaustedTransition,
      RadixDigitLanguageDef.missingProgramCounterTransition,
      RadixDigitLanguageDef.nextTransition,
      RadixDigitLanguageDef.valueTransition,
      RadixDigitLanguageDef.languageFaultTransition,
      RadixDigitLanguageDef.engineFaultTransition,
      RadixDigitLanguageDef.resourceFaultTransition,
      RadixDigitLanguageDef.faultTransition,
      RadixDigitLanguageDef.run, RadixDigitLanguageDef.a]

def compatibility :
    Compatibility "ArithmeticTargetMachines" externalSymbols radixSymbols
      externalValidated radixValidated where
  leftSymbolsInjective := {
    sort := tag_injective _
    constructor := tag_injective _
    relation := tag_injective _
    equation := tag_injective _
    rewrite := tag_injective _ }
  rightSymbolsInjective := {
    sort := tag_injective _
    constructor := tag_injective _
    relation := tag_injective _
    equation := tag_injective _
    rewrite := tag_injective _ }
  symbolImagesDisjoint := {
    sort := external_radix_disjoint
    constructor := external_radix_disjoint
    relation := external_radix_disjoint
    equation := external_radix_disjoint
    rewrite := external_radix_disjoint }
  leftRewritesRooted := externalRewritesRooted
  rightRewritesRooted := radixRewritesRooted
  typeNamesNodup :=
    LanguageDef.typeNames_nodup_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
  constructorNamesNodup :=
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
  equationNamesNodup :=
    LanguageDef.equationNames_nodup_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
  rewriteNamesNodup :=
    LanguageDef.rewriteNames_nodup_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
  leftTermsStable := by
    intro term membership
    apply LanguageDef.validateTerm_eq_nil_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨term, membership, rfl⟩)
  rightTermsStable := by
    intro term membership
    apply LanguageDef.validateTerm_eq_nil_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨term, membership, rfl⟩)
  leftEquationsStable := by
    intro equation membership
    apply LanguageDef.validateEquation_eq_nil_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  rightEquationsStable := by
    intro equation membership
    apply LanguageDef.validateEquation_eq_nil_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  leftRewritesStable := by
    intro rewrite membership
    apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨rewrite, membership, rfl⟩)
  rightRewritesStable := by
    intro rewrite membership
    apply LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil combinedLanguage
      combinedLanguage_validate
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨rewrite, membership, rfl⟩)

def presentation : ValidatedLanguageDef := compatibility.presentation

set_option maxRecDepth 100000 in
theorem wire_isSome :
    (CanonicalWire.renderLanguage? presentation.language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? presentation.language).getD ""

theorem wire_nonempty : wire != "" := by decide +kernel

/-- Exact transport for the deliberately premise-free root executor.  The
premise-aware contextual theorem is `Compatibility.left_rewriteAt_exact`; its
inhabited arithmetic-target instances live in `ArithmeticTargetCoproductNTT`. -/
theorem external_premiseFreeStep_exact (term : Pattern) :
    rewriteStep presentation.language (mapPattern externalSymbols term) =
      (rewriteStep externalValidated.language term).map
        (mapPattern externalSymbols) :=
  compatibility.left_rewriteStep_exact term

/-- Symmetric exact transport for the premise-free root executor. -/
theorem radix_premiseFreeStep_exact (term : Pattern) :
    rewriteStep presentation.language (mapPattern radixSymbols term) =
      (rewriteStep radixValidated.language term).map
        (mapPattern radixSymbols) :=
  compatibility.right_rewriteStep_exact term

theorem external_typing_exact
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (term : Pattern) (expected : TypeExpr) :
    WellSorted.checkHasType presentation.language (free.map externalSymbols)
        (bound.map (mapTypeExpr externalSymbols))
        (mapPattern externalSymbols term) (mapTypeExpr externalSymbols expected) =
      WellSorted.checkHasType externalValidated.language free bound term expected :=
  StructuralCoproductTyping.left_checkHasType_exact compatibility
    free bound term expected

theorem radix_typing_exact
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (term : Pattern) (expected : TypeExpr) :
    WellSorted.checkHasType presentation.language (free.map radixSymbols)
        (bound.map (mapTypeExpr radixSymbols))
        (mapPattern radixSymbols term) (mapTypeExpr radixSymbols expected) =
      WellSorted.checkHasType radixValidated.language free bound term expected :=
  StructuralCoproductTyping.right_checkHasType_exact compatibility
    free bound term expected

noncomputable def categoricalCoproduct :=
  StructuralPresentationCategory.Coproduct.isColimit compatibility

#print axioms combinedLanguage_validate
#print axioms wire_isSome
#print axioms external_premiseFreeStep_exact
#print axioms radix_premiseFreeStep_exact
#print axioms external_typing_exact
#print axioms categoricalCoproduct

end Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproduct
