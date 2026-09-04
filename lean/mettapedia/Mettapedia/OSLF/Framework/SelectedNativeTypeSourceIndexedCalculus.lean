import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
import Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct

/-!
# Source-preserving selected native-type calculus

The selected native-type construction has two different dependencies.  Its
carrier, universe, modal, context, and judgment signature depends only on the
finite native-type demand.  Its introduction rules additionally depend on the
exact authored rewrite occurrences selected by that demand.  This module
composes those two layers as ordered `CalculusLanguageExtension`s over the
authored source language.

The result is one ordinary flat calculus language.  Source object rows remain
literal prefixes, generated signature rows follow them, and source-indexed
formation/introduction rows form the final suffix.  Validation happens only
after all three pieces have been attached, because the final rules mention
both authored constructors and generated typing constructors.

Elimination is not part of this construction.  It can be added only after its
binder and eigenvariable support has an independently checked formulation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction

/-- Source-independent rows of the generated selected-native signature.  The
conversion root is intentionally not copied: conversion is global authority,
not an appendable row family. -/
def signatureExtension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageExtension :=
  let generated := SelectedNativeTypeContextualCalculus.signature demand
  { newTypes := generated.types
    newTerms := generated.terms
    newEquations := generated.equations
    newRewrites := generated.rewrites
    newJudgments := generated.judgments
    newRules := generated.rules
    rename := some generated.name }

/-- Ordered composite of the independent generated signature and the
source-indexed occurrence-step signature and sound rule fragment. -/
def extension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) : CalculusLanguageExtension :=
  (signatureExtension demand).comp
    ((SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).comp
      ((SelectedNativeTypeOccurrenceStepClaim.extension demand).comp
        (SelectedNativeTypeSourceIndexedIntroduction.profileExtension
          demand separated)))

/-- One flat source-plus-selected-native calculus before admission evidence
is attached. -/
def definition {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) : CalculusLanguageDef :=
  (extension demand separated).apply
    (SourcePreservingCalculusCoproduct.sourceBase source)

@[simp] theorem definition_types {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    (definition demand separated).types =
      source.language.types ++
        (SelectedNativeTypeContextualCalculus.signature demand).types ++
          (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTypes := by
  simp [definition, extension, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp]

@[simp] theorem definition_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    (definition demand separated).terms =
      source.language.terms ++
        (SelectedNativeTypeContextualCalculus.signature demand).terms ++
          (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms ++
            SelectedNativeTypeOccurrenceStepClaim.terms demand ++
              familyApplicationTerms demand := by
  simp [definition, extension, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp, List.append_assoc]

@[simp] theorem definition_judgments {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    (definition demand separated).judgments =
      (SelectedNativeTypeContextualCalculus.signature demand).judgments ++
        (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newJudgments := by
  simp [definition, extension, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty]

@[simp] theorem definition_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    (definition demand separated).rules =
      (SelectedNativeTypeContextualCalculus.signature demand).rules ++
        (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newRules ++
          SelectedNativeTypeSourceIndexedIntroduction.profiledRules demand := by
  simp [definition, extension, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty]

/-- The source-independent generated signature is proof-only. -/
theorem signature_rewrites_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (SelectedNativeTypeContextualCalculus.signature demand).rewrites = [] := by
  rw [SelectedNativeTypeContextualCalculus.signature,
    ContextualCarrierClaims.apply_rewrites]
  have preserved :=
    (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      demand.foundation).rewrites
  simpa [ContextualModalExtension.language,
    ContextualModalExtension.extension, ConstructorTermExtension.ofList,
    SelectedNativeTypeFoundation.definition_rewrites] using preserved

/-- The source-independent generated signature introduces no object
equation. -/
theorem signature_equations_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (SelectedNativeTypeContextualCalculus.signature demand).equations = [] := by
  rw [SelectedNativeTypeContextualCalculus.signature,
    ContextualCarrierClaims.apply_equations]
  have preserved :=
    (ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
      demand.foundation).equations
  simpa [ContextualModalExtension.language,
    ContextualModalExtension.extension, ConstructorTermExtension.ofList,
    SelectedNativeTypeFoundation.definition_equations] using preserved

/-- The generated typing layer contributes no operational rewrite.  Erasing
proof search therefore recovers the exact authored transition table, in
authored order. -/
@[simp] theorem definition_rewrites {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    (definition demand separated).rewrites = source.language.rewrites := by
  simp [definition, extension, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty,
    signature_rewrites_empty,
    SelectedNativeTypeSourceIndexedCarrierSupport.extension_rewrites_empty]

/-- The same proof-only attachment preserves every authored equation. -/
@[simp] theorem definition_equations {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) :
    (definition demand separated).equations = source.language.equations := by
  simp [definition, extension, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty,
    signature_equations_empty,
    SelectedNativeTypeSourceIndexedCarrierSupport.extension_equations_empty]

/-- Exact finite obligations for admitting the source-indexed composite. -/
structure Compatibility {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand) : Prop where
  disjoint : (extension demand separated).disjointFrom
    (SourcePreservingCalculusCoproduct.sourceBase source) = true
  policy : (extension demand separated).policyHolds
    (SourcePreservingCalculusCoproduct.sourceBase source)
      .newJudgmentsOnly = true
  valid : (definition demand separated).isValid = true

namespace Compatibility

variable {source : ValidatedLanguageDef}
  {demand : SelectedNativeTypeDemand source}
  {separated : SupportSeparatedDemand demand}

/-- The admitted flat selected-native calculus. -/
def target (compatible : Compatibility demand separated) :
    ValidatedCalculusLanguageDef :=
  ⟨definition demand separated, compatible.valid⟩

/-- The construction is an ordinary checked extension of the authored
source's empty proof fibre. -/
def validatedExtension (compatible : Compatibility demand separated) :
    ValidatedCalculusLanguageExtension
      (SourcePreservingCalculusCoproduct.validatedSourceBase source) where
  extension := extension demand separated
  policy := .newJudgmentsOnly
  disjoint := compatible.disjoint
  policyHolds := compatible.policy
  valid := compatible.valid

/-- The authored source embeds without renaming.  Its rows are literal
prefixes of the generated target. -/
def sourceInclusion (compatible : Compatibility demand separated) :
    StructuralMorphism source compatible.target.toValidatedLanguageDef where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    rw [mapEquation_id]
    change declaration ∈ (definition demand separated).equations
    rw [definition_equations]
    exact membership
  mapsRewrites declaration membership := by
    rw [mapRewriteRule_id]
    change declaration ∈ (definition demand separated).rewrites
    rw [definition_rewrites]
    exact membership

theorem target_rewrites (compatible : Compatibility demand separated) :
    compatible.target.1.rewrites = source.language.rewrites :=
  definition_rewrites demand separated

theorem target_equations (compatible : Compatibility demand separated) :
    compatible.target.1.equations = source.language.equations :=
  definition_equations demand separated

end Compatibility

/-! ## Discriminating attached-language witness -/

namespace Canary

open SelectedNativeTypeContextualCalculus.Canary
open SelectedNativeTypeSourceIndexedIntroduction.Canary
open ContextualModalSignature.Canary

/-- The non-root two-rely example is an actual source-preserving composite,
not merely a locally valid detached rule. -/
def middleDefinition : CalculusLanguageDef :=
  definition (middleDemand .star) middle_supportSeparated

private theorem middleCompiler_eq_grouped :
    ContextualModalSignatureCompiler.definition
        (middleDemand .star).foundation =
      ContextualModalExtension.language (middleDemand .star).foundation := by
  have foundationEq :
      (middleDemand .star).foundation =
        ContextualModalSignatureCompiler.singleton
          (middleOccurrence .star).groundedOccurrence := by
    apply SelectedNativeTypeFoundation.Demand.ext
    rfl
  rw [foundationEq, singletonCompiler_eq_grouped]

theorem middle_rewrites_exact :
    middleDefinition.rewrites =
      ContextualModalSignature.Canary.source.language.rewrites := by
  exact definition_rewrites _ _

private theorem middle_baseCarrierRoots :
    (middleDemand .star).foundation.carrierObjects.roots =
      [ .base termType.name, .base termType.name
      , .base termType.name, .base termType.name ] := by
  unfold SelectedNativeTypeDemand.foundation
    SelectedNativeTypeFoundation.Demand.carrierObjects
    SelectedNativeTypeFoundation.Demand.carrierRoots
    SelectedNativeTypeFoundation.requiredCarrierRoots
    DisplayedContextProfile.carrierTypes
  simp only [middleDemand, middleOccurrence,
    ProfiledRewriteOccurrence.constant, List.map_singleton,
    List.flatMap_singleton]
  rw [middle_occurrence_dependencies_exact]
  rfl

private theorem middle_authoredCarrierRoots :
    (SelectedNativeTypeSourceIndexedCarrierSupport.authoredRequest
      (middleDemand .star)).roots =
      [.base termType.name, .base termType.name, .base termType.name] := by
  simp [SelectedNativeTypeSourceIndexedCarrierSupport.authoredRequest,
    SelectedNativeTypeSourceIndexedCarrierSupport.authoredRoots,
    middleDemand, middleOccurrence, ProfiledRewriteOccurrence.constant]

private theorem middle_augmentedCarrierObjects :
    (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
      (middleDemand .star)).objects = [.base termType.name] := by
  unfold SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
    CarrierObjectClosure.Request.objects
  rw [CarrierObjectClosure.Request.append_roots, middle_baseCarrierRoots,
    middle_authoredCarrierRoots]
  rfl

private theorem middle_carrierExtension_types_empty :
    (SelectedNativeTypeSourceIndexedCarrierSupport.carrierExtension
      (middleDemand .star)).newTypes = [] := by
  unfold SelectedNativeTypeSourceIndexedCarrierSupport.carrierExtension
    CarrierObjectLanguageDef.indexedAppendExtension
    CalculusLanguageExtension.AppendOnlyCalculusRefinement.residual
  change
    (CarrierObjectLanguageDef.indexedDefinition
      (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
        (middleDemand .star))).types.drop
        (CarrierObjectLanguageDef.indexedDefinition
          (middleDemand .star).foundation.carrierObjects).types.length = []
  simp [CarrierObjectLanguageDef.indexedDefinition,
    CarrierObjectLanguageDef.definition_types,
    CarrierObjectLanguageDef.carrierTypes,
    CarrierObjectLanguageDef.Naming.indexed, middle_augmentedCarrierObjects,
    middle_carrier_objects]

private theorem middle_carrierExtension_rules_empty :
    (SelectedNativeTypeSourceIndexedCarrierSupport.carrierExtension
      (middleDemand .star)).newRules = [] := by
  unfold SelectedNativeTypeSourceIndexedCarrierSupport.carrierExtension
    CarrierObjectLanguageDef.indexedAppendExtension
    CalculusLanguageExtension.AppendOnlyCalculusRefinement.residual
  change
    (CarrierObjectLanguageDef.indexedDefinition
      (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
        (middleDemand .star))).rules.drop
        (CarrierObjectLanguageDef.indexedDefinition
          (middleDemand .star).foundation.carrierObjects).rules.length = []
  simp [CarrierObjectLanguageDef.indexedDefinition,
    CarrierObjectLanguageDef.definition_rules,
    CarrierObjectLanguageDef.carrierTypes,
    CarrierObjectLanguageDef.Naming.indexed, middle_augmentedCarrierObjects,
    middle_carrier_objects]

/-- Repeated endpoint carriers do not emit duplicate carrier or claim rows. -/
theorem middle_sourceCarrierSupport_rules_empty :
    (SelectedNativeTypeSourceIndexedCarrierSupport.extension
      (middleDemand .star)).newRules = [] := by
  simp [SelectedNativeTypeSourceIndexedCarrierSupport.extension,
    SelectedNativeTypeSourceIndexedCarrierSupport.claimExtension,
    SelectedNativeTypeSourceIndexedCarrierSupport.additionalCarrierNames,
    ContextualCarrierClaims.carrierExtension,
    ContextualCarrierClaims.bridgeRules,
    CalculusLanguageExtension.comp, middle_carrierExtension_types_empty,
    middle_carrierExtension_rules_empty]

theorem middle_rule_inventory : middleDefinition.rules.length = 6 := by
  change
    (definition (middleDemand .star) middle_supportSeparated).rules.length = 6
  simp only [definition, CalculusLanguageExtension.apply_rules,
    extension, CalculusLanguageExtension.comp, signatureExtension,
    SelectedNativeTypeSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageDef.extend_rules,
    InferenceExtension.ProofCalculus.empty]
  rw [middle_sourceCarrierSupport_rules_empty]
  rw [SelectedNativeTypeContextualCalculus.signature,
    ContextualCarrierClaims.apply_rules, middleCompiler_eq_grouped,
    ContextualModalExtension.language_rules,
    SelectedNativeTypeFoundation.definition_rules,
    middle_stableCarrierNames]
  simp [ContextualCarrierClaims.bridgeRules,
    ContextualInferenceCanonicalContext.extension,
    SelectedNativeTypeSourceIndexedIntroduction.profiledRules,
    SelectedNativeTypeSourceIndexedIntroduction.rulesAt, middleDemand]

end Canary

#print axioms definition_rewrites
#print axioms Compatibility.sourceInclusion
#print axioms Canary.middle_rule_inventory

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus
