import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus

/-!
# Guarded source-preserving selected native-type calculus

This construction replaces the unguarded occurrence suffix when authored
rewrites carry relation premises.  It composes the selected modal signature,
authored endpoint-carrier support, exact occurrence-step formulas, canonical
context certificates, and guard-retaining formation/introduction rules.

The output is one ordinary flat calculus.  Authored source rows remain a
literal prefix, while the generated typing layer contributes no object
equation or operational rewrite.  Semantic soundness remains a separate
obligation against independently supplied relation and occurrence meaning.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction

/-- Ordered guarded extension over an authored source language. -/
def extension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (_separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) : CalculusLanguageExtension :=
  (SelectedNativeTypeSourceIndexedCalculus.signatureExtension demand).comp
    ((SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).comp
      ((SelectedNativeTypeOccurrenceStepClaim.extension demand).comp
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension
          demand profile)))

/-- One flat source-plus-guarded-native calculus before concrete admission. -/
def definition {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) : CalculusLanguageDef :=
  (extension demand separated profile).apply
    (SourcePreservingCalculusCoproduct.sourceBase source)

@[simp] theorem definition_types {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    (definition demand separated profile).types =
      source.language.types ++
        (SelectedNativeTypeContextualCalculus.signature demand).types ++
          (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTypes := by
  simp [definition, extension,
    SelectedNativeTypeSourceIndexedCalculus.signatureExtension,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp]

@[simp] theorem definition_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    (definition demand separated profile).terms =
      source.language.terms ++
        (SelectedNativeTypeContextualCalculus.signature demand).terms ++
          (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newTerms ++
            SelectedNativeTypeOccurrenceStepClaim.terms demand ++
              familyApplicationTerms demand ++
                SelectedNativeTypeAuthoredVariableClaim.terms demand ++
                  SelectedNativeTypeBoundRelationClaim.terms profile := by
  simp [definition, extension,
    SelectedNativeTypeSourceIndexedCalculus.signatureExtension,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp, List.append_assoc]

@[simp] theorem definition_judgments {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    (definition demand separated profile).judgments =
      (SelectedNativeTypeContextualCalculus.signature demand).judgments ++
        (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newJudgments := by
  simp [definition, extension,
    SelectedNativeTypeSourceIndexedCalculus.signatureExtension,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty]

@[simp] theorem definition_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    (definition demand separated profile).rules =
      (SelectedNativeTypeContextualCalculus.signature demand).rules ++
        (SelectedNativeTypeSourceIndexedCarrierSupport.extension demand).newRules ++
          profiledRules demand profile := by
  simp [definition, extension,
    SelectedNativeTypeSourceIndexedCalculus.signatureExtension,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty, List.append_assoc]

/-- Operational erasure recovers the authored rewrite table exactly and in
authored order. -/
@[simp] theorem definition_rewrites {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    (definition demand separated profile).rewrites = source.language.rewrites := by
  simp [definition, extension,
    SelectedNativeTypeSourceIndexedCalculus.signatureExtension,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty,
    SelectedNativeTypeSourceIndexedCalculus.signature_rewrites_empty,
    SelectedNativeTypeSourceIndexedCarrierSupport.extension_rewrites_empty]

/-- The guarded proof layer introduces no object equation. -/
@[simp] theorem definition_equations {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) :
    (definition demand separated profile).equations = source.language.equations := by
  simp [definition, extension,
    SelectedNativeTypeSourceIndexedCalculus.signatureExtension,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.profileExtension,
    SourcePreservingCalculusCoproduct.sourceBase,
    CalculusLanguageExtension.comp,
    InferenceExtension.ProofCalculus.empty,
    SelectedNativeTypeSourceIndexedCalculus.signature_equations_empty,
    SelectedNativeTypeSourceIndexedCarrierSupport.extension_equations_empty]

/-- Exact finite obligations for admitting the guarded composite. -/
structure Compatibility {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand) : Prop where
  disjoint : (extension demand separated profile).disjointFrom
    (SourcePreservingCalculusCoproduct.sourceBase source) = true
  policy : (extension demand separated profile).policyHolds
    (SourcePreservingCalculusCoproduct.sourceBase source)
      (.extendsBaseJudgments [ContextualInference.contextualJudgment.head]) = true
  valid : (definition demand separated profile).isValid = true

namespace Compatibility

variable {source : ValidatedLanguageDef}
  {demand : SelectedNativeTypeDemand source}
  {separated : SupportSeparatedDemand demand}
  {profile : PremiseProfile demand}

/-- Admitted guarded flat calculus. -/
def target (compatible : Compatibility demand separated profile) :
    ValidatedCalculusLanguageDef :=
  ⟨definition demand separated profile, compatible.valid⟩

/-- Checked extension with explicit authority to add proofs of the shared
contextual judgment. -/
def validatedExtension (compatible : Compatibility demand separated profile) :
    ValidatedCalculusLanguageExtension
      (SourcePreservingCalculusCoproduct.validatedSourceBase source) where
  extension := extension demand separated profile
  policy := .extendsBaseJudgments [ContextualInference.contextualJudgment.head]
  disjoint := compatible.disjoint
  policyHolds := compatible.policy
  valid := compatible.valid

/-- Authored source rows embed literally in the guarded target. -/
def sourceInclusion (compatible : Compatibility demand separated profile) :
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
    change declaration ∈ (definition demand separated profile).equations
    rw [definition_equations]
    exact membership
  mapsRewrites declaration membership := by
    rw [mapRewriteRule_id]
    change declaration ∈ (definition demand separated profile).rewrites
    rw [definition_rewrites]
    exact membership

theorem target_rewrites
    (compatible : Compatibility demand separated profile) :
    compatible.target.1.rewrites = source.language.rewrites :=
  definition_rewrites demand separated profile

theorem target_equations
    (compatible : Compatibility demand separated profile) :
    compatible.target.1.equations = source.language.equations :=
  definition_equations demand separated profile

end Compatibility

#print axioms definition_rewrites
#print axioms definition_equations
#print axioms Compatibility.sourceInclusion

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus
