import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedValidation

/-!
# Generator origins for guarded source-indexed rules

The guarded selected-native calculus is assembled from several append-only
rule families.  Semantic proofs should follow those generators rather than
enumerating the completed rule table.  This module gives every stored rule an
exact family origin and lifts that classification to arbitrary checker
applications.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedRuleOrigin

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction

/-- Complete carrier-name inventory of the source-preserving calculus. -/
def carrierNames {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List String :=
  SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
    SelectedNativeTypeSourceIndexedCarrierSupport.additionalCarrierNames demand

/-- Exact generator family which contributed one stored rule. -/
inductive RuleOrigin {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) : RuleSchema → Prop where
  | universe (carrier : String) (membership : carrier ∈ carrierNames demand) :
      RuleOrigin demand profile
        (CarrierTypingLanguageDef.universeAxiom carrier)
  | canonicalNil :
      RuleOrigin demand profile
        ContextualInferenceCanonicalContext.nilRule
  | canonicalCons :
      RuleOrigin demand profile
        ContextualInferenceCanonicalContext.consRule
  | carrierBridge (carrier : String)
      (membership : carrier ∈ carrierNames demand) :
      RuleOrigin demand profile
        (ContextualCarrierClaims.liftTypingRule carrier)
  | formation (slot : Occurrence demand) :
      RuleOrigin demand profile
        (ContextualInference.lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
            demand slot))
  | introduction (slot : Occurrence demand) :
      RuleOrigin demand profile
        (ContextualInference.lowerRule
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            profile slot))

/-- Every rule in the flat guarded calculus has an exact generator origin.
The proof follows the append structure of the generators and does not inspect
the completed concrete rule array. -/
theorem origin_of_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    {rule : RuleSchema}
    (membership : rule ∈
      (SelectedNativeTypeGuardedSourceIndexedCalculus.definition
        demand separated profile).rules) :
    RuleOrigin demand profile rule := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_rules]
    at membership
  rcases List.mem_append.mp membership with prefixMembership | profiledMembership
  · rcases List.mem_append.mp prefixMembership with
      signatureMembership | carrierSuffixMembership
    · rw [SelectedNativeTypeSourceIndexedValidation.signature_rules]
        at signatureMembership
      rcases List.mem_append.mp signatureMembership with
        signaturePrefixMembership | bridgeMembership
      · rcases List.mem_append.mp signaturePrefixMembership with
          universeMembership | canonicalMembership
        · obtain ⟨carrier, carrierMembership, rfl⟩ :=
            List.mem_map.mp universeMembership
          exact .universe carrier
            (List.mem_append_left _ carrierMembership)
        · have classified :
            rule = ContextualInferenceCanonicalContext.nilRule ∨
              rule = ContextualInferenceCanonicalContext.consRule := by
            simpa [ContextualInferenceCanonicalContext.extension] using
              canonicalMembership
          rcases classified with rfl | rfl
          · exact .canonicalNil
          · exact .canonicalCons
      · unfold ContextualCarrierClaims.bridgeRules at bridgeMembership
        obtain ⟨carrier, carrierMembership, rfl⟩ :=
          List.mem_map.mp bridgeMembership
        exact .carrierBridge carrier
          (List.mem_append_left _ carrierMembership)
    · rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_rules]
        at carrierSuffixMembership
      rcases List.mem_append.mp carrierSuffixMembership with
        universeMembership | bridgeMembership
      · obtain ⟨carrier, carrierMembership, rfl⟩ :=
          List.mem_map.mp universeMembership
        exact .universe carrier
          (List.mem_append_right _ carrierMembership)
      · unfold ContextualCarrierClaims.bridgeRules at bridgeMembership
        obtain ⟨carrier, carrierMembership, rfl⟩ :=
          List.mem_map.mp bridgeMembership
        exact .carrierBridge carrier
          (List.mem_append_right _ carrierMembership)
  · rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules]
      at profiledMembership
    obtain ⟨row, rowMembership, ruleMembership⟩ :=
      List.mem_flatten.mp profiledMembership
    obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
    have classified :
        rule = ContextualInference.lowerRule
            (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
              demand slot) ∨
          rule = ContextualInference.lowerRule
            (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
              profile slot) := by
      simpa [SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt] using
        ruleMembership
    rcases classified with rfl | rfl
    · exact .formation slot
    · exact .introduction slot

/-- Every admitted application selects a rule with generator provenance.
The result retains the exact successful lookup used by the checker. -/
theorem application_has_origin {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : PremiseProfile demand)
    {definition : ValidatedCalculusLanguageDef}
    (definitionExact : definition.1 =
      SelectedNativeTypeGuardedSourceIndexedCalculus.definition
        demand separated profile)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication definition ruleInstance premises conclusion) :
    ∃ rule,
      definition.1.lookupRule? ruleInstance.ruleId = some rule ∧
        RuleOrigin demand profile rule := by
  cases application with
  | intro rule lookup _argumentsValid _sideConditionsValid
      _premisesInstantiate _conclusionInstantiates =>
      refine ⟨rule, lookup, ?_⟩
      apply origin_of_mem demand separated profile
      have stored : rule ∈ definition.1.rules :=
        List.mem_of_find?_eq_some lookup
      simpa [definitionExact] using stored

#print axioms origin_of_mem
#print axioms application_has_origin

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedRuleOrigin
