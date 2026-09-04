import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedCalculus
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics

/-!
# Formation semantics for the guarded selected-native calculus

Guarded source-indexed generation retains the same independently interpreted
universe objects and modal formation meaning as the unguarded fragment.  Its
formation schemas additionally require canonical ambient-context evidence.

This module proves that the universe and guarded-formation rows selected by
the semantic layer are the rows actually emitted by the guarded generator.
The proofs follow generator families and do not enumerate a concrete output.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedFormationSemantics

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics

/-- Every request-bound universe axiom remains in the common generated
signature prefix of the guarded calculus. -/
theorem universeAxiom_mem_definition
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : SelectedNativeTypeGuardedSourceIndexedIntroduction.PremiseProfile
      demand)
    (carrier : SelectedNativeTypeSourceIndexedSemanticDecoding.CarrierSlot
      demand) :
    CarrierTypingLanguageDef.universeAxiom (carrierName carrier) ∈
      (SelectedNativeTypeGuardedSourceIndexedCalculus.definition
        demand separated profile).rules := by
  have membership := carrierName_mem_generatedCarrierNames demand carrier
  rw [List.mem_append] at membership
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_rules]
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_append.mpr
  cases membership with
  | inl foundationMembership =>
      exact Or.inl
        (foundationUniverseAxiom_mem_signature demand foundationMembership)
  | inr suffixMembership =>
      apply Or.inr
      rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_rules]
      apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨carrierName carrier, suffixMembership, rfl⟩

/-- Every guarded formation schema is an actual row of the final flat
guarded definition. -/
theorem formationRule_mem_definition
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : SelectedNativeTypeGuardedSourceIndexedIntroduction.PremiseProfile
      demand)
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand) :
    ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot) ∈
      (SelectedNativeTypeGuardedSourceIndexedCalculus.definition
        demand separated profile).rules := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_rules]
  apply List.mem_append.mpr
  apply Or.inr
  rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules]
  apply List.mem_flatten.mpr
  refine
    ⟨SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt
      demand profile slot, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨slot, rfl⟩
  · simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt]

/-- Adding canonical ambient-context premises does not change the displayed
formation conclusion classified by the independent semantic view. -/
theorem formationConclusion_exact
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand) :
    (schemaFormationView demand slot).conclusionWire =
      ContextualInference.lowerSequent
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot).conclusion := by
  simpa [SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
    SelectedNativeTypeSourceIndexedIntroduction.formationRule,
    SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore]
    using schemaFormationConclusion_exact demand slot

#print axioms universeAxiom_mem_definition
#print axioms formationRule_mem_definition
#print axioms formationConclusion_exact

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedFormationSemantics
