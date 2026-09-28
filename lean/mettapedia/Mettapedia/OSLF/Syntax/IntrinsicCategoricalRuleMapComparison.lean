import Mettapedia.OSLF.Syntax.CategoricalScopedRuleActionMaps
import Mettapedia.OSLF.Syntax.IntrinsicRuleActionComparison

/-!
# Authored conditional rules satisfy the categorical action-map contract

The intrinsic rule presentation already interprets each scoped premise in the
canonical presheaf target. This module compares its actual, position-indexed
witness transport with the general categorical input and rule-action maps.
No firing witness is replaced by mere endpoint existence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf
open Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest
open Mettapedia.OSLF.Binding.IntrinsicRuleActionComparison
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- The actual authored premise-map at a categorical list position, with
only equality transports between its intrinsic and list presentations. -/
noncomputable def witnessAt (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    let authored := position.cast (authoredPremises_length R index Z)
    Witness ((authoredPremises R index Y).get
      (authoredPosition R index Y authored)).request ⟶
    Witness ((authoredPremises R index Z).get position).request := by
  let authored := position.cast (authoredPremises_length R index Z)
  let sourceEntry := authoredPremises_get R index Y authored
  let targetEntry := authoredPremises_get_at R index Z position
  exact
    eqToHom (congrArg
      (fun premise : Premise
        (occurrencePresheaf R (A := A) index)
        (modelEvents R Y)
        (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request) sourceEntry) ≫
    mapWitness (childRequest R index authored Y)
      (childRequestMap R index authored h) ≫
    eqToHom (congrArg
      (fun premise : Premise
        (occurrencePresheaf R (A := A) index)
        (modelEvents R Z)
        (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request) targetEntry.symm)

/-- A premise witness is transported over the unchanged authored rule
occurrence. -/
theorem witnessAt_parameters (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    witnessAt R index h position ≫
      parameters ((authoredPremises R index Z).get position).request =
    parameters ((authoredPremises R index Y).get
      (authoredPosition R index Y
        (position.cast (authoredPremises_length R index Z)))).request := by
  let authored := position.cast (authoredPremises_length R index Z)
  let sourceEntry := authoredPremises_get R index Y authored
  let targetEntry := authoredPremises_get_at R index Z position
  change ((eqToHom (congrArg
      (fun premise : Premise
        (occurrencePresheaf R (A := A) index)
        (modelEvents R Y)
        (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request) sourceEntry) ≫
    mapWitness (childRequest R index authored Y)
      (childRequestMap R index authored h)) ≫
    eqToHom (congrArg
      (fun premise : Premise
        (occurrencePresheaf R (A := A) index)
        (modelEvents R Z)
        (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request) targetEntry.symm)) ≫ _ = _
  rw [Category.assoc, premise_transport_parameters targetEntry.symm,
    Category.assoc, mapWitness_parameters]
  change (eqToHom (congrArg
      (fun premise : Premise
        (occurrencePresheaf R (A := A) index)
        (modelEvents R Y)
        (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request) sourceEntry) ≫
      parameters (childRequest R index authored Y)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact premise_transport_parameters sourceEntry

/-- The concrete authored witness maps form an ordered categorical input
map, with the same rule occurrence as the parameter object. -/
noncomputable def authoredInputMap (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    InputMap (authoredPremises R index Y)
      (authoredPremises R index Z) where
  sameLength := (authoredPremises_length R index Y).trans
    (authoredPremises_length R index Z).symm
  index position := authoredPosition R index Y
    (position.cast (authoredPremises_length R index Z))
  indexVal position := rfl
  parameter := 𝟙 _
  witness position := witnessAt R index h position
  preservesParameters := by
    intro position
    simpa only [Category.comp_id] using
      witnessAt_parameters R index h position

/-- The general input-map construction gives exactly the existing authored
bundle map, including every selected premise witness. -/
theorem mapInput_authored (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    mapInput (authoredInputMap R index h) =
      authoredBundleMap R index h := by
  apply bundle_hom_ext (authoredPremises R index Z)
  · rw [mapInput_assignment, authoredBundleMap_assignment]
    simp [authoredInputMap]
  · intro position
    rw [mapInput_project, authoredBundleMap_project]
    change project (authoredPremises R index Y)
        (authoredPosition R index Y
          (position.cast (authoredPremises_length R index Z))) ≫
        witnessAt R index h position =
      authoredWitnessMapAt R index h position
    unfold witnessAt authoredWitnessMapAt authoredProject
    simp only [Category.assoc]

/-- The actual authored constructor and every binder-local child firing
satisfy the general categorical rule-action map law. -/
noncomputable def authoredActionMap (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    ActionMap (authoredRuleAction R index Y)
      (authoredRuleAction R index Z) where
  input := authoredInputMap R index h
  event := mapModelEvents R h
  endpoint := 𝟙 _
  endpoint_comm := by
    simpa only [Category.comp_id] using modelEndpointPair_map R h
  conclusion_comm := by simp [authoredInputMap]
  action_comm := by
    rw [mapInput_authored]
    exact authoredRuleAction_map R index h

/-- At the concrete semantic input object, the authored action map at an
identity interpretation is the identity. -/
theorem authoredActionMap_id_input (index : Fin R.length)
    (Y : SubstitutionModel R A) :
    mapInput (authoredActionMap R index (𝟙 Y)).input =
      𝟙 (Bundle (authoredPremises R index Y)) := by
  change mapInput (authoredInputMap R index (𝟙 Y)) = _
  rw [mapInput_authored]
  exact authoredBundleMap_id R index Y

/-- The comparison agrees with composition on the complete ordered input,
including each separate retained premise firing. -/
theorem authoredActionMap_comp_input (index : Fin R.length)
    {Y Z W : SubstitutionModel R A}
    (f : Y ⟶ Z) (g : Z ⟶ W) :
    mapInput (ActionMap.comp
      (authoredActionMap R index f)
      (authoredActionMap R index g)).input =
    mapInput (authoredActionMap R index (f ≫ g)).input := by
  change mapInput (InputMap.comp
      (authoredInputMap R index f)
      (authoredInputMap R index g)) =
    mapInput (authoredInputMap R index (f ≫ g))
  rw [mapInput_comp, mapInput_authored, mapInput_authored,
    mapInput_authored]
  exact (authoredBundleMap_comp R index f g).symm

/-- The same comparison agrees with composition on the individual
conclusion-event map. -/
theorem authoredActionMap_comp_event (index : Fin R.length)
    {Y Z W : SubstitutionModel R A}
    (f : Y ⟶ Z) (g : Z ⟶ W) :
    (ActionMap.comp (authoredActionMap R index f)
      (authoredActionMap R index g)).event =
    (authoredActionMap R index (f ≫ g)).event := by
  have h := (modelEventsFunctor R (A := A)).map_comp f g
  change mapModelEvents R (f ≫ g) =
    mapModelEvents R f ≫ mapModelEvents R g at h
  exact h.symm

end Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison

#print axioms Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison.authoredInputMap
#print axioms Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison.mapInput_authored
#print axioms Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison.authoredActionMap
#print axioms Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison.authoredActionMap_comp_input
#print axioms Mettapedia.OSLF.Binding.IntrinsicCategoricalRuleMapComparison.authoredActionMap_comp_event
