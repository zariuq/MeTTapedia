import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedActivation

/-! # Distinct meanings of private context evidence and exact theorem rows -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedValues

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (action)
open HOLLightContextActivation (theoremPayload theoremPayload_injective theoremPayload_fixed)
open HOLLightContextLicensing
open HOLLightLicensedActivation

def Meaning (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (value : Value) : Prop :=
  (∀ context, value = (licenses, available context) → Licensed initial policy (contexts context)) ∧
  (∀ before after, value = (licenses, included before after) → Path policy (contexts before) (contexts after)) ∧
  (∀ context fact, value = (judgments, theoremPayload context fact) →
    Licensed initial policy (contexts context) ∧ TheoryDerives policy (contexts context) fact)

theorem meaning_available (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (context : Nat) (licensed : Licensed initial policy (contexts context)) :
    Meaning initial policy contexts (licenses, available context) := by
  refine ⟨?_, ?_, ?_⟩
  · intro other same
    have equal := available_injective (congrArg Prod.snd same)
    exact equal ▸ licensed
  · intro before after same
    exact False.elim (available_ne_included context before after (congrArg Prod.snd same))
  · intro other fact same
    simp [licenses, judgments] at same

theorem meaning_included (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (before after : Nat) (path : Path policy (contexts before) (contexts after)) :
    Meaning initial policy contexts (licenses, included before after) := by
  refine ⟨?_, ?_, ?_⟩
  · intro context same
    exact False.elim (available_ne_included context before after (congrArg Prod.snd same).symm)
  · intro old new same
    obtain ⟨rfl, rfl⟩ := included_injective (congrArg Prod.snd same)
    exact path
  · intro other fact same
    simp [licenses, judgments] at same

theorem meaning_theorem (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (context : Nat) (fact : Theorem)
    (licensed : Licensed initial policy (contexts context)) (proof : TheoryDerives policy (contexts context) fact) :
    Meaning initial policy contexts (judgments, theoremPayload context fact) := by
  refine ⟨?_, ?_, ?_⟩
  · intro other same
    simp [licenses, judgments] at same
  · intro before after same
    simp [licenses, judgments] at same
  · intro otherContext otherFact same
    obtain ⟨rfl, rfl⟩ := theoremPayload_injective (congrArg Prod.snd same)
    exact ⟨licensed, proof⟩

theorem meaning_request (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (value : InferenceSchemaActivation.Tm) :
    Meaning initial policy contexts (requests, value) := by
  refine ⟨?_, ?_, ?_⟩
  · intro other same
    simp [licenses, requests] at same
  · intro before after same
    simp [licenses, requests] at same
  · intro other fact same
    simp [judgments, requests] at same

theorem pair_fixed (location : Location) (value : InferenceSchemaActivation.Tm)
    (fixed : FixedMatching.Fixed action value) : FixedMatching.Fixed locatedAction (location, value) := by
  intro assignment
  exact congrArg (fun term => (location, term)) (fixed assignment)

theorem read_values {O : Type*} (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (label : O → Value)
    {values : List Value} {selected : List O}
    (matched : List.Forall₂ (fun value occurrence => locatedAction.E (locatedAction.apply assignment value)
      (locatedAction.apply assignment (label occurrence))) values selected)
    (fixed : ∀ value ∈ values, FixedMatching.Fixed locatedAction value)
    (incoming : ∀ occurrence ∈ selected, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ value ∈ values, Meaning initial policy contexts value := by
  induction matched with
  | nil => intro value member; cases member
  | @cons value occurrence values selected same rest earlier =>
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · have equal : locatedAction.apply assignment result = locatedAction.apply assignment (label occurrence) :=
          Prod.ext same.1 same.2
        rw [fixed result (by simp) assignment] at equal
        rw [equal]
        exact incoming occurrence (by simp)
      · exact earlier (fun value member => fixed value (List.mem_cons_of_mem _ member))
          (fun occurrence member => incoming occurrence (List.mem_cons_of_mem _ member)) result member

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedValues
