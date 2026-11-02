import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedGenesis
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactRequestExecution

/-! # Constructive actual firings for rooted-license request activations -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedExecution

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm)
open HOLLightContextActivation (Entry)
open HOLLightLicensedActivation

abbrev Occurrence := IndexedOccurrences.Occurrence Value
abbrev label : Occurrence → Value := IndexedOccurrences.label
def location (occurrence : Occurrence) : Location := (label occurrence).1
def payload (occurrence : Occurrence) : Tm := (label occurrence).2

def system (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (commands : List Nat) :
    HOLLightLicensedPublication.System policy contexts entries Unit Unit Bool Occurrence location where
  commands := commands
  clientActivation := fun _ _ => none
  authority :=
    { process := fun actor => if actor then
        ⟨fun _ _ => true, (HOLLightLicensedPublication.kernelSources commands).map Sum.inl⟩
      else ⟨fun space _ => space == requests, []⟩
      kernel := true
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        cases actor with
        | true => exact False.elim (notKernel rfl)
        | false =>
            change (location occurrence == requests) = false
            cases position : location occurrence with
            | inr extra => rfl
            | inl space =>
                cases space with
                | requests => exact False.elim (protectedHere position)
                | judgments => rfl }
  kernelSchemas := rfl

theorem activated_runs (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (entries : Nat → Option (Entry contexts))
    (commands : List Nat) (source : Source) (installed : source ∈ HOLLightLicensedPublication.kernelSources commands)
    (inputs : Inputs) (requestValue : Tm) (premises outputs : List Value)
    (computed : activate policy contexts entries source inputs =
      some (ExactRequestExecution.rule (requests, requestValue) premises outputs))
    (privateReads : ∀ value ∈ premises, value.1 ≠ requests)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (request : Occurrence) (present : request ∈ before.present) (readback : label request = (requests, requestValue))
    (available : ∀ value ∈ premises, ∃ occurrence ∈ before.present, label occurrence = value) :
    ∃ after, (system policy contexts entries commands).Step payload true before after ∧
      (∀ occurrence ∈ before.present, occurrence ≠ request → occurrence ∈ after.present) ∧
      (∀ value ∈ outputs, ∃ occurrence ∈ after.present, label occurrence = value) := by
  obtain ⟨picked, takeSame, qualified⟩ := ExactRequestExecution.selection locatedAction
    (requests, requestValue) premises outputs before background request present readback available (by
      intro occurrence _ member same
      have different := privateReads (label occurrence) member
      subst occurrence
      exact different (congrArg Prod.fst readback))
  let raw := ExactRequestExecution.rule (requests, requestValue) premises outputs
  let after := picked.result label raw before
  have step : (system policy contexts entries commands).Step payload true before after := by
    refine ⟨.inl source, List.mem_map.mpr ⟨source, installed, rfl⟩, .inl inputs, raw,
      computed, picked, qualified, ?_, rfl⟩
    intro occurrence made
    rfl
  refine ⟨after, step, ?_, ?_⟩
  · intro occurrence old different
    apply mem_fire.mpr
    left
    refine ⟨old, ?_⟩
    intro taken
    exact different (by simpa [Selection.commit, takeSame] using taken)
  · intro value member
    have selected : value ∈ picked.made.map label := by
      rw [qualified.outputs]
      exact member
    obtain ⟨occurrence, made, readback⟩ := List.mem_map.mp selected
    refine ⟨occurrence, ?_, readback⟩
    apply mem_fire.mpr
    right
    simpa [Selection.commit] using made

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedExecution
