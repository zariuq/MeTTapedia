import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactRequestExecution

/-!
# Constructive physical execution of every activated registered HOL command

Each successful original command, including a two-output type declaration,
has an ordinary firing in the same actual schema-authority system when its
request and selected protected premises are present. Duplicate output values
receive distinct fresh occurrences. The request is consumed while every old
protected theorem remains available.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextExecution

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm)
open InferenceSchemaKernel (Space Value locatedAction)
open HOLLightContextActivation

abbrev Occurrence := IndexedOccurrences.Occurrence Value
abbrev label : Occurrence → Value := IndexedOccurrences.label
def location (occurrence : Occurrence) : Space := (label occurrence).1
def payload (occurrence : Occurrence) : Tm := (label occurrence).2

def system (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (sources : List Nat) :
    HOLLightContextPublication.System policy contexts entries Unit Unit Bool Occurrence location where
  sources := sources
  clientActivation := fun _ _ => none
  authority :=
    { process := fun actor => if actor then ⟨fun _ _ => true, sources.map Sum.inl⟩
      else ⟨fun space _ => space == .requests, []⟩
      kernel := true
      soleWriter := by
        intro actor notKernel occurrence protectedHere
        cases actor with
        | true => exact False.elim (notKernel rfl)
        | false =>
            change (location occurrence == Space.requests) = false
            rw [show location occurrence = Space.judgments from protectedHere]
            rfl }
  kernelSchemas := rfl

theorem activated_command_runs (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (entries : Nat → Option (Entry contexts))
    (sources : List Nat) (source : Nat) (installed : source ∈ sources)
    (cache : Array Theorem) (entry : Entry contexts) (parents : List Theorem) (output : Output)
    (computed : activate policy contexts entries source cache = some (fromResult source entry cache parents output))
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (request : Occurrence) (requestPresent : request ∈ before.present)
    (requestReadback : label request = (.requests, requestPayload source entry cache))
    (available : ∀ fact ∈ parents, ∃ occurrence ∈ before.present,
      label occurrence = (.judgments, theoremPayload entry.before fact)) :
    ∃ after, (system policy contexts entries sources).Step payload true before after ∧
      (∀ occurrence ∈ before.present, location occurrence = .judgments → occurrence ∈ after.present) ∧
      (∀ fact ∈ output.theorems, ∃ occurrence ∈ after.present,
        label occurrence = (.judgments, theoremPayload entry.after fact)) := by
  let raw := fromResult source entry cache parents output
  obtain ⟨picked, takeSame, valid⟩ := ExactRequestExecution.selection locatedAction
    (Space.requests, requestPayload source entry cache)
    (parents.map fun fact => (Space.judgments, theoremPayload entry.before fact))
    (output.theorems.map fun fact => (Space.judgments, theoremPayload entry.after fact))
    before background request requestPresent requestReadback (by
      intro value member
      obtain ⟨fact, factMember, shape⟩ := List.mem_map.mp member
      obtain ⟨occurrence, present, readback⟩ := available fact factMember
      exact ⟨occurrence, present, readback.trans shape⟩) (by
      intro occurrence present member same
      obtain ⟨fact, _, shape⟩ := List.mem_map.mp member
      subst occurrence
      have locations := congrArg Prod.fst (shape.trans requestReadback)
      cases locations)
  have qualified : picked.Valid locatedAction label raw before := valid
  let after := picked.result label raw before
  have step : (system policy contexts entries sources).Step payload true before after := by
    refine ⟨.inl source, List.mem_map.mpr ⟨source, installed, rfl⟩,
      .inl cache, raw, computed, picked, qualified, ?_, rfl⟩
    intro occurrence made
    rfl
  refine ⟨after, step, ?_, ?_⟩
  · intro occurrence present protectedHere
    apply mem_fire.mpr
    left
    refine ⟨present, ?_⟩
    intro taken
    have same : occurrence = request := by simpa [Selection.commit, takeSame] using taken
    have requestPublic : location request = .requests := congrArg Prod.fst requestReadback
    rw [same, requestPublic] at protectedHere
    cases protectedHere
  · intro fact member
    have outputMember : (Space.judgments, theoremPayload entry.after fact) ∈ picked.made.map label := by
      rw [qualified.outputs]
      exact List.mem_map.mpr ⟨fact, member, rfl⟩
    obtain ⟨occurrence, made, readback⟩ := List.mem_map.mp outputMember
    refine ⟨occurrence, ?_, readback⟩
    apply mem_fire.mpr
    right
    simpa [Selection.commit] using made

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextExecution
