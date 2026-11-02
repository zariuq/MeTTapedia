import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotActivation

/-!
# The complete snapshot update is one existing physical CMR interaction

The same selection consumes the old private snapshot and request, reads
exact protected premises and produces the entire computed result. Full
handle formation remains explicit. A public copy of a snapshot or premise
cannot supply the protected physical occurrence, even with equal payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotExecution

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation

abbrev Occurrence := IndexedOccurrences.Occurrence Value
abbrev label : Occurrence → Value := IndexedOccurrences.label

def fullRights : Rights Location := fun _ _ => true

def Inputs := Snapshot × ((Nat × Data × Array Theorem) ⊕ (Nat × Array Theorem))

def activate (policy : AxiomPolicy) [DecidablePred policy] : Bool → Inputs → Option (RuleInstance Value)
  | false, (snapshot, .inl (before, data, cache)) => installActivate policy snapshot before data cache
  | true, (snapshot, .inr (source, cache)) => runActivate policy snapshot source cache
  | _, _ => none

theorem install_selection (snapshot : Snapshot) (beforeId : Nat) (data : Data) (cache : Array Theorem)
    (prepared : Prepared) (world : Configuration Value Occurrence)
    (background : locatedAction.Consistent world.equations)
    (snapshotOccurrence requestOccurrence : Occurrence)
    (snapshotPresent : snapshotOccurrence ∈ world.present) (requestPresent : requestOccurrence ∈ world.present)
    (snapshotReadback : label snapshotOccurrence = (snapshots, snapshotPayload snapshot))
    (requestReadback : label requestOccurrence = (requests, installRequest beforeId data cache))
    (premisesPresent : ∀ fact ∈ prepared.parents, ∃ occurrence ∈ world.present,
      label occurrence = (judgments, HOLLightContextActivation.theoremPayload beforeId fact)) :
    ∃ picked : Selection Occurrence, picked.taken = [snapshotOccurrence, requestOccurrence] ∧
      picked.Valid locatedAction label (installRule snapshot beforeId data cache prepared) world := by
  classical
  have distinct : snapshotOccurrence ≠ requestOccurrence := by
    intro same
    have places := congrArg Prod.fst (snapshotReadback.symm.trans (same ▸ requestReadback))
    cases places
  apply ExactInteractionExecution.selection locatedAction _ _ _ world background
    [snapshotOccurrence, requestOccurrence] (by simpa using distinct)
  · intro occurrence member
    rcases List.mem_cons.mp member with rfl | member
    · exact snapshotPresent
    · exact (List.mem_singleton.mp member) ▸ requestPresent
  · simp only [List.map_cons, List.map_nil, snapshotReadback, requestReadback]
  · intro value member
    obtain ⟨fact, selected, rfl⟩ := List.mem_map.mp member
    exact premisesPresent fact selected
  · intro occurrence _ member taken
    obtain ⟨fact, _, sameValue⟩ := List.mem_map.mp member
    have place : (label occurrence).1 = judgments := congrArg Prod.fst sameValue.symm
    rcases List.mem_cons.mp taken with same | other
    · subst occurrence
      rw [snapshotReadback] at place
      cases place
    · have same : occurrence = requestOccurrence := List.mem_singleton.mp other
      subst occurrence
      rw [requestReadback] at place
      cases place

theorem install_fully_formed {O : Type*} [DecidableEq O] (location : O → Location) (payload : O → Tm)
    (snapshot : Snapshot) (beforeId : Nat) (data : Data) (cache : Array Theorem) (prepared : Prepared)
    (picked : Selection O) :
    InteractionFormation.Formed fullRights (fun occurrence => (location occurrence, payload occurrence)) picked
      (installRule snapshot beforeId data cache prepared) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro occurrence member
    rfl
  · intro occurrence member
    rfl
  · intro occurrence member
    rfl
  · intro observation member
    cases member
  · intro check member
    cases member

theorem public_snapshot_cannot_supply_private_take {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (beforeId : Nat)
    (data : Data) (cache : Array Theorem) (prepared : Prepared) (world : Configuration Value O)
    (picked : Selection O) (forged : O) (rest : List O) (first : picked.taken = forged :: rest)
    (publicLocation : location forged = requests) :
    ¬picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world := by
  intro qualified
  have matched := LocatedSubstitution.take_locations action location payload qualified
  rw [first] at matched
  cases matched with
  | cons same remaining =>
      change snapshots = location forged at same
      rw [publicLocation] at same
      cases same

theorem public_premise_cannot_supply_private_read {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (beforeId : Nat)
    (data : Data) (cache : Array Theorem) (prepared : Prepared) (world : Configuration Value O)
    (picked : Selection O) (forged : O) (selected : forged ∈ picked.read)
    (publicLocation : location forged = requests) :
    ¬picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world := by
  intro qualified
  have declared : ∀ value ∈ (installRule snapshot beforeId data cache prepared).read, value.1 = judgments := by
    intro value member
    obtain ⟨fact, _, rfl⟩ := List.mem_map.mp member
    rfl
  have actual := LocatedSubstitution.declared_read_space action location payload qualified judgments declared forged selected
  rw [publicLocation] at actual
  cases actual

theorem denied_send_cannot_publish_successor {O : Type*} [DecidableEq O]
    (rights : Rights Location) (location : O → Location) (payload : O → Tm)
    (snapshot : Snapshot) (beforeId : Nat) (data : Data) (cache : Array Theorem) (prepared : Prepared)
    (world : Configuration Value O) (picked : Selection O)
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world)
    (denied : rights snapshots .send = false) :
    ¬InteractionFormation.Formed rights (fun occurrence => (location occurrence, payload occurrence)) picked
      (installRule snapshot beforeId data cache prepared) := by
  intro formed
  have outputMember : (snapshots, snapshotPayload prepared.snapshot) ∈
      (installRule snapshot beforeId data cache prepared).produce := List.mem_cons_self ..
  rw [← qualified.outputs] at outputMember
  obtain ⟨occurrence, member, same⟩ := List.mem_map.mp outputMember
  have allowed := formed.physical.made occurrence (by simpa [Selection.commit] using member)
  have samePlace : location occurrence = snapshots := congrArg Prod.fst same
  rw [samePlace, denied] at allowed
  cases allowed

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotExecution
