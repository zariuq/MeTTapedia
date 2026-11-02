import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotControls
import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotExecution

/-!
# The actual private context/catalog update and all theorem outputs fire together

The source type declaration consumes one private snapshot and one public
request. The same formed ordinary two-way CMR interaction retains the
protected existence premise and publishes the successor snapshot, canonical
metadata delta and both source theorems. The resulting catalog is usable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPhysicalControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation HOLLightSnapshotExecution
open HOLLightSnapshotControls

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def snapshotOccurrence : Occurrence := (0, snapshots, snapshotPayload beforeSnapshot)
def requestOccurrence : Occurrence := (1, requests,
  installRequest 0 HOLLightFiniteCommandControls.typeData #[identityExistence])
def existenceOccurrence : Occurrence := (2, judgments, HOLLightContextActivation.theoremPayload 0 identityExistence)
def rootOccurrence : Occurrence := (3, licenses, HOLLightLicensedActivation.available 0)
def runOccurrence : Occurrence := (4, requests, runRequest 0 #[identityExistence])

def location (occurrence : Occurrence) : Location := (label occurrence).1
def payload (occurrence : Occurrence) : Tm := (label occurrence).2

def clientRights (place : Location) (_ : Facet) : Bool := decide (place = requests)

def authority : SchemaPublicationAuthority.System Bool Location Bool Occurrence location
    (fun occurrence => location occurrence ≠ requests) where
  process actor := if actor then ⟨fullRights, [false, true]⟩ else ⟨clientRights, [false, true]⟩
  kernel := true
  soleWriter := by
    intro actor different occurrence protectedHere
    cases actor with
    | false => simpa [clientRights] using protectedHere
    | true => exact False.elim (different rfl)

def initialWorld : Configuration Value Occurrence :=
  ⟨[], {snapshotOccurrence, requestOccurrence, existenceOccurrence, rootOccurrence, runOccurrence}⟩

theorem initial_consistent : locatedAction.Consistent initialWorld.equations :=
  ⟨action.identity, by simp [initialWorld]⟩

theorem actual_selection_computed :
    ∃ picked : Selection Occurrence, picked.taken = [snapshotOccurrence, requestOccurrence] ∧
      picked.Valid locatedAction label
        (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) initialWorld := by
  exact install_selection beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence]
    prepared initialWorld initial_consistent snapshotOccurrence requestOccurrence
    (by simp [initialWorld]) (by simp [initialWorld]) rfl rfl (by
      intro fact member
      have same : fact = identityExistence := by simpa [prepared, updated] using member
      subst fact
      exact ⟨existenceOccurrence, by simp [initialWorld], rfl⟩)

theorem complete_atomic_publication :
    ∃ after, InteractionFormation.SchemaStep authority (activate emptyAxiomPolicy) action payload true initialWorld after ∧
      snapshotOccurrence ∉ after.present ∧ requestOccurrence ∉ after.present ∧
      existenceOccurrence ∈ after.present ∧ rootOccurrence ∈ after.present ∧ runOccurrence ∈ after.present ∧
      (∀ value ∈ (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared).produce,
        ∃ occurrence ∈ after.present, label occurrence = value) := by
  obtain ⟨picked, taken, qualified⟩ := actual_selection_computed
  let rule := installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared
  let after := picked.result label rule initialWorld
  have stepped : InteractionFormation.SchemaStep authority (activate emptyAxiomPolicy) action payload true initialWorld after := by
    refine ⟨false, by simp [authority], (beforeSnapshot, Sum.inl (0, HOLLightFiniteCommandControls.typeData, #[identityExistence])),
      rule, installation_activates, picked, qualified, ?_, rfl⟩
    exact install_fully_formed location payload beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared picked
  refine ⟨after, stepped, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact qualified.consumed_removed (by simp [taken])
  · exact qualified.consumed_removed (by simp [taken])
  · apply mem_fire.mpr
    left
    exact ⟨by simp [initialWorld], by simp [Selection.commit, taken, existenceOccurrence, snapshotOccurrence, requestOccurrence]⟩
  · apply mem_fire.mpr
    left
    exact ⟨by simp [initialWorld], by simp [Selection.commit, taken, rootOccurrence, snapshotOccurrence, requestOccurrence]⟩
  · apply mem_fire.mpr
    left
    exact ⟨by simp [initialWorld], by simp [Selection.commit, taken, runOccurrence, snapshotOccurrence, requestOccurrence]⟩
  · intro value member
    rw [← qualified.outputs] at member
    obtain ⟨occurrence, made, same⟩ := List.mem_map.mp member
    exact ⟨occurrence, made_subset_fire (by simpa [Selection.commit] using made), same⟩

theorem complete_result_has_five_outputs :
    (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared).produce.length = 5 := by
  have delta : (prepared.snapshot.store.rows \ beforeSnapshot.store.rows).card = 2 := by decide
  simp only [installRule, List.length_cons, List.length_append, metadataDelta, List.length_map, Finset.length_sort]
  rw [delta]
  rfl

theorem incomplete_one_output_selection_refused (world : Configuration Value Occurrence) (picked : Selection Occurrence)
    (onlyOne : picked.made.length = 1) :
    ¬picked.Valid locatedAction label
      (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) world := by
  intro qualified
  have lengths := congrArg List.length qualified.outputs
  simp only [List.length_map, complete_result_has_five_outputs, onlyOne] at lengths
  cases lengths

theorem client_no_private_take : clientRights snapshots .receive = false := rfl
theorem client_no_private_read : clientRights snapshots .peek = false := rfl
theorem client_no_private_observation : clientRights snapshots .observe = false := rfl
theorem client_no_private_publication : clientRights snapshots .send = false := rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPhysicalControls
