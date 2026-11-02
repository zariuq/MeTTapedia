import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransportSemantics
import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublicationControls

/-!
# Earned inclusion succeeds physically; public copies and unknown IDs fail

The actual type-declaration firing supplies the successor snapshot and both
canonical metadata rows. A new public request then transports the retained
original proof through a fully formed ordinary CMR selection. Every private
snapshot/metadata occurrence survives and the original independent source
weakening justifies the exact full theorem at its target context.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransportControls

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (action)
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls
open HOLLightSnapshotData HOLLightSnapshotActivation HOLLightSnapshotExecution
open HOLLightSnapshotControls HOLLightSnapshotPhysicalControls
open HOLLightSnapshotContextTransport HOLLightSnapshotContextTransportSemantics

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def inputs := Snapshot × Nat × Nat × Theorem

def helperActivate (_ : Unit) (input : inputs) : Option (RuleInstance Value) :=
  activate input.1 input.2.1 input.2.2.1 input.2.2.2

def helperAuthority : SchemaPublicationAuthority.System Unit Location Bool Occurrence location
    (fun occurrence => location occurrence ≠ requests) where
  process actor := if actor then ⟨fullRights, [()]⟩ else ⟨clientRights, [()]⟩
  kernel := true
  soleWriter := by
    intro actor different occurrence protectedHere
    cases actor with
    | false => simpa [clientRights] using protectedHere
    | true => exact False.elim (different rfl)

theorem earned_inclusion_lookup : prepared.snapshot.store.lookup (.inr (0, 1)) = some 2 := by decide

theorem earned_target_lookup : prepared.snapshot.store.lookup (.inl 1) = some 1 := by decide

theorem activation_computed : activate prepared.snapshot 0 1 identityExistence =
    some (rule prepared.snapshot 0 1 identityExistence) := by
  simp only [HOLLightSnapshotContextTransport.activate, original_context_retained, exact_new_context, earned_target_lookup, earned_inclusion_lookup,
    Bind.bind, Option.bind]
  rfl

private theorem fresh_metadata_is_actual_output (row : Nat × HOLLightCanonicalLicenses.Key)
    (fresh : row ∈ prepared.snapshot.store.rows \ beforeSnapshot.store.rows) :
    (licenses, HOLLightCanonicalLicenses.payload row.2) ∈
      (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared).produce := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨row, (Finset.mem_sort _).mpr fresh, rfl⟩

theorem earned_inclusion_and_proof_fire_with_private_state_retained :
    ∃ world after,
      InteractionFormation.SchemaStep helperAuthority helperActivate action payload true world after ∧
      (∀ occurrence ∈ world.present, location occurrence ≠ requests → occurrence ∈ after.present) ∧
      (∃ occurrence ∈ after.present, label occurrence = (judgments, HOLLightContextActivation.theoremPayload 1 identityExistence)) ∧
      TheoryDerives emptyAxiomPolicy definedType.context identityExistence := by
  obtain ⟨first, installed, _, _, proofPresent, _, _, produced⟩ := complete_atomic_publication
  obtain ⟨snapshot, snapshotPresent, snapshotLabel⟩ := produced (snapshots, snapshotPayload prepared.snapshot) (List.mem_cons_self ..)
  obtain ⟨availability, availabilityPresent, availabilityLabel⟩ := produced
    (licenses, HOLLightLicensedActivation.available 1) (fresh_metadata_is_actual_output (1, .inl 1) (by decide))
  obtain ⟨inclusion, inclusionPresent, inclusionLabel⟩ := produced
    (licenses, HOLLightLicensedActivation.included 0 1) (fresh_metadata_is_actual_output (2, .inr (0, 1)) (by decide))
  let requestValue : Value := (requests, HOLLightLicensedActivation.weakeningRequest 0 1 identityExistence)
  obtain ⟨request, _, requestLabel⟩ := IndexedOccurrences.supply first.present requestValue
  have requestReadback : label request = requestValue := requestLabel
  let world : Configuration Value Occurrence := ⟨first.equations, insert request first.present⟩
  have consistent : locatedAction.Consistent world.equations := by
    obtain ⟨_, _, _, _, _, picked, qualified, _, destination⟩ := installed
    change locatedAction.Consistent first.equations
    rw [destination]
    exact qualified.consistent
  have available : ∀ value ∈ (rule prepared.snapshot 0 1 identityExistence).read,
      ∃ occurrence ∈ world.present, label occurrence = value := by
    intro value member
    have alternatives : value = (snapshots, snapshotPayload prepared.snapshot) ∨
        value = (licenses, HOLLightLicensedActivation.available 1) ∨
        value = (licenses, HOLLightLicensedActivation.included 0 1) ∨
        value = (judgments, HOLLightContextActivation.theoremPayload 0 identityExistence) := by
      simpa only [exact_reads, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases alternatives with rfl | rfl | rfl | rfl
    · exact ⟨snapshot, Finset.mem_insert_of_mem snapshotPresent, snapshotLabel⟩
    · exact ⟨availability, Finset.mem_insert_of_mem availabilityPresent, availabilityLabel⟩
    · exact ⟨inclusion, Finset.mem_insert_of_mem inclusionPresent, inclusionLabel⟩
    · exact ⟨existenceOccurrence, Finset.mem_insert_of_mem proofPresent, rfl⟩
  have separate : ∀ occurrence ∈ world.present, label occurrence ∈ (rule prepared.snapshot 0 1 identityExistence).read → occurrence ≠ request := by
    intro occurrence _ member equal
    subst occurrence
    rw [requestReadback] at member
    simp [exact_reads, requestValue, requests, snapshots, licenses, judgments] at member
  obtain ⟨picked, _, qualified⟩ := ExactRequestExecution.selection locatedAction requestValue
    (rule prepared.snapshot 0 1 identityExistence).read (rule prepared.snapshot 0 1 identityExistence).produce
    world consistent request (Finset.mem_insert_self ..) requestLabel available separate
  change picked.Valid locatedAction label (rule prepared.snapshot 0 1 identityExistence) world at qualified
  let after := picked.result label (rule prepared.snapshot 0 1 identityExistence) world
  have stepped : InteractionFormation.SchemaStep helperAuthority helperActivate action payload true world after := by
    refine ⟨(), by simp [helperAuthority], (prepared.snapshot, 0, 1, identityExistence), rule prepared.snapshot 0 1 identityExistence,
      activation_computed, picked, qualified, ?_, rfl⟩
    exact transport_fully_formed location payload prepared.snapshot 0 1 identityExistence picked
  have snapshotValid := HOLLightSnapshotPublicationControls.coupled_firing_earns_independent_source.1
  obtain ⟨assignment, solved⟩ := qualified.consistent
  obtain ⟨targetContext, targetKnown, _, transported⟩ := physical_transport_justifies_exact_source coreContext emptyAxiomPolicy coreContext
    prepared.snapshot snapshotValid 0 1 identityExistence activation_computed location payload qualified assignment solved (by
      intro occurrence read atJudgments observed sourceContext beforeKnown
      have same : sourceContext = coreContext := Option.some.inj (beforeKnown.symm.trans original_context_retained)
      subst sourceContext
      exact withExistence_valid identityExistence (by simp [withExistence]))
  have contextSame : targetContext = definedType.context := Option.some.inj (targetKnown.symm.trans exact_new_context)
  have outputMember : (judgments, HOLLightContextActivation.theoremPayload 1 identityExistence) ∈
      (rule prepared.snapshot 0 1 identityExistence).produce := List.mem_cons_self ..
  rw [← qualified.outputs] at outputMember
  obtain ⟨result, made, resultLabel⟩ := List.mem_map.mp outputMember
  refine ⟨world, after, stepped, ?_, ⟨result, ?_, resultLabel⟩, contextSame ▸ transported⟩
  · intro occurrence present notRequest
    exact private_occurrence_survives location payload prepared.snapshot 0 1 identityExistence qualified occurrence present notRequest
  · exact made_subset_fire (by simpa [Selection.commit] using made)

theorem unknown_context_id_two : context prepared.snapshot 2 = none := rfl

theorem unknown_target_id_refused : activate prepared.snapshot 0 2 identityExistence = none :=
  unknown_target_context_refused _ _ _ _ unknown_context_id_two

theorem unknown_source_id_refused : activate prepared.snapshot 2 1 identityExistence = none :=
  unknown_source_context_refused _ _ _ _ unknown_context_id_two

theorem reversed_unearned_inclusion_refused : activate prepared.snapshot 1 0 identityExistence = none :=
  missing_inclusion_refused _ _ _ _ (by decide)

theorem successor_snapshot_differs_from_root : prepared.snapshot ≠ beforeSnapshot := by
  intro same
  have counts := congrArg (fun snapshot : Snapshot => snapshot.entries.size) same
  change 1 = 0 at counts
  cases counts

theorem captured_root_snapshot_cannot_answer_successor_request (world : Configuration Value Occurrence)
    (picked : Selection Occurrence) (captured : Occurrence) (rest : List Occurrence)
    (first : picked.read = captured :: rest)
    (oldPayload : (location captured, payload captured) = (snapshots, snapshotPayload beforeSnapshot)) :
    ¬picked.Valid locatedAction label (rule prepared.snapshot 0 1 identityExistence) world :=
  stale_snapshot_cannot_supply_private_read location payload prepared.snapshot beforeSnapshot successor_snapshot_differs_from_root
    0 1 identityExistence world picked captured rest first oldPayload

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransportControls
