import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransport

/-!
# Independent source weakening from actual canonical inclusion and proof reads

The canonical private store retains the original licensed inclusion path.
The ordinary selected read supplies the old-context source theorem. Original
source weakening yields the same full theorem in the exact target context,
without changing its hypotheses or axiom dependencies or replaying history.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransportSemantics

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotActivation HOLLightSnapshotContextTransport
open HOLLightSnapshotPublication HOLLightSnapshotRegistrySemantics HOLLightContextLicensing

private theorem selected_for_pattern {A B : Type*} {relation : A → B → Prop} {patterns : List A} {selected : List B}
    (matched : List.Forall₂ relation patterns selected) (pattern : A) (member : pattern ∈ patterns) :
    ∃ occurrence ∈ selected, relation pattern occurrence := by
  induction matched with
  | nil => cases member
  | @cons first occurrence rest others related remaining earlier =>
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨occurrence, List.mem_cons_self .., related⟩
      · obtain ⟨actual, present, solved⟩ := earlier inRest
        exact ⟨actual, List.mem_cons_of_mem _ present, solved⟩

theorem canonical_path_is_original_source_path (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (snapshot : Snapshot) (valid : Valid root policy fallback snapshot)
    (before after : Nat) (beforeContext afterContext : TheoryContext)
    (beforeKnown : context snapshot before = some beforeContext) (afterKnown : context snapshot after = some afterContext)
    (included : (snapshot.store.lookup (.inr (before, after))).isSome = true) : Path policy beforeContext afterContext := by
  cases found : snapshot.store.lookup (.inr (before, after)) with
  | none => simp [found] at included
  | some index =>
      have actual := valid.registry.licensed index (.inr (before, after)) ((snapshot.store.represented index _).mpr found)
      simpa only [HOLLightCanonicalContextRegistry.Eligible, interpret, beforeKnown, afterKnown, Option.getD_some] using actual

theorem transport_fully_formed {O : Type*} [DecidableEq O] (location : O → Location) (payload : O → Tm)
    (snapshot : Snapshot) (before after : Nat) (fact : Theorem) (picked : Selection O) :
    InteractionFormation.Formed HOLLightSnapshotExecution.fullRights (fun occurrence => (location occurrence, payload occurrence)) picked
      (rule snapshot before after fact) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro occurrence member; rfl
  · intro occurrence member; rfl
  · intro occurrence member; rfl
  · intro query member; cases member
  · intro check member; cases member

theorem private_occurrence_survives {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (before after : Nat) (fact : Theorem)
    {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) (rule snapshot before after fact) world)
    (occurrence : O) (present : occurrence ∈ world.present) (notRequest : location occurrence ≠ requests) :
    occurrence ∈ (picked.result (fun occurrence => (location occurrence, payload occurrence)) (rule snapshot before after fact) world).present := by
  apply mem_fire.mpr
  left
  refine ⟨present, ?_⟩
  intro taken
  have actual : occurrence ∈ picked.taken := by simpa [Selection.commit] using taken
  have matchedTake := LocatedSubstitution.take_locations action location payload qualified
  rw [exact_take] at matchedTake
  obtain ⟨request, rest, same, remaining, selected⟩ := List.forall₂_cons_left_iff.mp matchedTake
  have empty : rest = [] := List.forall₂_nil_left_iff.mp remaining
  have equal : occurrence = request := by simpa [selected, empty] using actual
  exact notRequest (equal ▸ same.symm)

theorem public_inclusion_cannot_supply_private_read {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (before after : Nat) (fact : Theorem)
    (world : Configuration Value O) (picked : Selection O) (snapshotOccurrence availabilityOccurrence forged : O)
    (rest : List O) (first : picked.read = snapshotOccurrence :: availabilityOccurrence :: forged :: rest)
    (publicLocation : location forged = requests) :
    ¬picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) (rule snapshot before after fact) world := by
  intro qualified
  have matched := LocatedSubstitution.read_locations action location payload qualified
  rw [exact_reads, first] at matched
  cases matched with
  | cons snapshotSame remaining => cases remaining with
    | cons availabilitySame remaining => cases remaining with
      | cons inclusionSame remaining =>
          change licenses = location forged at inclusionSame
          rw [publicLocation] at inclusionSame
          cases inclusionSame

theorem stale_snapshot_cannot_supply_private_read {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (expected actual : Snapshot) (different : expected ≠ actual)
    (before after : Nat) (fact : Theorem) (world : Configuration Value O) (picked : Selection O)
    (snapshotOccurrence : O) (rest : List O) (first : picked.read = snapshotOccurrence :: rest)
    (captured : (location snapshotOccurrence, payload snapshotOccurrence) = (snapshots, snapshotPayload actual)) :
    ¬picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) (rule expected before after fact) world := by
  intro qualified
  obtain ⟨assignment, solved⟩ := qualified.consistent
  have matched := (Selection.models_problem locatedAction qualified solved).2.2.1
  rw [exact_reads, first] at matched
  cases matched with
  | cons same remaining =>
      change locatedAction.Solves assignment ((snapshots, snapshotPayload expected), (location snapshotOccurrence, payload snapshotOccurrence)) at same
      rw [captured] at same
      exact different ((HOLLightSnapshotSemantics.only_actual_snapshot_unifies expected actual assignment).mp same)

theorem physical_transport_justifies_exact_source {O : Type*} [DecidableEq O]
    (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (fallback : TheoryContext)
    (snapshot : Snapshot) (valid : Valid root policy fallback snapshot) (before after : Nat) (fact : Theorem)
    {raw : RuleInstance Value} (computed : activate snapshot before after fact = some raw)
    (location : O → Location) (payload : O → Tm) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) raw world)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem (fun occurrence => (location occurrence, payload occurrence)) raw world))
    (incoming : ∀ occurrence ∈ picked.read, location occurrence = judgments →
      action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload before fact →
        ∀ sourceContext, context snapshot before = some sourceContext → TheoryDerives policy sourceContext fact) :
    ∃ targetContext, context snapshot after = some targetContext ∧ Licensed root policy targetContext ∧
      TheoryDerives policy targetContext fact := by
  obtain ⟨beforeContext, afterContext, beforeKnown, afterKnown, available, included, rfl⟩ := activation_origin snapshot before after fact computed
  have path := canonical_path_is_original_source_path root policy fallback snapshot valid before after beforeContext afterContext beforeKnown afterKnown included
  have matched := (Selection.models_problem locatedAction qualified solved).2.2.1
  obtain ⟨occurrence, selected, related⟩ := selected_for_pattern matched
    (judgments, HOLLightContextActivation.theoremPayload before fact) (by simp [exact_reads])
  have place : location occurrence = judgments := related.1.symm
  have observed : action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload before fact := by
    have same : action.apply assignment (HOLLightContextActivation.theoremPayload before fact) =
        action.apply assignment (payload occurrence) := related.2
    rw [HOLLightContextActivation.theoremPayload_fixed] at same
    exact same.symm
  exact ⟨afterContext, afterKnown, licensed_context root policy fallback snapshot valid.registry after afterContext afterKnown available,
    transport_theorem policy path (incoming occurrence selected place observed beforeContext beforeKnown)⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransportSemantics
