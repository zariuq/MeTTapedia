import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublication

/-!
# Persistent proof-only use of the actual private snapshot catalog

A later source use consumes only its public request, reads the actual private
snapshot and original protected premises, and publishes exact source results.
Private snapshot and metadata occurrences survive. No source admission history
is replayed, and no administrative metadata is produced by proof-only use.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotReadExecution

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotActivation HOLLightSnapshotExecution
open HOLLightSnapshotPublication HOLLightSnapshotRegistrySemantics
open HOLLightContextLicensing

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

theorem run_fully_formed {O : Type*} [DecidableEq O] (location : O → Location) (payload : O → Tm)
    (snapshot : Snapshot) (source : Nat) (entry : RawEntry) (cache : Array Theorem)
    (output : Output) (parents : List Theorem) (picked : Selection O) :
    InteractionFormation.Formed fullRights (fun occurrence => (location occurrence, payload occurrence)) picked
      (runFromResult snapshot source entry cache output parents) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro occurrence member; rfl
  · intro occurrence member; rfl
  · intro occurrence member; rfl
  · intro query member; cases member
  · intro check member; cases member

theorem private_occurrence_survives {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (source : Nat) (entry : RawEntry)
    (cache : Array Theorem) (output : Output) (parents : List Theorem) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (runFromResult snapshot source entry cache output parents) world)
    (occurrence : O) (present : occurrence ∈ world.present) (notRequest : location occurrence ≠ requests) :
    occurrence ∈ (picked.result (fun occurrence => (location occurrence, payload occurrence))
      (runFromResult snapshot source entry cache output parents) world).present := by
  apply mem_fire.mpr
  left
  refine ⟨present, ?_⟩
  intro taken
  have actual : occurrence ∈ picked.taken := by simpa [Selection.commit] using taken
  obtain ⟨request, rest, same, remaining, selected⟩ := List.forall₂_cons_left_iff.mp
    (LocatedSubstitution.take_locations action location payload qualified)
  have empty : rest = [] := List.forall₂_nil_left_iff.mp remaining
  have equal : occurrence = request := by simpa [selected, empty] using actual
  exact notRequest (equal ▸ same.symm)

theorem run_source_outputs_only_judgments {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (source : Nat) (entry : RawEntry)
    (cache : Array Theorem) (output : Output) (parents : List Theorem) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (runFromResult snapshot source entry cache output parents) world) :
    ∀ occurrence ∈ picked.made, location occurrence = judgments := by
  intro occurrence made
  have member : (location occurrence, payload occurrence) ∈
      (runFromResult snapshot source entry cache output parents).produce := by
    rw [← qualified.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
  obtain ⟨fact, _, same⟩ := List.mem_map.mp member
  exact (congrArg Prod.fst same).symm

theorem public_snapshot_cannot_supply_private_read {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (source : Nat) (entry : RawEntry)
    (cache : Array Theorem) (output : Output) (parents : List Theorem) (world : Configuration Value O)
    (picked : Selection O) (forged : O) (rest : List O) (first : picked.read = forged :: rest)
    (publicLocation : location forged = requests) :
    ¬picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (runFromResult snapshot source entry cache output parents) world := by
  intro qualified
  have matched := LocatedSubstitution.read_locations action location payload qualified
  rw [first] at matched
  cases matched with
  | cons same remaining =>
      change snapshots = location forged at same
      rw [publicLocation] at same
      cases same

theorem physical_source_use_is_justified {O : Type*} [DecidableEq O]
    (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (fallback : TheoryContext)
    (snapshot : Snapshot) (valid : Valid root policy fallback snapshot) (source : Nat) (cache : Array Theorem)
    {raw : RuleInstance Value} (computed : runActivate policy snapshot source cache = some raw)
    (location : O → Location) (payload : O → Tm) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence)) raw world)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem (fun occurrence => (location occurrence, payload occurrence)) raw world))
    (incoming : ∀ occurrence ∈ picked.read, location occurrence = judgments → ∀ identifier fact,
      action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload identifier fact →
        ∀ sourceContext, context snapshot identifier = some sourceContext → TheoryDerives policy sourceContext fact) :
    ∀ occurrence ∈ picked.made, ∀ identifier fact,
      action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload identifier fact →
        ∃ sourceContext, context snapshot identifier = some sourceContext ∧ Licensed root policy sourceContext ∧
          TheoryDerives policy sourceContext fact := by
  obtain ⟨entry, command, sourceContext, output, parents, found, contextKnown, available, checked, selected, rfl⟩ :=
    run_origin policy snapshot source cache computed
  have matched := (Selection.models_problem locatedAction qualified solved).2.2.1
  have earlier : ∀ index ∈ command.parents, ∀ fact,
      cache[index]? = some fact → TheoryDerives policy sourceContext fact := by
    intro index cited fact lookupFact
    have member := DerivationGraph.lookupPremises_cited cache selected index cited fact lookupFact
    obtain ⟨occurrence, read, related⟩ := selected_for_pattern matched
      (judgments, HOLLightContextActivation.theoremPayload entry.1 fact)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨fact, member, rfl⟩))
    have place : location occurrence = judgments := related.1.symm
    have payloadSame : action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload entry.1 fact := by
      have same : action.apply assignment (HOLLightContextActivation.theoremPayload entry.1 fact) =
          action.apply assignment (payload occurrence) := related.2
      rw [HOLLightContextActivation.theoremPayload_fixed] at same
      exact same.symm
    exact incoming occurrence read place entry.1 fact payloadSame sourceContext contextKnown
  have independent := checked_command_licenses_output root policy
    (licensed_context root policy fallback snapshot valid.registry entry.1 sourceContext contextKnown available) command cache checked earlier
  obtain ⟨oldBefore, oldAfter, beforeKnown, afterKnown, routed⟩ := valid.routes source entry command found
  have sameBefore : oldBefore = sourceContext := Option.some.inj (beforeKnown.symm.trans contextKnown)
  have sameOutput : output.context = oldAfter := Option.some.inj
    ((HOLLightContextActivation.checked_target_context policy sourceContext cache command checked).symm.trans (sameBefore ▸ routed))
  intro occurrence made identifier fact observed
  have member : (location occurrence, payload occurrence) ∈
      (runFromResult snapshot source entry cache output parents).produce := by
    rw [← qualified.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
  obtain ⟨actual, actualMember, same⟩ := List.mem_map.mp member
  have payloadSame : HOLLightContextActivation.theoremPayload entry.2.1 actual = payload occurrence := congrArg Prod.snd same
  rw [← payloadSame, HOLLightContextActivation.theoremPayload_fixed] at observed
  obtain ⟨sameId, sameFact⟩ := HOLLightContextActivation.theoremPayload_injective observed
  refine ⟨output.context, ?_, independent.1, ?_⟩
  · exact sameId ▸ (sameOutput ▸ afterKnown)
  · exact sameFact ▸ independent.2.2 actual actualMember

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotReadExecution
