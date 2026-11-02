import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotExecution

/-!
# Independent source judgments extracted from actual snapshot-selected premises

A prepared public cache supplies data only. Actual physical read equations
supply its cited theorem authority, in the protected judgment location. The
one original command then licenses the successor context and every exact
published theorem. No source derivability test runs inside activation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotSemantics

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation
open HOLLightContextLicensing

private theorem fixed_reads {O : Type*} (good : Value → Prop)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (label : O → Value)
    {values : List Value} {selected : List O}
    (matched : List.Forall₂ (fun value occurrence => locatedAction.E (locatedAction.apply assignment value)
      (locatedAction.apply assignment (label occurrence))) values selected)
    (fixed : ∀ value ∈ values, FixedMatching.Fixed locatedAction value)
    (incoming : ∀ occurrence ∈ selected, good (locatedAction.apply assignment (label occurrence))) :
    ∀ value ∈ values, good value := by
  induction matched with
  | nil => intro value member; cases member
  | @cons value occurrence values selected same rest earlier =>
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · have equal : locatedAction.apply assignment result = locatedAction.apply assignment (label occurrence) :=
          Prod.ext same.1 same.2
        rw [fixed result (List.mem_cons_self ..) assignment] at equal
        rw [equal]
        exact incoming occurrence (List.mem_cons_self ..)
      · exact earlier (fun value member => fixed value (List.mem_cons_of_mem _ member))
          (fun occurrence member => incoming occurrence (List.mem_cons_of_mem _ member)) result member

theorem only_actual_snapshot_unifies (first second : Snapshot)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    locatedAction.Solves assignment ((snapshots, snapshotPayload first), (snapshots, snapshotPayload second)) ↔ first = second := by
  change (snapshots = snapshots ∧ action.apply assignment (snapshotPayload first) = action.apply assignment (snapshotPayload second)) ↔ _
  simp only [snapshotPayload, tagged_fixed, true_and]
  exact snapshotPayload_injective.eq_iff

theorem physical_selected_parents {O : Type*} [DecidableEq O]
    (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (beforeId : Nat) (data : Data) (cache : Array Theorem) {prepared : Prepared}
    (computed : prepare policy snapshot beforeId data cache = some prepared)
    (location : O → Location) (payload : O → Tm) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world))
    (incoming : ∀ sourceContext, context snapshot beforeId = some sourceContext → ∀ occurrence ∈ picked.read,
      location occurrence = judgments → ∀ fact,
        action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload beforeId fact →
          TheoryDerives policy sourceContext fact) :
    ∀ sourceContext, context snapshot beforeId = some sourceContext → ∀ index ∈ prepared.command.parents,
      ∀ fact, cache[index]? = some fact → TheoryDerives policy sourceContext fact := by
  intro sourceContext contextKnown index cited fact found
  obtain ⟨contextData, formed, command, output, table, parents, _, _, _, _, selected, samePrepared⟩ :=
    prepare_origin policy snapshot beforeId data cache computed
  subst prepared
  have sameReads := (Selection.models_problem locatedAction qualified solved).2.2.1
  have readGood := fixed_reads (fun value : Value => ∀ theoremValue,
      value = (judgments, HOLLightContextActivation.theoremPayload beforeId theoremValue) → TheoryDerives policy sourceContext theoremValue)
    assignment (fun occurrence => (location occurrence, payload occurrence)) sameReads (by
      intro value member
      obtain ⟨theoremValue, _, rfl⟩ := List.mem_map.mp member
      intro substitution
      change (judgments, action.apply substitution (HOLLightContextActivation.theoremPayload beforeId theoremValue)) = _
      rw [HOLLightContextActivation.theoremPayload_fixed]) (by
      intro occurrence member theoremValue equal
      have samePlace : location occurrence = judgments := congrArg Prod.fst equal
      have samePayload : action.apply assignment (payload occurrence) =
          HOLLightContextActivation.theoremPayload beforeId theoremValue := congrArg Prod.snd equal
      exact incoming sourceContext contextKnown occurrence member samePlace theoremValue samePayload)
  have member := DerivationGraph.lookupPremises_cited cache selected index cited fact found
  exact readGood (judgments, HOLLightContextActivation.theoremPayload beforeId fact)
    (List.mem_map.mpr ⟨fact, member, rfl⟩) fact rfl

theorem physical_installation_extracts_source {O : Type*} [DecidableEq O]
    (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (beforeId : Nat) (data : Data) (cache : Array Theorem) {prepared : Prepared}
    (computed : prepare policy snapshot beforeId data cache = some prepared)
    (location : O → Location) (payload : O → Tm) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world))
    (licensed : ∀ sourceContext, context snapshot beforeId = some sourceContext → Licensed initial policy sourceContext)
    (incoming : ∀ sourceContext, context snapshot beforeId = some sourceContext → ∀ occurrence ∈ picked.read,
      location occurrence = judgments → ∀ fact,
        action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload beforeId fact →
          TheoryDerives policy sourceContext fact) :
    Licensed initial policy prepared.output.context ∧
      (∀ fact ∈ prepared.output.theorems, TheoryDerives policy prepared.output.context fact) ∧
      context prepared.snapshot prepared.after = some prepared.output.context := by
  apply HOLLightSnapshotInstallation.prepared_source_is_rooted initial policy snapshot beforeId data cache computed licensed
  exact physical_selected_parents policy snapshot beforeId data cache computed location payload qualified assignment solved incoming

theorem actual_judgment_output_is_exact {O : Type*} [DecidableEq O]
    (location : O → Location) (payload : O → Tm) (snapshot : Snapshot) (beforeId : Nat)
    (data : Data) (cache : Array Theorem) (prepared : Prepared) {world : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
      (installRule snapshot beforeId data cache prepared) world)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (occurrence : O) (made : occurrence ∈ picked.made) (protectedLocation : location occurrence = judgments)
    (identifier : Nat) (fact : Theorem)
    (observed : action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload identifier fact) :
    identifier = prepared.after ∧ fact ∈ prepared.output.theorems := by
  have outputMember : (location occurrence, payload occurrence) ∈
      (installRule snapshot beforeId data cache prepared).produce := by
    rw [← qualified.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
  rcases List.mem_cons.mp outputMember with snapshotOutput | other
  · have place : snapshots = location occurrence := congrArg Prod.fst snapshotOutput.symm
    rw [protectedLocation] at place
    cases place
  · rcases List.mem_append.mp other with metadata | theoremOutput
    · obtain ⟨row, _, same⟩ := List.mem_map.mp metadata
      have place : licenses = location occurrence := congrArg Prod.fst same
      rw [protectedLocation] at place
      cases place
    · obtain ⟨actual, member, same⟩ := List.mem_map.mp theoremOutput
      have samePayload : HOLLightContextActivation.theoremPayload prepared.after actual = payload occurrence := congrArg Prod.snd same
      rw [← samePayload, HOLLightContextActivation.theoremPayload_fixed] at observed
      obtain ⟨sameId, sameFact⟩ := HOLLightContextActivation.theoremPayload_injective observed
      exact ⟨sameId.symm, sameFact ▸ member⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotSemantics
