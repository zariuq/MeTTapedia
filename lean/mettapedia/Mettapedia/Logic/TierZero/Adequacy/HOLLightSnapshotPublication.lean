import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotRegistrySemantics

/-!
# Rooted validity and exact theorem publication through the coupled interaction

The initial finite context is explicit. Actual installation preserves the
canonical rooted registry and every earned source route. Independent theorem
validity comes from the selected protected reads and original local checker;
all prior immutable contexts remain available to existing clients and proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublication

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotInstallation HOLLightSnapshotActivation
open HOLLightSnapshotRouting HOLLightSnapshotRegistrySemantics HOLLightSnapshotSemantics
open HOLLightContextLicensing

structure Valid (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (snapshot : Snapshot) : Prop where
  routes : Routes snapshot
  registry : RegistryValid root policy fallback snapshot

theorem initial_valid (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (table : DeclarationTable.Table root) : Valid root policy fallback (initial table) :=
  ⟨initial_routed table, initialized_valid root policy fallback table⟩

theorem prepared_routes (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (routed : Routes snapshot) (before : Nat) (data : Data) (cache : Array Theorem)
    {prepared : Prepared} (computed : prepare policy snapshot before data cache = some prepared) : Routes prepared.snapshot := by
  obtain ⟨contextData, formed, command, output, table, parents, contextKnown, _, decoded, checked, _, rfl⟩ :=
    prepare_origin policy snapshot before data cache computed
  have known : context snapshot before = some (HOLLightFiniteContextData.toContext contextData formed) := by
    simp only [context, contextKnown, Bind.bind, Option.bind]
    unfold HOLLightFiniteContextData.decode
    rw [dif_pos ((HOLLightFiniteContextData.valid_iff _).mpr formed)]
  exact routes_updated policy snapshot routed before data command output table parents cache known checked decoded

theorem prepared_old_contexts (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (before : Nat) (data : Data) (cache : Array Theorem)
    {prepared : Prepared} (computed : prepare policy snapshot before data cache = some prepared) :
    ∀ identifier sourceContext, context snapshot identifier = some sourceContext → context prepared.snapshot identifier = some sourceContext := by
  obtain ⟨_, _, command, output, table, parents, _, _, _, _, _, rfl⟩ :=
    prepare_origin policy snapshot before data cache computed
  exact old_context_retained snapshot before data command output table parents

theorem coupled_publication_preserves_source_authority {O : Type*} [DecidableEq O]
    (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (fallback : TheoryContext)
    (snapshot : Snapshot) (valid : Valid root policy fallback snapshot)
    (beforeId : Nat) (data : Data) (cache : Array Theorem) {prepared : Prepared}
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
    Valid root policy fallback prepared.snapshot ∧
      (∀ identifier sourceContext, context snapshot identifier = some sourceContext → context prepared.snapshot identifier = some sourceContext) ∧
      ∀ occurrence ∈ picked.made, location occurrence = judgments → ∀ identifier fact,
        action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload identifier fact →
          ∃ sourceContext, context prepared.snapshot identifier = some sourceContext ∧
            Licensed root policy sourceContext ∧ TheoryDerives policy sourceContext fact := by
  have selected := physical_selected_parents policy snapshot beforeId data cache computed location payload qualified assignment solved incoming
  have nextValid : Valid root policy fallback prepared.snapshot :=
    ⟨prepared_routes policy snapshot valid.routes beforeId data cache computed,
      prepared_registry_valid root policy fallback snapshot valid.registry beforeId data cache computed selected⟩
  have licensed : ∀ sourceContext, context snapshot beforeId = some sourceContext → Licensed root policy sourceContext := by
    intro sourceContext known
    obtain ⟨_, _, _, _, _, _, _, available, _, _, _, _⟩ := prepare_origin policy snapshot beforeId data cache computed
    exact licensed_context root policy fallback snapshot valid.registry beforeId sourceContext known available
  have independent := physical_installation_extracts_source root policy snapshot beforeId data cache computed location payload qualified assignment solved licensed incoming
  refine ⟨nextValid, prepared_old_contexts policy snapshot beforeId data cache computed, ?_⟩
  intro occurrence made atJudgments identifier fact observed
  obtain ⟨sameId, actualMember⟩ := actual_judgment_output_is_exact location payload snapshot beforeId data cache prepared qualified
    assignment occurrence made atJudgments identifier fact observed
  exact ⟨prepared.output.context, sameId ▸ independent.2.2, independent.1, independent.2.1 fact actualMember⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublication
