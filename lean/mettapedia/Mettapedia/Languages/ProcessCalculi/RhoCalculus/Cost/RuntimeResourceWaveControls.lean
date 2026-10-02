import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWaveAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeResourceWave
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeExamples

/-!
# Executed runtime controls for resource waves

The independently enumerated candidates of `twoIndependentLocations` have
disjoint source claims and form a two-event resource wave. Two communications
competing for one purse remain individually enabled but cannot both belong
to a wave at that snapshot. Both controls retain source occurrence indices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeResourceWaveControls

open Mettapedia.GSLT.Causality.ResourceInteraction
open RuntimeExamples

def twoConfig : RawCostConfig := twoIndependentLocations.normalizeConfig

theorem two_canonical : twoConfig.Canonical :=
  RawCostTerm.normalizeConfig_canonical twoIndependentLocations

theorem two_wellFormed : twoConfig.Forall (fun term => term.wellFormed = true) := by
  rw [List.forall_iff_forall_mem]
  decide +kernel

theorem two_encodingCanonical : twoConfig.Forall RawCostTerm.EncodingCanonical :=
  RawCostTerm.normalizeConfig_forall_encodingCanonical twoIndependentLocations

/-- The completeness hypotheses hold for this actual configuration. Every
enabled resource entry, rather than only a supplied catalogue, is enumerated
with its labels and structural successor representation intact. -/
theorem two_resource_enumeration_complete
    (entry : (costResourceSystem String).Entry)
    (enabled : (costResourceSystem String).Enables (decodeRawConfig twoConfig) entry.2) :
    RuntimeCostStepComplete twoConfig entry.1 (CostResourceWave.event entry).spend
      ((costResourceSystem String).fire (decodeRawConfig twoConfig) entry.2) :=
  enabled_resourceEntry_complete_runtime two_canonical two_encodingCanonical
    two_wellFormed entry enabled

/-- Enumeration retains the two original locations and debits. -/
theorem two_candidate_labels :
    (runtimeCostCandidatesFromConfig twoConfig).map
      (fun step => (step.location, step.spend)) = [(pay, alice), (wrong, bob)] := by
  decide +kernel

/-- Endpoint and purse claims refer to four distinct actual source slots. -/
theorem two_candidate_claims :
    (runtimeCostCandidatesFromConfig twoConfig).map RawRuntimeStep.consumedIndices =
      [[2, 0], [3, 1]] := by
  decide +kernel

/-- Both actual candidates execute, in either order, with the same exact
resource target and the existing chronological cost trace. -/
theorem two_candidate_wave :
    ∃ wave : SelectedRuntimeWave twoConfig,
      wave.selected.map RuntimeEventEmbedding.step = runtimeCostCandidatesFromConfig twoConfig ∧
      wave.events.length = 2 ∧
      (costResourceSystem String).StepEnables (decodeRawConfig twoConfig)
        (wave.events.map CostedEvent.resourceEntry) ∧
      (costResourceSystem String).waveTarget (decodeRawConfig twoConfig)
        (wave.events.map CostedEvent.resourceEntry) = wave.toCostMatching.target ∧
      ∀ schedule, wave.events.Perm schedule →
        (costResourceSystem String).Fires (schedule.map CostedEvent.resourceEntry)
          (decodeRawConfig twoConfig) wave.toCostMatching.target ∧
        CostTrace (decodeRawConfig twoConfig) (costWaveTrace schedule)
          wave.toCostMatching.target := by
  obtain ⟨wave, represented, enabled, _⟩ := runtimeClaims_have_resource_execution
    two_canonical two_wellFormed (runtimeCostCandidatesFromConfig twoConfig)
    (fun _ member => member) (by decide +kernel)
  refine ⟨wave, represented, ?_, enabled, wave.resourceTarget, ?_⟩
  · have count := congrArg List.length represented
    have candidates : (runtimeCostCandidatesFromConfig twoConfig).length = 2 := by
      decide +kernel
    simpa only [SelectedRuntimeWave.events, List.length_map, candidates] using count
  · intro schedule permutation
    exact ⟨wave.resourceFires permutation,
      wave.toCostMatching.permutation_serializes permutation.symm⟩

/-- Each enumerated candidate also has the exact labelled single-instance
comparison, with only the established structural residual boundary. -/
theorem two_candidate_resource_firing (step : RawRuntimeStep)
    (member : step ∈ runtimeCostCandidatesFromConfig twoConfig) :
    ∃ entry : (costResourceSystem String).Entry,
      entry.1 = decodeCostName step.location ∧
      (CostResourceWave.event entry).spend = decodeCostSig step.spend ∧
      (costResourceSystem String).Enables (decodeRawConfig twoConfig) entry.2 ∧
      step.residual.normalizeConfig.StructurallyRepresents
        ((costResourceSystem String).fire (decodeRawConfig twoConfig) entry.2) :=
  runtimeCandidate_has_enabled_resourceEntry two_canonical two_wellFormed member

def contestedConfig : RawCostConfig :=
  (parList [whole alice, whole alice, purse pay [alice]]).normalizeConfig

theorem contested_canonical : contestedConfig.Canonical :=
  RawCostTerm.normalizeConfig_canonical
    (parList [whole alice, whole alice, purse pay [alice]])

theorem contested_wellFormed :
    contestedConfig.Forall (fun term => term.wellFormed = true) := by
  rw [List.forall_iff_forall_mem]
  decide +kernel

/-- The endpoint occurrences differ, but the purse occurrence is shared. -/
theorem contested_candidate_claims :
    (runtimeCostCandidatesFromConfig contestedConfig).map RawRuntimeStep.consumedIndices =
      [[1, 0], [2, 0]] := by
  decide +kernel

/-- Every contender individually has a funded resource transition; contention
does not mean either alternative is absent from the operational relation. -/
theorem contested_individually_enabled (step : RawRuntimeStep)
    (member : step ∈ runtimeCostCandidatesFromConfig contestedConfig) :
    ∃ entry : (costResourceSystem String).Entry,
      entry.1 = decodeCostName step.location ∧
      (CostResourceWave.event entry).spend = decodeCostSig step.spend ∧
      (costResourceSystem String).Enables (decodeRawConfig contestedConfig) entry.2 ∧
      step.residual.normalizeConfig.StructurallyRepresents
        ((costResourceSystem String).fire (decodeRawConfig contestedConfig) entry.2) :=
  runtimeCandidate_has_enabled_resourceEntry
    contested_canonical contested_wellFormed member

/-- The actual conflicting candidates cannot be submitted together as a
selected wave, despite their individual enablement. -/
theorem contested_not_one_wave :
    ¬∃ wave : SelectedRuntimeWave contestedConfig,
      wave.selected.map RuntimeEventEmbedding.step =
        runtimeCostCandidatesFromConfig contestedConfig := by
  rintro ⟨wave, represented⟩
  have claimed : ((wave.selected.map RuntimeEventEmbedding.step).flatMap
      RawRuntimeStep.consumedIndices).Nodup := by
    rw [List.flatMap_map]
    exact wave.indices_nodup
  rw [represented] at claimed
  have conflict : ¬((runtimeCostCandidatesFromConfig contestedConfig).flatMap
      RawRuntimeStep.consumedIndices).Nodup := by decide +kernel
  exact conflict claimed

/-- The conflict also fails the semantic resource test: the two candidates
consume four occurrences from a configuration with only three. This holds
for every actual occurrence embedding of the returned candidates. -/
theorem contested_not_resource_enabled
    (embeddings : List (RuntimeEventEmbedding contestedConfig))
    (represented : embeddings.map RuntimeEventEmbedding.step =
      runtimeCostCandidatesFromConfig contestedConfig) :
    ¬(costResourceSystem String).StepEnables (decodeRawConfig contestedConfig)
      (embeddings.map fun embedding => embedding.event.resourceEntry) := by
  intro enabled
  have fits : (embeddings.map fun embedding => embedding.event.consumed).sum ≤
      decodeRawConfig contestedConfig := by
    simpa only [List.map_map, CostResourceWave.event_resourceEntry,
      Function.comp_def] using (CostResourceWave.stepEnables_iff _ _).mp enabled
  have claimEq : embeddings.flatMap RuntimeEventEmbedding.indices =
      (runtimeCostCandidatesFromConfig contestedConfig).flatMap
        RawRuntimeStep.consumedIndices := by
    rw [← represented, List.flatMap_map]
    rfl
  have demand : ((embeddings.map fun (embedding : RuntimeEventEmbedding contestedConfig) =>
      embedding.event.consumed).sum).card = 4 := by
    rw [RuntimeEventEmbedding.consumed_sum_card, claimEq]
    decide +kernel
  have available : (decodeRawConfig contestedConfig).card = 3 := by decide +kernel
  have bound := Multiset.card_le_card fits
  rw [demand, available] at bound
  omega

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeResourceWaveControls
