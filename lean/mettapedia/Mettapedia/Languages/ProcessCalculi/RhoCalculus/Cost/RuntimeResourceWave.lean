import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWave
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeWave

/-!
# Runtime occurrence claims in the common resource semantics

The existing runtime wave supplies enabled candidates and disjoint source
indices. Its decoded matching satisfies the resource-wave contract, including
the exact target after all selected events fire. This connects the index-based
runtime interface to the shared concurrency theory without identifying two
equal syntax values with one source occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.GSLT.Causality.ResourceInteraction

namespace SelectedRuntimeWave

/-- Runtime occurrence separation supplies collective resource availability. -/
theorem resourceEnabled {config : RawCostConfig} (wave : SelectedRuntimeWave config) :
    (costResourceSystem String).StepEnables (decodeRawConfig config)
      (wave.events.map CostedEvent.resourceEntry) :=
  wave.toCostMatching.resourceEnabled

/-- The resource result retains exactly the existing matching's untouched
runtime frame, exposed purse tails, and communication contracta. -/
theorem resourceTarget {config : RawCostConfig} (wave : SelectedRuntimeWave config) :
    (costResourceSystem String).waveTarget (decodeRawConfig config)
        (wave.events.map CostedEvent.resourceEntry) = wave.toCostMatching.target :=
  wave.toCostMatching.resourceTarget

/-- Every worker ordering of the decoded runtime events is also a legal
execution in the common resource semantics. The located events are retained. -/
theorem resourceFires {config : RawCostConfig} (wave : SelectedRuntimeWave config)
    {schedule : List (CostedEvent String)} (permutation : wave.events.Perm schedule) :
    (costResourceSystem String).Fires (schedule.map CostedEvent.resourceEntry)
      (decodeRawConfig config) wave.toCostMatching.target := by
  rw [← wave.resourceTarget]
  exact ((costResourceSystem String).step_orders_meet
    (permutation.map CostedEvent.resourceEntry) wave.resourceEnabled).2

end SelectedRuntimeWave

/-- Actual enabled runtime candidates with collectively distinct claimed
indices have one matching in both semantics. No additional resource-fit
hypothesis is delegated to the caller. -/
theorem runtimeClaims_have_resource_execution {config : RawCostConfig}
    (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (steps : List RawRuntimeStep)
    (enabled : ∀ step ∈ steps, step ∈ runtimeCostCandidatesFromConfig config)
    (claims_nodup : (steps.flatMap RawRuntimeStep.consumedIndices).Nodup) :
    ∃ wave : SelectedRuntimeWave config,
      wave.selected.map RuntimeEventEmbedding.step = steps ∧
      (costResourceSystem String).StepEnables (decodeRawConfig config)
        (wave.events.map CostedEvent.resourceEntry) ∧
      (costResourceSystem String).Fires (wave.events.map CostedEvent.resourceEntry)
        (decodeRawConfig config) wave.toCostMatching.target := by
  obtain ⟨wave, represents⟩ := SelectedRuntimeWave.exists_of_selectedSteps
    canonical config_ok steps enabled claims_nodup
  exact ⟨wave, represents, wave.resourceEnabled, wave.resourceFires (.refl _)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
