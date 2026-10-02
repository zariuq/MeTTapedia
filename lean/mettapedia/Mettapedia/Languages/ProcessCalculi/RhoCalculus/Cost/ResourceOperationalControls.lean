import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceOperationalEquivalence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWaveControls

/-!
# Located resource support and scheduling controls

Two competing actual events are individually enabled at one source, and
each resource firing is the corresponding ordinary funded branch. Their
different targets and shared purse exclude a joint wave. Removing funding
blocks the same event even though its communicating endpoints remain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceOperationalControls

open ParallelExamples

theorem competing_resource_entries_enabled :
    (costResourceSystem String).Enables contestedSource aliceEvent.resourceEntry.2 ∧
      (costResourceSystem String).Enables contestedSource aliceCompetitor.resourceEntry.2 := by
  simpa only [CostResourceWave.enables_iff_consumed_le,
    CostResourceWave.event_resourceEntry] using ResourceWaveControls.both_contenders_enabled

theorem actual_resource_targets :
    (costResourceSystem String).fire contestedSource aliceEvent.resourceEntry.2 =
        aliceBranch.target ∧
      (costResourceSystem String).fire contestedSource aliceCompetitor.resourceEntry.2 =
        competitorBranch.target := by
  decide +kernel

theorem competing_entries_give_distinct_costSteps :
    CostStep contestedSource aliceEvent.location aliceEvent.spend aliceBranch.target ∧
      CostStep contestedSource aliceCompetitor.location aliceCompetitor.spend
        competitorBranch.target ∧
      aliceBranch.target ≠ competitorBranch.target := by
  have left := CostResourceWave.enabled_costStep contestedSource aliceEvent.resourceEntry
    competing_resource_entries_enabled.1
  have right := CostResourceWave.enabled_costStep contestedSource aliceCompetitor.resourceEntry
    competing_resource_entries_enabled.2
  rw [actual_resource_targets.1] at left
  rw [actual_resource_targets.2] at right
  exact ⟨left, right, contested_branch_targets_differ⟩

theorem endpoints_without_funding_block_resource_event :
    ¬ (costResourceSystem String).Enables aliceEvent.endpoints aliceEvent.resourceEntry.2 := by
  rw [CostResourceWave.enables_iff_consumed_le, CostResourceWave.event_resourceEntry]
  decide +kernel

theorem supported_alternatives_need_not_form_one_wave :
    (costResourceSystem String).Enables contestedSource aliceEvent.resourceEntry.2 ∧
      (costResourceSystem String).Enables contestedSource aliceCompetitor.resourceEntry.2 ∧
      ¬ (costResourceSystem String).StepEnables contestedSource
        [aliceEvent.resourceEntry, aliceCompetitor.resourceEntry] := by
  refine ⟨competing_resource_entries_enabled.1, competing_resource_entries_enabled.2, ?_⟩
  rw [CostResourceWave.stepEnables_iff_matching]
  simpa only [List.map_cons, List.map_nil, CostResourceWave.event_resourceEntry,
    CostCompatibleAt] using contested_branches_are_not_compatible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceOperationalControls
