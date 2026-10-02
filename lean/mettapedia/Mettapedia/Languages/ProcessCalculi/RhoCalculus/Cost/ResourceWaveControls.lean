import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWave
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

/-!
# Resource-wave controls on actual funded rho events

The existing same-channel and contested-purse configurations distinguish
compatible parallel work from scheduling a winner among conflicting matches.
Equal event values retain multiplicity when the source has enough occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWaveControls

open ParallelExamples

/-- A shared channel alone creates no conflict: both funded events are chosen. -/
theorem same_channel_selects_both :
    CostResourceWave.select sameChannelSource [aliceEvent, bobEvent] =
      ([aliceEvent, bobEvent], []) := by
  rfl

/-- One purse funds either contender individually. -/
theorem both_contenders_enabled :
    aliceEvent.consumed ≤ contestedSource ∧
      aliceCompetitor.consumed ≤ contestedSource := by
  decide +kernel

/-- Declared priority selects the first contender and retains the other. -/
theorem contested_selects_first :
    CostResourceWave.select contestedSource [aliceEvent, aliceCompetitor] =
      ([aliceEvent], [aliceCompetitor]) := by
  rfl

/-- Reversing the catalogue changes the selected branch. -/
theorem reversing_priority_selects_competitor :
    CostResourceWave.select contestedSource [aliceCompetitor, aliceEvent] =
      ([aliceCompetitor], [aliceEvent]) := by
  rfl

/-- The selected matching recovers the existing ordinary Alice branch. -/
theorem alice_selection_target :
    (CostResourceWave.matching contestedSource [aliceEvent, aliceCompetitor]).target =
      aliceBranch.target := by
  decide +kernel

/-- The opposite priority recovers the other existing ordinary branch. -/
theorem competitor_selection_target :
    (CostResourceWave.matching contestedSource [aliceCompetitor, aliceEvent]).target =
      competitorBranch.target := by
  decide +kernel

/-- Atomic valid waves can have different observable outcomes when the
catalogue contains competing matches. Serializability does not remove choice. -/
theorem priority_changes_result :
    (CostResourceWave.matching contestedSource [aliceEvent, aliceCompetitor]).target ≠
      (CostResourceWave.matching contestedSource [aliceCompetitor, aliceEvent]).target := by
  rw [alice_selection_target, competitor_selection_target]
  exact contested_branch_targets_differ

/-- Two equal events are selected when both resource occurrences are present. -/
theorem duplicate_events_retained :
    CostResourceWave.select (costWaveSource [aliceEvent, aliceEvent] 0)
        [aliceEvent, aliceEvent] = ([aliceEvent, aliceEvent], []) := by
  rfl

/-- The selected receipt has two occurrences, even though their labels agree. -/
theorem duplicate_receipt_card :
    (CostResourceWave.matching (costWaveSource [aliceEvent, aliceEvent] 0)
      [aliceEvent, aliceEvent]).receipt.card = 2 := by
  rfl

/-- Catalogue quiescence is weaker than absence of an actual funded reaction. -/
theorem empty_catalogue_does_not_exclude_a_step :
    (CostResourceWave.select contestedSource []).1 = [] ∧
      ParallelCostStep contestedSource aliceBranch.receipt aliceBranch.target :=
  ⟨rfl, contested_alice_branch_preserved⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWaveControls
