import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Parallel

/-!
# Closed examples for parallel cost-accounted rho

These examples exercise the two distinctions that a threaded implementation
must preserve: same-channel events can be compatible when their resource
occurrences are disjoint, while events competing for one purse occurrence are
alternative branches rather than one wave.  Duplicate event labels remain
duplicate receipt occurrences.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.ParallelExamples

abbrev ExampleGround := String

def channel : CostName ExampleGround := .signature {"channel"}
def aliceSeal : CostSig ExampleGround := {"alice"}
def bobSeal : CostSig ExampleGround := {"bob"}

theorem aliceSeal_valid : aliceSeal.RuntimeValid := by
  simp [CostSig.RuntimeValid, aliceSeal]

theorem bobSeal_valid : bobSeal.RuntimeValid := by
  simp [CostSig.RuntimeValid, bobSeal]

def aliceSelection : FundingSelection ExampleGround channel aliceSeal where
  chosen := {⟨aliceSeal, .empty, aliceSeal_valid⟩}
  demand_eq := by simp

def bobSelection : FundingSelection ExampleGround channel bobSeal where
  chosen := {⟨bobSeal, .empty, bobSeal_valid⟩}
  demand_eq := by simp

def openBody : CostTerm ExampleGround := .drop (.bvar 0)
def alicePayload : CostTerm ExampleGround := .signed .nil aliceSeal
def bobPayload : CostTerm ExampleGround := .signed .nil bobSeal

/-- First same-channel event, funded by an Alice purse occurrence. -/
def aliceEvent : CostedEvent ExampleGround :=
  .wholeRecvSend channel openBody alicePayload aliceSeal aliceSeal_valid
    aliceSelection

/-- A distinct same-channel event, funded by a Bob purse occurrence. -/
def bobEvent : CostedEvent ExampleGround :=
  .wholeRecvSend channel openBody bobPayload bobSeal bobSeal_valid bobSelection

/-- A second endpoint occurrence demanding the same Alice purse shape. -/
def aliceCompetitor : CostedEvent ExampleGround :=
  .wholeRecvSend channel openBody bobPayload aliceSeal aliceSeal_valid
    aliceSelection

def sameChannelSource : CostConfig ExampleGround :=
  costWaveSource [aliceEvent, bobEvent] 0

/-- Same-channel events are compatible when both endpoint and purse
occurrences are disjoint. -/
theorem same_channel_disjoint_events_compatible :
    CostCompatibleAt sameChannelSource aliceEvent bobEvent := by
  exact ⟨0, rfl⟩

/-- The compatible same-channel pair has the full costed diamond. -/
theorem same_channel_disjoint_events_diamond :
    CostedDiamond sameChannelSource aliceEvent bobEvent :=
  compatible_costed_diamond same_channel_disjoint_events_compatible

/-- Swapping a serialization preserves the occurrence bag of receipts. -/
theorem swapped_same_channel_receipt_invariant :
    costWaveReceipt [bobEvent, aliceEvent] =
      costWaveReceipt [aliceEvent, bobEvent] := by
  exact costWaveReceipt_eq_of_perm (List.Perm.swap aliceEvent bobEvent [])

/-- Swapping the two events is still an ordinary interleaving between the
same source and target. -/
theorem swapped_same_channel_serializes :
    CostTrace sameChannelSource (costWaveTrace [bobEvent, aliceEvent])
      (costWaveTarget [aliceEvent, bobEvent] 0) := by
  exact costWave_permutation_serializes
    (List.Perm.swap aliceEvent bobEvent []) 0

/-- The corresponding wave-pomsets are isomorphic, not merely equal in total
cost. -/
noncomputable def swapped_same_channel_receipt_iso :
    CausalReceiptIso (costWaveCausalReceipt [bobEvent, aliceEvent])
      (costWaveCausalReceipt [aliceEvent, bobEvent]) :=
  costWaveCausalReceipt_iso_of_perm (List.Perm.swap aliceEvent bobEvent [])

/-- Identical labels remain two distinct receipt occurrences. -/
theorem duplicate_event_receipts_are_not_deduplicated :
    (costWaveReceipt [aliceEvent, aliceEvent]).card = 2 := by
  rfl

/-- The two identical-label occurrences are nevertheless independent events
inside the wave pomset. -/
theorem duplicate_event_occurrences_are_independent :
    (costWaveCausalReceipt [aliceEvent, aliceEvent]).Independent
      ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  rw [costWaveCausalReceipt_independent_iff]
  decide

/-! ## One-purse contention preserves two alternative branches -/

def contestedPurse : CostTerm ExampleGround :=
  .purse channel (.cons aliceSeal .empty)

/-- Two endpoint groups but only one Alice purse occurrence. -/
def contestedSource : CostConfig ExampleGround :=
  aliceEvent.endpoints + aliceCompetitor.endpoints +
    aliceEvent.fundingBefore

def aliceBranch : CostMatching ExampleGround where
  source := contestedSource
  events := [aliceEvent]
  frame := aliceCompetitor.endpoints
  source_eq := by
    simp [contestedSource, costWaveSource, CostedEvent.consumed]
    ac_rfl

def competitorBranch : CostMatching ExampleGround where
  source := contestedSource
  events := [aliceCompetitor]
  frame := aliceEvent.endpoints
  source_eq := by
    simp [contestedSource, costWaveSource, CostedEvent.consumed,
      aliceEvent, aliceCompetitor, CostedEvent.fundingBefore]
    ac_rfl

/-- The first contender remains a legal branch. -/
theorem contested_alice_branch_preserved :
    ParallelCostStep contestedSource aliceBranch.receipt aliceBranch.target := by
  exact ⟨aliceBranch, rfl, by simp [aliceBranch], rfl, rfl⟩

/-- The second contender remains a separate legal branch. -/
theorem contested_competitor_branch_preserved :
    ParallelCostStep contestedSource competitorBranch.receipt
      competitorBranch.target := by
  exact ⟨competitorBranch, rfl, by simp [competitorBranch], rfl, rfl⟩

/-- The two branches have observably different contracta. -/
theorem contested_branch_targets_differ :
    aliceBranch.target ≠ competitorBranch.target := by
  decide

theorem contested_purse_occurs_once :
    contestedSource.count contestedPurse = 1 := by
  decide

theorem aliceEvent_uses_contestedPurse :
    contestedPurse ∈ aliceEvent.fundingBefore := by
  decide

theorem aliceCompetitor_uses_contestedPurse :
    contestedPurse ∈ aliceCompetitor.fundingBefore := by
  decide

/-- The two preserved branches cannot be combined into one wave because they
compete for the same single purse occurrence. -/
theorem contested_branches_are_not_compatible :
    ¬CostCompatibleAt contestedSource aliceEvent aliceCompetitor :=
  shared_single_purse_conflicts contestedPurse contested_purse_occurs_once
    aliceEvent_uses_contestedPurse aliceCompetitor_uses_contestedPurse

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.ParallelExamples
