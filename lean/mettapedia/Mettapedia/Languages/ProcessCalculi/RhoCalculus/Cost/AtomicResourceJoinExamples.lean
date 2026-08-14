import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceJoin
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

/-!
# Closed examples for atomic located-resource joins

The positive cases expose whole-redex and split-endpoint atomic joins.  The
negative cases distinguish absence of a purse at the interaction location,
the wrong signature at the right location, and occurrence contention between
two otherwise enabled communications.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceJoinExamples

open ParallelExamples

/-! ## Positive whole-redex and split-endpoint joins -/

def aliceSource : CostConfig ExampleGround := aliceEvent.consumed
def aliceTarget : CostConfig ExampleGround := aliceEvent.produced

theorem alice_whole_redex_is_atomic :
    AtomicResourceJoin aliceSource aliceEvent aliceTarget := by
  exact ⟨0, by simp [aliceSource], by simp [aliceTarget]⟩

theorem alice_whole_redex_is_cost_step :
    CostStep aliceSource aliceEvent.location aliceEvent.spend aliceTarget :=
  alice_whole_redex_is_atomic.toCostStep

def combinedSelection :
    FundingSelection ExampleGround channel (aliceSeal + bobSeal) where
  chosen := aliceSelection.chosen + bobSelection.chosen
  demand_eq := by
    simp [aliceSelection, bobSelection]

def splitEvent : CostedEvent ExampleGround :=
  .split channel openBody alicePayload aliceSeal bobSeal
    aliceSeal_valid bobSeal_valid combinedSelection

def splitSource : CostConfig ExampleGround := splitEvent.consumed
def splitTarget : CostConfig ExampleGround := splitEvent.produced

theorem split_endpoints_and_both_purses_are_atomic :
    AtomicResourceJoin splitSource splitEvent splitTarget := by
  exact ⟨0, by simp [splitSource], by simp [splitTarget]⟩

theorem split_receipt_measures_both_selected_heads :
    splitEvent.toSpendEvent.rawSpend = aliceSeal + bobSeal := by
  exact splitEvent.toSpendEvent_rawSpend

/-! ## Location and exact-cover rejection -/

def expectedAlicePurse : CostTerm ExampleGround :=
  .purse channel (.cons aliceSeal .empty)

theorem expected_alice_purse_is_selected :
    expectedAlicePurse ∈ aliceEvent.fundingBefore := by
  decide

def otherChannel : CostName ExampleGround := .signature {"other-channel"}

def wrongLocationPurse : CostTerm ExampleGround :=
  .purse otherChannel (.cons aliceSeal .empty)

def wrongLocationSource : CostConfig ExampleGround :=
  aliceEvent.endpoints + {wrongLocationPurse}

theorem expected_alice_purse_absent_at_wrong_location :
    expectedAlicePurse ∉ wrongLocationSource := by
  decide

theorem wrong_location_cannot_enable_join (target : CostConfig ExampleGround) :
    ¬AtomicResourceJoin wrongLocationSource aliceEvent target := by
  intro join
  exact expected_alice_purse_absent_at_wrong_location
    (Multiset.mem_of_le join.fundingBefore_le_source
      expected_alice_purse_is_selected)

def wrongSignaturePurse : CostTerm ExampleGround :=
  .purse channel (.cons bobSeal .empty)

def wrongSignatureSource : CostConfig ExampleGround :=
  aliceEvent.endpoints + {wrongSignaturePurse}

theorem expected_alice_purse_absent_with_wrong_signature :
    expectedAlicePurse ∉ wrongSignatureSource := by
  decide

theorem wrong_signature_cannot_enable_join (target : CostConfig ExampleGround) :
    ¬AtomicResourceJoin wrongSignatureSource aliceEvent target := by
  intro join
  exact expected_alice_purse_absent_with_wrong_signature
    (Multiset.mem_of_le join.fundingBefore_le_source
      expected_alice_purse_is_selected)

/-! ## Occurrence contention remains a branching choice -/

theorem shared_purse_occurrence_cannot_fund_one_parallel_join :
    ¬CostCompatibleAt contestedSource aliceEvent aliceCompetitor :=
  contested_branches_are_not_compatible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceJoinExamples
