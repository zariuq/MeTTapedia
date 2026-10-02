import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

/-!
# Chronology is not determined by a parallel receipt

Two disjoint, funded communications on the same channel have legal
serializations with a common source, target and receipt bag. Their ordered
labels differ. An occurrence bag therefore cannot recover the chosen
linearization, even when restricted to serializations of this one wave.
This does not change the causal receipt or impose an order on independent
events: a chronological observation is additional information.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.TemporalReceiptBoundary

open ParallelExamples

/-- Both schedules execute through the original located funded relation. -/
theorem both_orders_execute :
    CostTrace sameChannelSource (costWaveTrace [aliceEvent, bobEvent])
        (costWaveTarget [aliceEvent, bobEvent] 0) ∧
      CostTrace sameChannelSource (costWaveTrace [bobEvent, aliceEvent])
        (costWaveTarget [aliceEvent, bobEvent] 0) :=
  ⟨costWave_serializes [aliceEvent, bobEvent] 0,
    swapped_same_channel_serializes⟩

/-- A concrete chronological observation distinguishes the serializations. -/
theorem chronological_words_differ :
    costWaveTrace [aliceEvent, bobEvent] ≠
      costWaveTrace [bobEvent, aliceEvent] := by
  decide +kernel

/-- Accounting retains every contribution but forgets this linear order. -/
theorem same_receipt :
    costWaveReceipt [aliceEvent, bobEvent] =
      costWaveReceipt [bobEvent, aliceEvent] :=
  swapped_same_channel_receipt_invariant.symm

/-- There is no reconstruction from the receipt bag that is correct for
every legal ordering of this actual two-event wave. -/
theorem no_chronology_from_receipt :
    ¬∃ readout : Multiset (SpendEvent ExampleGround (CostName ExampleGround)) →
        List (CostName ExampleGround × CostSig ExampleGround),
      ∀ schedule : List (CostedEvent ExampleGround),
        schedule.Perm [aliceEvent, bobEvent] →
          readout (costWaveReceipt schedule) = costWaveTrace schedule := by
  rintro ⟨readout, correct⟩
  have forward := correct [aliceEvent, bobEvent] (.refl _)
  have backward := correct [bobEvent, aliceEvent]
    (List.Perm.swap aliceEvent bobEvent [])
  rw [← same_receipt] at backward
  exact chronological_words_differ (forward.symm.trans backward)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.TemporalReceiptBoundary
