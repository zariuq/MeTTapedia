import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Parallel

/-!
# Event-count budgets for parallel cost-rho traces

A concurrent budget counts funded reaction occurrences, not scheduler waves.
Each wave contributes the cardinality of its occurrence-preserving receipt.
This keeps a one-event wave and one event inside a wider wave at the same cost,
and makes increasing a budget a monotone relaxation of the same relation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

namespace ParallelCostStep

/-- A concurrent step always emits at least one receipt occurrence. -/
theorem receipt_ne_zero {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) : receipt ≠ 0 := by
  rintro rfl
  obtain ⟨matching, _source, events_nonempty, receipt_zero, _target⟩ := step
  apply events_nonempty
  have card_zero := congrArg Multiset.card receipt_zero
  have length_zero : matching.events.length = 0 := by
    simpa [CostMatching.receipt, costWaveReceipt] using card_zero
  simpa using length_zero

end ParallelCostStep

namespace LocatedTokenCover

variable {Ground : Type u} {location : CostName Ground} {demand : CostSig Ground}
  {available residual : Multiset (LocatedPurse Ground)}

/-- Forget only the untouched frame of a located cover, retaining the exact
selected purse occurrences needed by one concurrent event. -/
def toFundingSelection
    (cover : LocatedTokenCover location demand available residual) :
    FundingSelection Ground location demand where
  chosen := cover.chosen
  demand_eq := cover.demand_eq

@[simp]
theorem toFundingSelection_before
    (cover : LocatedTokenCover location demand available residual) :
    cover.toFundingSelection.before = cover.selectedBefore := rfl

@[simp]
theorem toFundingSelection_after
    (cover : LocatedTokenCover location demand available residual) :
    cover.toFundingSelection.after = cover.selectedAfter := rfl

end LocatedTokenCover

/-- Every ordinary funded COMM is available as a singleton concurrent wave.
Together with wave serialization, this is the one-step outcome-set equality:
parallelism adds commuting groupings, not new or missing reductions. -/
theorem costStep_has_singleton_parallel {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground}
    {spend : CostSig Ground} (step : CostStep source location spend target) :
    ∃ receipt, ParallelCostStep source receipt target := by
  cases step with
  | @wholeRecvSend context available residual channel body payload outerSig
      signature_valid cover =>
      let event : CostedEvent Ground := .wholeRecvSend location body payload
        spend signature_valid cover.toFundingSelection
      let frame : CostConfig Ground :=
        context + LocatedPurse.configComponents cover.untouched
      let matching : CostMatching Ground :=
        { source := context +
            (.signed (.par (.recv location body) (.send location payload))
              spend ::ₘ 0) +
            LocatedPurse.configComponents available
          events := [event]
          frame := frame
          source_eq := by
            rw [cover.available_decomposition]
            simp [costWaveSource, event, frame, CostedEvent.consumed,
              CostedEvent.endpoints, CostedEvent.fundingBefore,
              LocatedPurse.configComponents]
            rw [← Multiset.singleton_add]
            ac_rfl }
      refine ⟨matching.receipt, matching, by simp [matching], by simp, rfl, ?_⟩
      rw [cover.residual_decomposition]
      simp [matching, CostMatching.target, costWaveTarget, event, frame,
        CostedEvent.produced, CostedEvent.contractum,
        CostedEvent.fundingAfter, LocatedPurse.configComponents]
      ac_rfl
  | @wholeSendRecv context available residual channel body payload outerSig
      signature_valid cover =>
      let event : CostedEvent Ground := .wholeSendRecv location body payload
        spend signature_valid cover.toFundingSelection
      let frame : CostConfig Ground :=
        context + LocatedPurse.configComponents cover.untouched
      let matching : CostMatching Ground :=
        { source := context +
            (.signed (.par (.send location payload) (.recv location body))
              spend ::ₘ 0) +
            LocatedPurse.configComponents available
          events := [event]
          frame := frame
          source_eq := by
            rw [cover.available_decomposition]
            simp [costWaveSource, event, frame, CostedEvent.consumed,
              CostedEvent.endpoints, CostedEvent.fundingBefore,
              LocatedPurse.configComponents]
            rw [← Multiset.singleton_add]
            ac_rfl }
      refine ⟨matching.receipt, matching, by simp [matching], by simp, rfl, ?_⟩
      rw [cover.residual_decomposition]
      simp [matching, CostMatching.target, costWaveTarget, event, frame,
        CostedEvent.produced, CostedEvent.contractum,
        CostedEvent.fundingAfter, LocatedPurse.configComponents]
      ac_rfl
  | @split context available residual channel body payload recvSeal sendSeal
      recv_valid send_valid cover =>
      let event : CostedEvent Ground := .split location body payload
        recvSeal sendSeal recv_valid send_valid cover.toFundingSelection
      let frame : CostConfig Ground :=
        context + LocatedPurse.configComponents cover.untouched
      let matching : CostMatching Ground :=
        { source := context + (.signed (.recv location body) recvSeal ::ₘ 0) +
            (.signed (.send location payload) sendSeal ::ₘ 0) +
            LocatedPurse.configComponents available
          events := [event]
          frame := frame
          source_eq := by
            rw [cover.available_decomposition]
            simp [costWaveSource, event, frame, CostedEvent.consumed,
              CostedEvent.endpoints, CostedEvent.fundingBefore,
              LocatedPurse.configComponents]
            rw [← Multiset.singleton_add, ← Multiset.singleton_add]
            ac_rfl }
      refine ⟨matching.receipt, matching, by simp [matching], by simp, rfl, ?_⟩
      rw [cover.residual_decomposition]
      simp [matching, CostMatching.target, costWaveTarget, event, frame,
        CostedEvent.produced, CostedEvent.contractum,
        CostedEvent.fundingAfter, LocatedPurse.configComponents]
      ac_rfl

namespace CostTrace

/-- Concatenate two ordinary cost-step traces at their common state. -/
theorem append {Ground : Type u}
    {source middle target : CostConfig Ground}
    {leftTrace rightTrace : List (CostName Ground × CostSig Ground)}
    (left : CostTrace source leftTrace middle)
    (right : CostTrace middle rightTrace target) :
    CostTrace source (leftTrace ++ rightTrace) target := by
  induction left with
  | nil => simpa using right
  | cons head tail ih =>
      exact CostTrace.cons head (ih right)

end CostTrace

/-- A finite sequence of concurrent waves, indexed by the exact number of
funded reaction occurrences emitted across all waves. -/
inductive ParallelCostTrace {Ground : Type u} :
    CostConfig Ground →
    Multiset (SpendEvent Ground (CostName Ground)) →
    CostConfig Ground → Nat → Prop where
  | nil (config : CostConfig Ground) : ParallelCostTrace config 0 config 0
  | cons {source middle target : CostConfig Ground}
      {waveReceipt tailReceipt :
        Multiset (SpendEvent Ground (CostName Ground))}
      {tailCount : Nat}
      (head : ParallelCostStep source waveReceipt middle)
      (tail : ParallelCostTrace middle tailReceipt target tailCount) :
      ParallelCostTrace source (waveReceipt + tailReceipt) target
        (waveReceipt.card + tailCount)

namespace ParallelCostTrace

/-- The trace index is not an auxiliary counter: it is exactly the cardinality
of the complete occurrence receipt. -/
theorem count_eq_receipt_card {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count : Nat} (trace : ParallelCostTrace source receipt target count) :
    count = receipt.card := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simp only [Multiset.card_add]
      omega

/-- Every nonempty concurrent trace consumes a positive event budget. -/
theorem positive_of_receipt_ne_zero {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count : Nat} (trace : ParallelCostTrace source receipt target count)
    (nonempty : receipt ≠ 0) : 0 < count := by
  rw [trace.count_eq_receipt_card]
  exact Multiset.card_pos.mpr nonempty

/-- Every concurrent trace is an ordinary interleaving trace.  Wave boundaries
are erased, but no event occurrence or target state is changed. -/
theorem serializes {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    {count : Nat} (trace : ParallelCostTrace source receipt target count) :
    ∃ labels, CostTrace source labels target := by
  induction trace with
  | nil => exact ⟨[], CostTrace.nil _⟩
  | @cons source middle target waveReceipt tailReceipt tailCount head tail ih =>
      obtain ⟨matching, source_eq, _nonempty, _receipt_eq, target_eq⟩ := head
      obtain ⟨tailLabels, tailTrace⟩ := ih
      have waveTrace : CostTrace source (costWaveTrace matching.events) middle := by
        simpa [source_eq, target_eq] using matching.serializes
      exact ⟨costWaveTrace matching.events ++ tailLabels,
        waveTrace.append tailTrace⟩

end ParallelCostTrace

/-- Every ordinary interleaving trace is also a concurrent trace, using
singleton waves.  This is the reverse outcome inclusion. -/
theorem costTrace_has_parallel {Ground : Type u}
    {source target : CostConfig Ground}
    {labels : List (CostName Ground × CostSig Ground)}
    (trace : CostTrace source labels target) :
    ∃ receipt count, ParallelCostTrace source receipt target count := by
  induction trace with
  | nil => exact ⟨0, 0, ParallelCostTrace.nil _⟩
  | cons head tail ih =>
      obtain ⟨headReceipt, headParallel⟩ := costStep_has_singleton_parallel head
      obtain ⟨tailReceipt, tailCount, tailParallel⟩ := ih
      exact ⟨headReceipt + tailReceipt, headReceipt.card + tailCount,
        ParallelCostTrace.cons headParallel tailParallel⟩

/-- Parallel-wave reachability and ordinary interleaving reachability have
exactly the same source/target outcome set. -/
theorem parallel_reachable_iff_interleaving_reachable {Ground : Type u}
    {source target : CostConfig Ground} :
    (∃ receipt count, ParallelCostTrace source receipt target count) ↔
      (∃ labels, CostTrace source labels target) := by
  constructor
  · rintro ⟨receipt, count, trace⟩
    exact trace.serializes
  · rintro ⟨labels, trace⟩
    exact costTrace_has_parallel trace

/-- A bounded concurrent execution is an exact trace whose event count is at
most the allowance.  Exhaustion and quiescence remain separate observations;
this predicate only states what a budget permits. -/
def ParallelRunsWithin {Ground : Type u} (fuel : Nat)
    (source : CostConfig Ground)
    (receipt : Multiset (SpendEvent Ground (CostName Ground)))
    (target : CostConfig Ground) : Prop :=
  ∃ used, ParallelCostTrace source receipt target used ∧ used ≤ fuel

/-- Increasing an event budget cannot remove an admitted concurrent trace. -/
theorem parallelRunsWithin_mono {Ground : Type u}
    {small large : Nat} (budget_le : small ≤ large)
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (run : ParallelRunsWithin small source receipt target) :
    ParallelRunsWithin large source receipt target := by
  obtain ⟨used, trace, within⟩ := run
  exact ⟨used, trace, within.trans budget_le⟩

/-- Zero event fuel admits only the empty receipt. -/
theorem parallelRunsWithin_zero_receipt {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (run : ParallelRunsWithin 0 source receipt target) : receipt = 0 := by
  obtain ⟨used, trace, within⟩ := run
  have used_zero : used = 0 := Nat.eq_zero_of_le_zero within
  have card_zero : receipt.card = 0 := by
    rw [← trace.count_eq_receipt_card, used_zero]
  exact Multiset.card_eq_zero.mp card_zero

/-- A positive concurrent step cannot be admitted with zero event fuel. -/
theorem parallelStep_not_within_zero {Ground : Type u}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) :
    ¬ParallelRunsWithin 0 source receipt target := by
  intro run
  exact step.receipt_ne_zero (parallelRunsWithin_zero_receipt run)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
