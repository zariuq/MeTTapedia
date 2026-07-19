import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Parallel

/-!
# Atomic located-resource joins

A funded communication is one atomic resource transformation: its endpoint
occurrences and its selected located purse-head occurrences disappear
together, while its contractum and the corresponding purse tails appear
together.  This decomposition is independent of any runtime reservation or
locking protocol.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- One event is enabled atomically in a disjoint resource frame.  The two
equations expose the complete consumed and produced resource families rather
than treating atomicity as an operational scheduling convention. -/
def AtomicResourceJoin {Ground : Type u}
    (source : CostConfig Ground) (event : CostedEvent Ground)
    (target : CostConfig Ground) : Prop :=
  ∃ frame : CostConfig Ground,
    source = frame + event.consumed ∧
      target = frame + event.produced

namespace AtomicResourceJoin

variable {Ground : Type u} {source target : CostConfig Ground}
  {event : CostedEvent Ground}

/-- An atomic resource join is an ordinary funded cost step. -/
theorem toCostStep (join : AtomicResourceJoin source event target) :
    CostStep source event.surface event.spend target := by
  obtain ⟨frame, source_eq, target_eq⟩ := join
  rw [source_eq, target_eq]
  exact event.toCostStepIn frame

/-- Every resource consumed by the event is present in the source with at
least the required occurrence multiplicity. -/
theorem consumed_le_source (join : AtomicResourceJoin source event target) :
    event.consumed ≤ source := by
  obtain ⟨frame, source_eq, _target_eq⟩ := join
  rw [source_eq]
  exact Multiset.le_add_left _ _

/-- Endpoint occurrences of an atomic event are present in its source. -/
theorem endpoints_le_source (join : AtomicResourceJoin source event target) :
    event.endpoints ≤ source := by
  exact le_trans (Multiset.le_add_right _ _) join.consumed_le_source

/-- Every selected located purse occurrence is present in the source. -/
theorem fundingBefore_le_source
    (join : AtomicResourceJoin source event target) :
    event.fundingBefore ≤ source := by
  exact le_trans (Multiset.le_add_left _ _) join.consumed_le_source

/-- Every product of the event, including exposed purse tails, occurs in the
target with at least the produced multiplicity. -/
theorem produced_le_target (join : AtomicResourceJoin source event target) :
    event.produced ≤ target := by
  obtain ⟨frame, _source_eq, target_eq⟩ := join
  rw [target_eq]
  exact Multiset.le_add_left _ _

end AtomicResourceJoin

/-- Every declarative funded cost step has an exact atomic resource
decomposition.  This direction reconstructs the local event and moves only
the cover's untouched purse occurrences into the frame. -/
theorem CostStep.exists_atomicResourceJoin
    {source : CostConfig Ground} {surface : CostName Ground}
    {spend : CostSig Ground} {target : CostConfig Ground}
    (step : CostStep source surface spend target) :
    ∃ event : CostedEvent Ground,
      event.surface = surface ∧ event.spend = spend ∧
        AtomicResourceJoin source event target := by
  cases step with
  | @wholeRecvSend context available residual channel body payload outerSig
      signature_valid cover =>
      let funding : FundingSelection Ground surface spend :=
        ⟨cover.chosen, cover.demand_eq⟩
      let event := CostedEvent.wholeRecvSend surface body payload spend
        signature_valid funding
      refine ⟨event, rfl, rfl, ?_⟩
      refine ⟨context + LocatedPurse.configComponents cover.untouched, ?_, ?_⟩
      · calc
          context +
                (.signed (.par (.recv surface body) (.send surface payload))
                  spend ::ₘ 0) +
              LocatedPurse.configComponents available =
              context +
                (.signed (.par (.recv surface body) (.send surface payload))
                  spend ::ₘ 0) +
                LocatedPurse.configComponents
                  (cover.selectedBefore + cover.untouched) :=
            congrArg (fun purses =>
              context +
                (.signed (.par (.recv surface body) (.send surface payload))
                  spend ::ₘ 0) + LocatedPurse.configComponents purses)
              cover.available_decomposition
          _ = context + LocatedPurse.configComponents cover.untouched +
                event.consumed := by
            simp only [event, funding, CostedEvent.consumed,
              CostedEvent.endpoints, CostedEvent.fundingBefore,
              FundingSelection.before, LocatedTokenCover.selectedBefore,
              LocatedPurse.configComponents, Multiset.map_add]
            ac_rfl
      · calc
          context + (body.commSubst payload).components +
              LocatedPurse.configComponents residual =
              context + (body.commSubst payload).components +
                LocatedPurse.configComponents
                  (cover.selectedAfter + cover.untouched) :=
            congrArg (fun purses => context +
              (body.commSubst payload).components +
              LocatedPurse.configComponents purses)
              cover.residual_decomposition
          _ = context + LocatedPurse.configComponents cover.untouched +
                event.produced := by
            simp only [event, funding, CostedEvent.produced,
              CostedEvent.contractum, CostedEvent.fundingAfter,
              FundingSelection.after, LocatedTokenCover.selectedAfter,
              LocatedPurse.configComponents, Multiset.map_add]
            ac_rfl
  | @wholeSendRecv context available residual channel body payload outerSig
      signature_valid cover =>
      let funding : FundingSelection Ground surface spend :=
        ⟨cover.chosen, cover.demand_eq⟩
      let event := CostedEvent.wholeSendRecv surface body payload spend
        signature_valid funding
      refine ⟨event, rfl, rfl, ?_⟩
      refine ⟨context + LocatedPurse.configComponents cover.untouched, ?_, ?_⟩
      · calc
          context +
                (.signed (.par (.send surface payload) (.recv surface body))
                  spend ::ₘ 0) +
              LocatedPurse.configComponents available =
              context +
                (.signed (.par (.send surface payload) (.recv surface body))
                  spend ::ₘ 0) +
                LocatedPurse.configComponents
                  (cover.selectedBefore + cover.untouched) :=
            congrArg (fun purses =>
              context +
                (.signed (.par (.send surface payload) (.recv surface body))
                  spend ::ₘ 0) + LocatedPurse.configComponents purses)
              cover.available_decomposition
          _ = context + LocatedPurse.configComponents cover.untouched +
                event.consumed := by
            simp only [event, funding, CostedEvent.consumed,
              CostedEvent.endpoints, CostedEvent.fundingBefore,
              FundingSelection.before, LocatedTokenCover.selectedBefore,
              LocatedPurse.configComponents, Multiset.map_add]
            ac_rfl
      · calc
          context + (body.commSubst payload).components +
              LocatedPurse.configComponents residual =
              context + (body.commSubst payload).components +
                LocatedPurse.configComponents
                  (cover.selectedAfter + cover.untouched) :=
            congrArg (fun purses => context +
              (body.commSubst payload).components +
              LocatedPurse.configComponents purses)
              cover.residual_decomposition
          _ = context + LocatedPurse.configComponents cover.untouched +
                event.produced := by
            simp only [event, funding, CostedEvent.produced,
              CostedEvent.contractum, CostedEvent.fundingAfter,
              FundingSelection.after, LocatedTokenCover.selectedAfter,
              LocatedPurse.configComponents, Multiset.map_add]
            ac_rfl
  | @split context available residual channel body payload recvSeal sendSeal
      recv_seal_valid send_seal_valid cover =>
      let funding : FundingSelection Ground surface (recvSeal + sendSeal) :=
        ⟨cover.chosen, cover.demand_eq⟩
      let event := CostedEvent.split surface body payload recvSeal sendSeal recv_seal_valid
        send_seal_valid funding
      refine ⟨event, rfl, rfl, ?_⟩
      refine ⟨context + LocatedPurse.configComponents cover.untouched, ?_, ?_⟩
      · calc
          context + (.signed (.recv surface body) recvSeal ::ₘ 0) +
                (.signed (.send surface payload) sendSeal ::ₘ 0) +
              LocatedPurse.configComponents available =
              context + (.signed (.recv surface body) recvSeal ::ₘ 0) +
                (.signed (.send surface payload) sendSeal ::ₘ 0) +
                LocatedPurse.configComponents
                  (cover.selectedBefore + cover.untouched) :=
            congrArg (fun purses =>
              context + (.signed (.recv surface body) recvSeal ::ₘ 0) +
                (.signed (.send surface payload) sendSeal ::ₘ 0) +
                LocatedPurse.configComponents purses)
              cover.available_decomposition
          _ = context + LocatedPurse.configComponents cover.untouched +
                event.consumed := by
            simp only [event, funding, CostedEvent.consumed,
              CostedEvent.endpoints, CostedEvent.fundingBefore,
              FundingSelection.before, LocatedTokenCover.selectedBefore,
              LocatedPurse.configComponents, Multiset.map_add]
            ac_rfl
      · calc
          context + (body.commSubst payload).components +
              LocatedPurse.configComponents residual =
              context + (body.commSubst payload).components +
                LocatedPurse.configComponents
                  (cover.selectedAfter + cover.untouched) :=
            congrArg (fun purses => context +
              (body.commSubst payload).components +
              LocatedPurse.configComponents purses)
              cover.residual_decomposition
          _ = context + LocatedPurse.configComponents cover.untouched +
                event.produced := by
            simp only [event, funding, CostedEvent.produced,
              CostedEvent.contractum, CostedEvent.fundingAfter,
              FundingSelection.after, LocatedTokenCover.selectedAfter,
              LocatedPurse.configComponents, Multiset.map_add]
            ac_rfl

/-- The atomic located-resource join and the declarative cost step have
exactly the same labelled transition relation. -/
theorem costStep_iff_exists_atomicResourceJoin
    {source : CostConfig Ground} {surface : CostName Ground}
    {spend : CostSig Ground} {target : CostConfig Ground} :
    CostStep source surface spend target ↔
      ∃ event : CostedEvent Ground,
        event.surface = surface ∧ event.spend = spend ∧
          AtomicResourceJoin source event target := by
  constructor
  · exact CostStep.exists_atomicResourceJoin
  · rintro ⟨event, rfl, rfl, join⟩
    exact join.toCostStep

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
