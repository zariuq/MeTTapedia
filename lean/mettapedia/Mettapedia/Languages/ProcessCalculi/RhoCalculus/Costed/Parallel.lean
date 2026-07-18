import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Located
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Valuation
import Mathlib.Tactic

/-!
# Parallel waves for concrete cost-accounted rho

The paper's one-step relation remains the authoritative interleaving semantics.
This module adds a concurrent refinement: a wave is a common multiset
decomposition into funded COMM events plus an untouched frame.  Consequently,
different events in one wave consume disjoint endpoint occurrences and
disjoint purse occurrences even when their syntax or channel names coincide.

Every wave is serializable by ordinary `CostStep`s.  The observable wave
receipt is the occurrence-preserving bag of its event receipts, so permuting a
serialization cannot change the account or deduplicate repeated work.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

open scoped BigOperators

universe u

/-! ## One exact funding selection -/

/-- The purse-head occurrences selected by one firing.  Unselected purses are
not stored here; they belong to the wave frame. -/
structure FundingSelection (Ground : Type u)
    (surface : CostName Ground) (demand : CostSig Ground) where
  chosen : Multiset (SelectedPurseHead Ground)
  demand_eq : demand = (chosen.map SelectedPurseHead.head).sum

namespace FundingSelection

variable {Ground : Type u} {surface : CostName Ground} {demand : CostSig Ground}

/-- Selected purse occurrences before their heads are consumed. -/
def before (selection : FundingSelection Ground surface demand) :
    Multiset (LocatedPurse Ground) :=
  selection.chosen.map fun choice =>
    ⟨surface, .cons choice.head choice.tail⟩

/-- Selected purse occurrences after their tails are exposed. -/
def after (selection : FundingSelection Ground surface demand) :
    Multiset (LocatedPurse Ground) :=
  selection.chosen.map fun choice => ⟨surface, choice.tail⟩

/-- A selection is a located cover with no hidden untouched purse component. -/
def toLocatedCover (selection : FundingSelection Ground surface demand) :
    LocatedTokenCover surface demand selection.before selection.after where
  chosen := selection.chosen
  untouched := 0
  available_eq := by simp [before]
  residual_eq := by simp [after]
  demand_eq := selection.demand_eq

/-- One located receipt contribution for every selected purse occurrence. -/
def contributions (selection : FundingSelection Ground surface demand) :
    Multiset (FundingContribution Ground (CostName Ground)) :=
  selection.chosen.map fun choice =>
    ⟨surface, choice.head, choice.head_valid⟩

/-- A nonzero demand forces an actual selected purse occurrence. -/
theorem chosen_ne_zero (selection : FundingSelection Ground surface demand)
    (demand_valid : demand.RuntimeValid) : selection.chosen ≠ 0 := by
  intro chosen_zero
  apply demand_valid
  rw [selection.demand_eq, chosen_zero]
  simp

/-- The selected heads form one occurrence-preserving event label. -/
def toSpendEvent (selection : FundingSelection Ground surface demand)
    (demand_valid : demand.RuntimeValid) :
    SpendEvent Ground (CostName Ground) where
  funding := selection.contributions
  funding_nonempty := by
    intro empty
    have card_zero : selection.chosen.card = 0 := by
      have mapped_zero := congrArg Multiset.card empty
      simpa [contributions] using mapped_zero
    exact selection.chosen_ne_zero demand_valid (Multiset.card_eq_zero.mp card_zero)

/-- The event label measures exactly the demanded signature. -/
theorem toSpendEvent_rawSpend
    (selection : FundingSelection Ground surface demand)
    (demand_valid : demand.RuntimeValid) :
    (selection.toSpendEvent demand_valid).rawSpend = demand := by
  simp [toSpendEvent, contributions, SpendEvent.rawSpend, selection.demand_eq]

end FundingSelection

/-! ## Concrete funded COMM events -/

/-- A funded COMM event stripped of its untouched context.  These are exactly
the three communication shapes of `CostStep`; each constructor retains the
selected purse-head occurrences separately from its endpoint occurrences. -/
inductive CostedEvent (Ground : Type u) where
  | wholeRecvSend
      (channel : CostName Ground) (body payload : CostTerm Ground)
      (outerSig : CostSig Ground)
      (signature_valid : outerSig.RuntimeValid)
      (funding : FundingSelection Ground channel outerSig)
  | wholeSendRecv
      (channel : CostName Ground) (body payload : CostTerm Ground)
      (outerSig : CostSig Ground)
      (signature_valid : outerSig.RuntimeValid)
      (funding : FundingSelection Ground channel outerSig)
  | split
      (channel : CostName Ground) (body payload : CostTerm Ground)
      (recvSeal sendSeal : CostSig Ground)
      (recv_seal_valid : recvSeal.RuntimeValid)
      (send_seal_valid : sendSeal.RuntimeValid)
      (funding : FundingSelection Ground channel (recvSeal + sendSeal))

namespace CostedEvent

variable {Ground : Type u}

private theorem runtimeValid_add_left {left right : CostSig Ground}
    (left_valid : left.RuntimeValid) : (left + right).RuntimeValid := by
  intro sum_zero
  apply left_valid
  have contained : left ≤ left + right :=
    Multiset.le_iff_exists_add.mpr ⟨right, rfl⟩
  rw [sum_zero] at contained
  exact Multiset.le_zero.mp contained

/-- Interaction surface of an event. -/
def surface : CostedEvent Ground → CostName Ground
  | .wholeRecvSend channel .. => channel
  | .wholeSendRecv channel .. => channel
  | .split channel .. => channel

/-- Exact demanded signature of an event. -/
def spend : CostedEvent Ground → CostSig Ground
  | .wholeRecvSend _ _ _ outerSig .. => outerSig
  | .wholeSendRecv _ _ _ outerSig .. => outerSig
  | .split _ _ _ recvSeal sendSeal .. => recvSeal + sendSeal

/-- Every concrete event has a nonzero demand. -/
theorem spend_valid (event : CostedEvent Ground) : event.spend.RuntimeValid := by
  cases event with
  | wholeRecvSend _ _ _ _ valid _ => exact valid
  | wholeSendRecv _ _ _ _ valid _ => exact valid
  | split _ _ _ _ _ recv_valid _ _ => exact runtimeValid_add_left recv_valid

/-- Endpoint components consumed by the event. -/
def endpoints : CostedEvent Ground → CostConfig Ground
  | .wholeRecvSend channel body payload outerSig _ _ =>
      .signed (.par (.recv channel body) (.send channel payload)) outerSig ::ₘ 0
  | .wholeSendRecv channel body payload outerSig _ _ =>
      .signed (.par (.send channel payload) (.recv channel body)) outerSig ::ₘ 0
  | .split channel body payload recvSeal sendSeal _ _ _ =>
      (.signed (.recv channel body) recvSeal ::ₘ 0) +
        (.signed (.send channel payload) sendSeal ::ₘ 0)

/-- Selected purse components consumed by the event. -/
def fundingBefore : CostedEvent Ground → CostConfig Ground
  | .wholeRecvSend _ _ _ _ _ funding =>
      LocatedPurse.configComponents funding.before
  | .wholeSendRecv _ _ _ _ _ funding =>
      LocatedPurse.configComponents funding.before
  | .split _ _ _ _ _ _ _ funding =>
      LocatedPurse.configComponents funding.before

/-- Contractum components produced by the event. -/
def contractum : CostedEvent Ground → CostConfig Ground
  | .wholeRecvSend _ body payload _ _ _ => (body.commSubst payload).components
  | .wholeSendRecv _ body payload _ _ _ => (body.commSubst payload).components
  | .split _ body payload _ _ _ _ _ => (body.commSubst payload).components

/-- Exposed purse-tail components produced by the event. -/
def fundingAfter : CostedEvent Ground → CostConfig Ground
  | .wholeRecvSend _ _ _ _ _ funding =>
      LocatedPurse.configComponents funding.after
  | .wholeSendRecv _ _ _ _ _ funding =>
      LocatedPurse.configComponents funding.after
  | .split _ _ _ _ _ _ _ funding =>
      LocatedPurse.configComponents funding.after

/-- All source resources owned by this firing occurrence. -/
def consumed (event : CostedEvent Ground) : CostConfig Ground :=
  event.endpoints + event.fundingBefore

/-- All target resources produced by this firing occurrence. -/
def produced (event : CostedEvent Ground) : CostConfig Ground :=
  event.contractum + event.fundingAfter

/-- Canonical occurrence-preserving receipt label of an event. -/
def toSpendEvent : (event : CostedEvent Ground) →
    SpendEvent Ground (CostName Ground)
  | .wholeRecvSend _ _ _ _ valid funding => funding.toSpendEvent valid
  | .wholeSendRecv _ _ _ _ valid funding => funding.toSpendEvent valid
  | .split _ _ _ _ _ recvValid _ funding =>
      funding.toSpendEvent (runtimeValid_add_left recvValid)

/-- Event receipt and event demand agree exactly. -/
theorem toSpendEvent_rawSpend (event : CostedEvent Ground) :
    event.toSpendEvent.rawSpend = event.spend := by
  cases event <;> simp [toSpendEvent, spend, FundingSelection.toSpendEvent_rawSpend]

/-- A local event fires in any disjoint multiset frame using the original
interleaving semantics. -/
def toCostStepIn (event : CostedEvent Ground) (frame : CostConfig Ground) :
    CostStep (frame + event.consumed) event.surface event.spend
      (frame + event.produced) := by
  cases event with
  | wholeRecvSend channel body payload outerSig valid funding =>
      change CostStep
        (frame + ((.signed (.par (.recv channel body) (.send channel payload))
          outerSig ::ₘ 0) + LocatedPurse.configComponents funding.before))
        channel outerSig
        (frame + ((body.commSubst payload).components +
          LocatedPurse.configComponents funding.after))
      simpa only [add_assoc] using
        (CostStep.wholeRecvSend (context := frame) (body := body)
          (payload := payload) valid funding.toLocatedCover)
  | wholeSendRecv channel body payload outerSig valid funding =>
      change CostStep
        (frame + ((.signed (.par (.send channel payload) (.recv channel body))
          outerSig ::ₘ 0) + LocatedPurse.configComponents funding.before))
        channel outerSig
        (frame + ((body.commSubst payload).components +
          LocatedPurse.configComponents funding.after))
      simpa only [add_assoc] using
        (CostStep.wholeSendRecv (context := frame) (body := body)
          (payload := payload) valid funding.toLocatedCover)
  | split channel body payload recvSeal sendSeal recvValid sendValid funding =>
      change CostStep
        (frame + (((.signed (.recv channel body) recvSeal ::ₘ 0) +
          (.signed (.send channel payload) sendSeal ::ₘ 0)) +
          LocatedPurse.configComponents funding.before))
        channel (recvSeal + sendSeal)
        (frame + ((body.commSubst payload).components +
          LocatedPurse.configComponents funding.after))
      simpa only [add_assoc] using
        (CostStep.split (context := frame) (body := body) (payload := payload)
          recvValid sendValid funding.toLocatedCover)

end CostedEvent

/-! ## Interleaving traces and common-source waves -/

/-- A labelled finite trace of ordinary cost steps. -/
inductive CostTrace {Ground : Type u} :
    CostConfig Ground → List (CostName Ground × CostSig Ground) →
      CostConfig Ground → Prop where
  | nil (config : CostConfig Ground) : CostTrace config [] config
  | cons {source middle target surface spend trace}
      (head : CostStep source surface spend middle)
      (tail : CostTrace middle trace target) :
      CostTrace source ((surface, spend) :: trace) target

/-- Source configuration of a wave: every event owns a separate summand. -/
def costWaveSource {Ground : Type u}
    (events : List (CostedEvent Ground)) (frame : CostConfig Ground) :
    CostConfig Ground :=
  (events.map CostedEvent.consumed).sum + frame

/-- Target configuration after every event in a wave has fired. -/
def costWaveTarget {Ground : Type u}
    (events : List (CostedEvent Ground)) (frame : CostConfig Ground) :
    CostConfig Ground :=
  (events.map CostedEvent.produced).sum + frame

/-- Ordered labels of one serialization. -/
def costWaveTrace {Ground : Type u} (events : List (CostedEvent Ground)) :
    List (CostName Ground × CostSig Ground) :=
  events.map fun event => (event.surface, event.spend)

/-- The occurrence bag of event receipts in a wave. -/
def costWaveReceipt {Ground : Type u} (events : List (CostedEvent Ground)) :
    Multiset (SpendEvent Ground (CostName Ground)) :=
  events.map CostedEvent.toSpendEvent

/-- A wave serializes to the paper's ordinary one-step relation. -/
theorem costWave_serializes {Ground : Type u}
    (events : List (CostedEvent Ground)) (frame : CostConfig Ground) :
    CostTrace (costWaveSource events frame) (costWaveTrace events)
      (costWaveTarget events frame) := by
  induction events generalizing frame with
  | nil =>
      simpa [costWaveSource, costWaveTarget, costWaveTrace] using
        (CostTrace.nil frame)
  | cons event rest ih =>
      let nextFrame := frame + event.produced
      have head : CostStep (costWaveSource (event :: rest) frame)
          event.surface event.spend (costWaveSource rest nextFrame) := by
        have eventStep := event.toCostStepIn (costWaveSource rest frame)
        simpa [costWaveSource, nextFrame, add_assoc, add_comm, add_left_comm] using eventStep
      have tail := ih nextFrame
      have tail' : CostTrace (costWaveSource rest nextFrame)
          (costWaveTrace rest) (costWaveTarget (event :: rest) frame) := by
        simpa [costWaveTarget, nextFrame, add_assoc, add_comm, add_left_comm] using tail
      exact CostTrace.cons head tail'

/-- Wave sources depend only on the occurrence multiset, not serialization. -/
theorem costWaveSource_eq_of_perm {Ground : Type u}
    {left right : List (CostedEvent Ground)} (permutation : left.Perm right)
    (frame : CostConfig Ground) :
    costWaveSource left frame = costWaveSource right frame := by
  unfold costWaveSource
  rw [(permutation.map CostedEvent.consumed).sum_eq]

/-- Wave targets depend only on the occurrence multiset, not serialization. -/
theorem costWaveTarget_eq_of_perm {Ground : Type u}
    {left right : List (CostedEvent Ground)} (permutation : left.Perm right)
    (frame : CostConfig Ground) :
    costWaveTarget left frame = costWaveTarget right frame := by
  unfold costWaveTarget
  rw [(permutation.map CostedEvent.produced).sum_eq]

/-- Receipt bags retain occurrences but forget serialization order. -/
theorem costWaveReceipt_eq_of_perm {Ground : Type u}
    {left right : List (CostedEvent Ground)} (permutation : left.Perm right) :
    costWaveReceipt left = costWaveReceipt right := by
  exact Multiset.coe_eq_coe.mpr (permutation.map CostedEvent.toSpendEvent)

/-- Every permutation of a wave is a valid ordinary interleaving between the
same source and target. -/
theorem costWave_permutation_serializes {Ground : Type u}
    {events schedule : List (CostedEvent Ground)}
    (permutation : schedule.Perm events) (frame : CostConfig Ground) :
    CostTrace (costWaveSource events frame) (costWaveTrace schedule)
      (costWaveTarget events frame) := by
  simpa [costWaveSource_eq_of_perm permutation frame,
    costWaveTarget_eq_of_perm permutation frame] using
    costWave_serializes schedule frame

/-! ## Matchings, compatibility, and the costed diamond -/

/-- One fixed matching in a common source configuration.  The source equation
is the occurrence-level separation witness: every endpoint and selected purse
used by an event appears in its own multiset summand. -/
structure CostMatching (Ground : Type u) where
  source : CostConfig Ground
  events : List (CostedEvent Ground)
  frame : CostConfig Ground
  source_eq : source = costWaveSource events frame

namespace CostMatching

variable {Ground : Type u}

/-- Target of a fixed matching. -/
def target (matching : CostMatching Ground) : CostConfig Ground :=
  costWaveTarget matching.events matching.frame

/-- Occurrence bag of the matching's event receipts. -/
def receipt (matching : CostMatching Ground) :
    Multiset (SpendEvent Ground (CostName Ground)) :=
  costWaveReceipt matching.events

/-- A fixed matching is an ordinary interleaving in its listed order. -/
theorem serializes (matching : CostMatching Ground) :
    CostTrace matching.source (costWaveTrace matching.events) matching.target := by
  change CostTrace matching.source (costWaveTrace matching.events)
    (costWaveTarget matching.events matching.frame)
  rw [matching.source_eq]
  exact costWave_serializes matching.events matching.frame

/-- Every permutation of a fixed matching has the same source, target, and
receipt, and is an ordinary interleaving. -/
theorem permutation_serializes (matching : CostMatching Ground)
    {schedule : List (CostedEvent Ground)}
    (permutation : schedule.Perm matching.events) :
    CostTrace matching.source (costWaveTrace schedule) matching.target := by
  change CostTrace matching.source (costWaveTrace schedule)
    (costWaveTarget matching.events matching.frame)
  rw [matching.source_eq]
  exact costWave_permutation_serializes permutation matching.frame

theorem receipt_eq_of_perm (matching : CostMatching Ground)
    {schedule : List (CostedEvent Ground)}
    (permutation : schedule.Perm matching.events) :
    costWaveReceipt schedule = matching.receipt :=
  costWaveReceipt_eq_of_perm permutation

end CostMatching

/-- Nondeterministic concurrent reduction.  A derivation selects one nonempty
matching; alternative matchings remain separate derivations. -/
def ParallelCostStep {Ground : Type u}
    (source : CostConfig Ground)
    (receipt : Multiset (SpendEvent Ground (CostName Ground)))
  (target : CostConfig Ground) : Prop :=
  ∃ matching : CostMatching Ground,
    matching.source = source ∧ matching.events ≠ [] ∧
      matching.receipt = receipt ∧ matching.target = target

/-- Two events are compatible in a source exactly when that source admits a
single decomposition containing both events' endpoint and purse resources. -/
def CostCompatibleAt {Ground : Type u} (source : CostConfig Ground)
    (left right : CostedEvent Ground) : Prop :=
  ∃ frame : CostConfig Ground, source = costWaveSource [left, right] frame

namespace CostCompatibleAt

variable {Ground : Type u} {source : CostConfig Ground}
  {left right : CostedEvent Ground} [DecidableEq Ground]

/-- Compatibility forces enough multiplicity for both consumed occurrences. -/
theorem consumed_count_le (compatible : CostCompatibleAt source left right)
    (resource : CostTerm Ground) :
    left.consumed.count resource + right.consumed.count resource ≤
      source.count resource := by
  obtain ⟨frame, source_eq⟩ := compatible
  rw [source_eq]
  simp only [costWaveSource, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Multiset.count_add]
  omega

end CostCompatibleAt

/-- Intermediate after the left event of a compatible pair fires first. -/
def costAfterLeft {Ground : Type u} (left right : CostedEvent Ground)
    (frame : CostConfig Ground) : CostConfig Ground :=
  left.produced + right.consumed + frame

/-- Intermediate after the right event of a compatible pair fires first. -/
def costAfterRight {Ground : Type u} (left right : CostedEvent Ground)
    (frame : CostConfig Ground) : CostConfig Ground :=
  right.produced + left.consumed + frame

/-- Common target of both serializations of a compatible pair. -/
def costPairTarget {Ground : Type u} (left right : CostedEvent Ground)
    (frame : CostConfig Ground) : CostConfig Ground :=
  left.produced + right.produced + frame

/-- The four ordinary steps witnessing the costed diamond. -/
def CostedDiamond {Ground : Type u} (source : CostConfig Ground)
    (left right : CostedEvent Ground) : Prop :=
  ∃ frame : CostConfig Ground,
    source = costWaveSource [left, right] frame ∧
    CostStep source left.surface left.spend
      (costAfterLeft left right frame) ∧
    CostStep (costAfterLeft left right frame) right.surface right.spend
      (costPairTarget left right frame) ∧
    CostStep source right.surface right.spend
      (costAfterRight left right frame) ∧
    CostStep (costAfterRight left right frame) left.surface left.spend
      (costPairTarget left right frame)

/-- Compatible funded events commute to one exact multiset target; the result
is equality, not merely a schedule-chosen normal form. -/
theorem compatible_costed_diamond {Ground : Type u}
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (compatible : CostCompatibleAt source left right) :
    CostedDiamond source left right := by
  obtain ⟨frame, source_eq⟩ := compatible
  refine ⟨frame, source_eq, ?_, ?_, ?_, ?_⟩
  · have step := left.toCostStepIn (right.consumed + frame)
    rw [source_eq]
    simpa [costWaveSource, costAfterLeft, add_assoc, add_comm, add_left_comm] using step
  · have step := right.toCostStepIn (left.produced + frame)
    simpa [costAfterLeft, costPairTarget, add_assoc, add_comm, add_left_comm] using step
  · have step := right.toCostStepIn (left.consumed + frame)
    rw [source_eq]
    simpa [costWaveSource, costAfterRight, add_assoc, add_comm, add_left_comm] using step
  · have step := left.toCostStepIn (right.produced + frame)
    simpa [costAfterRight, costPairTarget, add_assoc, add_comm, add_left_comm] using step

/-- A source containing only one occurrence of a purse term cannot support two
events that both select that occurrence in the same matching. -/
theorem shared_single_purse_conflicts {Ground : Type u}
    [DecidableEq Ground]
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (purse : CostTerm Ground)
    (source_count : source.count purse = 1)
    (left_uses : purse ∈ left.fundingBefore)
    (right_uses : purse ∈ right.fundingBefore) :
    ¬CostCompatibleAt source left right := by
  intro compatible
  have left_positive : 0 < left.consumed.count purse := by
    have funding_positive := Multiset.count_pos.mpr left_uses
    simp only [CostedEvent.consumed, Multiset.count_add]
    omega
  have right_positive : 0 < right.consumed.count purse := by
    have funding_positive := Multiset.count_pos.mpr right_uses
    simp only [CostedEvent.consumed, Multiset.count_add]
    omega
  have enough := compatible.consumed_count_le purse
  rw [source_count] at enough
  omega

/-! ## The causal receipt of one wave -/

/-- Events of one compatible wave have no causes among themselves.  Causes
from the pre-wave history remain outside this fragment and are attached when
the runtime composes the wave with its existing receipt prefix. -/
def costWaveCausalReceipt {Ground : Type u}
    (events : List (CostedEvent Ground)) :
    CausalReceipt (Fin events.length) Ground (CostName Ground) where
  label index := (events.get index).toSpendEvent
  arcMultiplicity _ _ := 0
  rank _ := 0
  arc_rank_lt _ _ positive := by simp at positive

/-- Causal reachability inside a wave fragment is exactly equality. -/
theorem costWaveCausalReceipt_causalLE_iff {Ground : Type u}
    (events : List (CostedEvent Ground)) (left right : Fin events.length) :
    (costWaveCausalReceipt events).CausalLE left right ↔ left = right := by
  constructor
  · intro path
    rcases (costWaveCausalReceipt events).causalLE_eq_or_rank_lt path with equal | strict
    · exact equal
    · simp [costWaveCausalReceipt] at strict
  · rintro rfl
    exact (costWaveCausalReceipt events).causalLE_refl left

/-- Distinct events in one wave are causally independent. -/
theorem costWaveCausalReceipt_independent_iff {Ground : Type u}
    (events : List (CostedEvent Ground)) (left right : Fin events.length) :
    (costWaveCausalReceipt events).Independent left right ↔ left ≠ right := by
  simp only [CausalReceipt.Independent,
    costWaveCausalReceipt_causalLE_iff]
  constructor
  · rintro ⟨different, _⟩
    exact different
  · intro different
    exact ⟨different, fun reverse => different reverse.symm⟩

private theorem costWave_fin_sum_get_eq_sum_map
    {Alpha : Type*} {M : Type*} [AddCommMonoid M]
    (items : List Alpha) (value : Alpha → M) :
    (∑ index : Fin items.length, value (items.get index)) =
      (items.map value).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [Fin.sum_univ_succ]
      change value head + (∑ index : Fin tail.length, value (tail.get index)) =
        value head + (tail.map value).sum
      rw [ih]

/-- The causal pomset's measure is the bag-sum of the individual event
demands. -/
theorem costWaveCausalReceipt_totalRawMeasure {Ground : Type u}
    (events : List (CostedEvent Ground)) :
    (costWaveCausalReceipt events).totalRawMeasure =
      (events.map CostedEvent.spend).sum := by
  change (∑ index : Fin events.length,
    (events.get index).toSpendEvent.rawSpend) =
      (events.map CostedEvent.spend).sum
  calc
    (∑ index : Fin events.length,
        (events.get index).toSpendEvent.rawSpend) =
        (events.map fun event => event.toSpendEvent.rawSpend).sum :=
      costWave_fin_sum_get_eq_sum_map events
        (fun event => event.toSpendEvent.rawSpend)
    _ = (events.map CostedEvent.spend).sum := by
      simp only [CostedEvent.toSpendEvent_rawSpend]

/-- The causal measure is exactly the sum over the occurrence bag returned as
the wave receipt. -/
theorem costWaveCausalReceipt_eq_receipt_bag_sum {Ground : Type u}
    (events : List (CostedEvent Ground)) :
    (costWaveCausalReceipt events).totalRawMeasure =
      ((costWaveReceipt events).map SpendEvent.rawSpend).sum := by
  rw [costWaveCausalReceipt_totalRawMeasure]
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp [costWaveReceipt, CostedEvent.toSpendEvent_rawSpend, ih]

/-- Isomorphism of finite causal receipts preserves event labels, direct-arc
multiplicities, and the acyclicity rank. -/
structure CausalReceiptIso
    {LeftEvent RightEvent : Type*} [Fintype LeftEvent] [Fintype RightEvent]
    {Ground : Type u} {Surface : Type*}
    (left : CausalReceipt LeftEvent Ground Surface)
    (right : CausalReceipt RightEvent Ground Surface) where
  events : LeftEvent ≃ RightEvent
  label_eq : ∀ event, left.label event = right.label (events event)
  arcMultiplicity_eq : ∀ cause effect,
    left.arcMultiplicity cause effect =
      right.arcMultiplicity (events cause) (events effect)
  rank_eq : ∀ event, left.rank event = right.rank (events event)

/-- A list permutation canonically matches the nth occurrence of each value,
including repeated equal values. -/
def permFinEquiv {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    {left right : List Alpha} (permutation : left.Perm right) :
    Fin left.length ≃ Fin right.length where
  toFun := permutation.idxBij
  invFun := permutation.symm.idxBij
  left_inv _ := permutation.idxBij_symm_idxBij
  right_inv _ := permutation.idxBij_idxBij_symm

/-- Permuting a serialization only relabels the discrete wave pomset.  This is
stronger than equality of total cost and does not identify duplicate labels. -/
noncomputable def costWaveCausalReceipt_iso_of_perm {Ground : Type u}
    {schedule events : List (CostedEvent Ground)}
    (permutation : schedule.Perm events) :
    CausalReceiptIso (costWaveCausalReceipt schedule)
      (costWaveCausalReceipt events) := by
  classical
  let ids := permFinEquiv permutation
  refine
    { events := ids
      label_eq := ?_
      arcMultiplicity_eq := ?_
      rank_eq := ?_ }
  · intro index
    change (schedule.get index).toSpendEvent =
      (events.get (ids index)).toSpendEvent
    exact congrArg CostedEvent.toSpendEvent
      (permutation.getElem_idxBij_eq_getElem index).symm
  · intro _ _
    rfl
  · intro _
    rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
