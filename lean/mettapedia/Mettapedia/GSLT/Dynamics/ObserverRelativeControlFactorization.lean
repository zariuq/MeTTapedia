import Mettapedia.GSLT.Core.OpenTotalityObservation
import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.GSLT.Core.ControlInfluenceSeparation
import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
import Mettapedia.GSLT.Dynamics.ScheduleObservationFactorization

/-!
# Observer-relative control over capability-indexed executions

This module assembles existing execution, observation, scheduling, activation,
pruning, and completion interfaces without replacing any of them.

The factorization is:

```text
proof-relevant execution
  -> exact event history
  -> retained witness container S
  -> declared semantic value V
  -> optional scheduling readout Q

observer + completion demand
  -> admitted control transformations
  -> transient active/deferred partition
  -> observer-preserving, occurrence-accounted pruning
  -> open, closed, exhausted, cancelled, or faulted observation
```

An occurrence index is kept separate from event payload, semantic value, and
scheduler score.  It can be added to a client observer as either an ordered
stream or a multiplicity-sensitive bag.  An injective stream index forbids
every event-list change.  An injective bag index permits reordering but
forbids occurrence loss and duplicate collapse.

Selecting active work is not pruning: every unselected occurrence remains in
the deferred partition.  Permanent removal additionally requires an
observer-relative preservation proof and an exact removed-occurrence ledger.
The composite conservation theorem proves that activation followed by
admitted pruning never silently destroys occurrence mass.

Finally, budget exhaustion remains distinct from closed absence.  An
exhausted computation may export a resumable residual only through explicit
capture admission, but exhaustion alone never establishes refutation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Core.ControlInfluenceSeparation
open Mettapedia.GSLT.Core.OpenTotalityObservation

universe uState uExecution uIdentity uGuard uView uScore uOtherView uOtherScore
universe uReceipt uActivationReceipt

/-! ## Occurrence identity is an independent axis -/

/-- A declared occurrence identity for proof-relevant events.  No
injectivity is assumed: a client may intentionally observe a coarser identity
such as an answer, constructor, or provenance class. -/
structure OccurrenceIndex (Event : Type*) (Identity : Type uIdentity) where
  identify : Event → Identity

namespace OccurrenceIndex

variable {Event : Type*} {Identity : Type uIdentity}

/-- Reindex occurrence identity along an event translation.  This changes
only how source events are named; it does not assert that the translation
retains distinct source occurrences. -/
def pullback {SourceEvent : Type*}
    (eventMap : SourceEvent → Event)
    (index : OccurrenceIndex Event Identity) :
    OccurrenceIndex SourceEvent Identity where
  identify := index.identify ∘ eventMap

@[simp] theorem pullback_identify {SourceEvent : Type*}
    (eventMap : SourceEvent → Event)
    (index : OccurrenceIndex Event Identity) (event : SourceEvent) :
    (index.pullback eventMap).identify event = index.identify (eventMap event) :=
  rfl

/-- The occurrence index retains every event distinction. -/
def Exact (index : OccurrenceIndex Event Identity) : Prop :=
  Function.Injective index.identify

/-- Pullback retains exact occurrence identity precisely when the event map
is injective, provided the target occurrence index was already exact.  Thus a
many-to-one translation cannot inherit exactness by declaration. -/
theorem pullback_exact_iff {SourceEvent : Type*}
    (eventMap : SourceEvent → Event)
    (index : OccurrenceIndex Event Identity) (exact : index.Exact) :
    (index.pullback eventMap).Exact ↔ Function.Injective eventMap := by
  constructor
  · intro pulledBackExact first second mappedEqual
    apply pulledBackExact
    exact congrArg index.identify mappedEqual
  · intro mapExact first second identifiedEqual
    apply mapExact
    exact exact identifiedEqual

/-- Ordered occurrence observation retains order, multiplicity, and the
declared identity coordinate. -/
def streamObserver (index : OccurrenceIndex Event Identity) :
    Observer (List Event) (List Identity) where
  observe := List.map index.identify

/-- Bag occurrence observation forgets order but retains multiplicity and
the declared identity coordinate. -/
def bagObserver (index : OccurrenceIndex Event Identity) :
    Observer (List Event) (Multiset Identity) where
  observe := fun events => Multiset.map index.identify (events : Multiset Event)

@[simp] theorem streamObserver_observe
    (index : OccurrenceIndex Event Identity) (events : List Event) :
    index.streamObserver.observe events = events.map index.identify :=
  rfl

@[simp] theorem bagObserver_observe
    (index : OccurrenceIndex Event Identity) (events : List Event) :
    index.bagObserver.observe events =
      Multiset.map index.identify (events : Multiset Event) :=
  rfl

/-- An exact ordered occurrence observation reflects the complete event
list. -/
theorem source_eq_target_of_stream_lawful
    (index : OccurrenceIndex Event Identity) (exact : index.Exact)
    {Receipt : Type uReceipt} {change : Change Event Receipt}
    (lawful : LawfulAt index.streamObserver change) :
    change.source = change.target := by
  exact (List.map_injective_iff.mpr exact) lawful

/-- An exact occurrence-bag observation reflects event multiplicity while
deliberately allowing permutations. -/
theorem source_bag_eq_target_bag_of_bag_lawful
    (index : OccurrenceIndex Event Identity) (exact : index.Exact)
    {Receipt : Type uReceipt} {change : Change Event Receipt}
    (lawful : LawfulAt index.bagObserver change) :
    (change.source : Multiset Event) = (change.target : Multiset Event) := by
  apply Multiset.map_injective exact
  exact lawful

end OccurrenceIndex

namespace OccurrenceIndexCanary

def exactUnit : OccurrenceIndex Unit Unit where
  identify := id

theorem exactUnit_exact : exactUnit.Exact :=
  Function.injective_id

def collapseBool (_ : Bool) : Unit := ()

/-- An exact target index cannot hide a many-to-one event translation. -/
theorem collapseBool_pullback_not_exact :
    ¬ (exactUnit.pullback collapseBool).Exact := by
  rw [exactUnit.pullback_exact_iff collapseBool exactUnit_exact]
  intro injective
  have equal : false = true := injective rfl
  exact Bool.noConfusion equal

/-- Reindexing along identity retains exact occurrence identity. -/
theorem identity_pullback_exact :
    (exactUnit.pullback id).Exact :=
  (exactUnit.pullback_exact_iff id exactUnit_exact).2 Function.injective_id

end OccurrenceIndexCanary

/-! ## The assembly of existing semantic layers -/

/-- The minimal control assembly over an existing capability-indexed
observation architecture.  It adds no execution step and chooses no
controller.  It only names the occurrence identity, client contract, and
policy-facing scheduling readout used at this boundary. -/
structure ObserverRelativeControlFactorization
    {State : Type uState} {Execution : State → State → Type uExecution}
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (Identity : Type uIdentity) (Guard : Type uGuard)
    (View : Type uView) (Score : Type uScore) where
  occurrence : OccurrenceIndex architecture.Event Identity
  contract : Contract architecture.Event Guard View
  schedule : architecture.SchedulerReadout Score

namespace ObserverRelativeControlFactorization

variable {State : Type uState} {Execution : State → State → Type uExecution}
variable {architecture :
  CapabilityIndexedObservationArchitecture State Execution}
variable {Identity : Type uIdentity} {Guard : Type uGuard}
variable {View : Type uView} {Score : Type uScore}
variable {OtherView : Type uOtherView} {OtherScore : Type uOtherScore}

/-- Event type supplied by the upstream proof-relevant architecture. -/
abbrev ExecutionEvent
    (_control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :=
  architecture.Event

/-- Witness container supplied by the observation discipline. -/
abbrev Container
    (_control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :=
  architecture.Container

/-- Semantic value supplied by the observation discipline. -/
abbrev Value
    (_control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :=
  architecture.Value

/-- Add ordered occurrence identity to the client observation.  Scheduling
readout and completion demand remain unchanged. -/
def withOccurrenceStream
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :
    ObserverRelativeControlFactorization architecture Identity Guard
      (View × List Identity) Score where
  occurrence := control.occurrence
  contract := control.contract.addAxis control.occurrence.streamObserver
  schedule := control.schedule

/-- Add multiplicity-sensitive occurrence identity while permitting
reordering. -/
def withOccurrenceBag
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :
    ObserverRelativeControlFactorization architecture Identity Guard
      (View × Multiset Identity) Score where
  occurrence := control.occurrence
  contract := control.contract.addAxis control.occurrence.bagObserver
  schedule := control.schedule

/-- Deliberately forget client observation detail.  This can grant more
control transformations, but it neither changes execution nor alters the
scheduler readout. -/
def postcompose
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (summarize : View → OtherView) :
    ObserverRelativeControlFactorization architecture Identity Guard
      OtherView Score where
  occurrence := control.occurrence
  contract := control.contract.postcompose summarize
  schedule := control.schedule

/-- Change only the scheduling readout.  No semantic value, witness
container, observer, occurrence identity, or completion demand changes. -/
def mapSchedule
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (summarize : Score → OtherScore) :
    ObserverRelativeControlFactorization architecture Identity Guard
      View OtherScore where
  occurrence := control.occurrence
  contract := control.contract
  schedule := { readout := summarize ∘ control.schedule.readout }

@[simp] theorem withOccurrenceStream_demand
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :
    control.withOccurrenceStream.contract.demand = control.contract.demand :=
  rfl

@[simp] theorem withOccurrenceBag_demand
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score) :
    control.withOccurrenceBag.contract.demand = control.contract.demand :=
  rfl

@[simp] theorem postcompose_demand
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (summarize : View → OtherView) :
    (control.postcompose summarize).contract.demand = control.contract.demand :=
  rfl

@[simp] theorem mapSchedule_contract
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (summarize : Score → OtherScore) :
    (control.mapSchedule summarize).contract = control.contract :=
  rfl

/-! ## Every permanent change consumes observer-relative authority -/

/-- A concrete event-list change paired with its proof of invisibility to
the declared client observer. -/
abbrev AdmittedChange
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (Receipt : Type uReceipt) :=
  { change : Change control.ExecutionEvent Receipt //
      control.contract.Preserves change }

/-- Apply an admitted change. -/
def AdmittedChange.result
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score} {Receipt : Type uReceipt}
    (change : control.AdmittedChange Receipt) : List control.ExecutionEvent :=
  change.1.target

/-- Applying an admitted change preserves exactly the declared observation. -/
theorem AdmittedChange.observation_eq
    {control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score} {Receipt : Type uReceipt}
    (change : control.AdmittedChange Receipt) :
    control.contract.observer.observe change.result =
      control.contract.observer.observe change.1.source :=
  change.2.symm

/-- A permanent prune has both observer-relative authority and an exact
removed-occurrence accounting ledger. -/
abbrev AdmittedPruning
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (Receipt : Type uReceipt) :=
  { pruning : PruningChange control.ExecutionEvent Receipt //
      control.contract.Preserves pruning.toChange }

/-- Exact ordered occurrence observation admits only the identity event-list
change. -/
theorem source_eq_target_of_exact_occurrence_stream
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (exact : control.occurrence.Exact)
    {Receipt : Type uReceipt}
    (change : control.withOccurrenceStream.AdmittedChange Receipt) :
    change.1.source = change.1.target := by
  have occurrenceLawful :=
    (control.contract.preserves_addAxis_iff
      control.occurrence.streamObserver change.1).1 change.2
  exact control.occurrence.source_eq_target_of_stream_lawful exact
    occurrenceLawful.2

/-- Exact occurrence-bag observation allows permutations but reflects the
complete multiplicity-sensitive event bag. -/
theorem source_bag_eq_target_bag_of_exact_occurrence_bag
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (exact : control.occurrence.Exact)
    {Receipt : Type uReceipt}
    (change : control.withOccurrenceBag.AdmittedChange Receipt) :
    (change.1.source : Multiset control.ExecutionEvent) =
      (change.1.target : Multiset control.ExecutionEvent) := by
  have occurrenceLawful :=
    (control.contract.preserves_addAxis_iff
      control.occurrence.bagObserver change.1).1 change.2
  exact control.occurrence.source_bag_eq_target_bag_of_bag_lawful exact
    occurrenceLawful.2

/-- An admitted pruning at an exact occurrence-bag observer removes no
occurrence.  Reordering remains possible because only the bags are equated. -/
theorem removed_eq_zero_of_exact_occurrence_bag
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    (exact : control.occurrence.Exact)
    {Receipt : Type uReceipt}
    (pruning : control.withOccurrenceBag.AdmittedPruning Receipt) :
    pruning.1.removed = 0 := by
  have bagsEqual :
      (pruning.1.source : Multiset control.ExecutionEvent) =
        (pruning.1.target : Multiset control.ExecutionEvent) :=
    control.source_bag_eq_target_bag_of_exact_occurrence_bag exact
      ⟨pruning.1.toChange, pruning.2⟩
  have accounting := pruning.1.accounting
  rw [bagsEqual] at accounting
  have zeroEq : (0 : Multiset control.ExecutionEvent) = pruning.1.removed := by
    have cancel :
        (pruning.1.target : Multiset control.ExecutionEvent) + 0 =
          (pruning.1.target : Multiset control.ExecutionEvent) +
            pruning.1.removed := by
      simpa using accounting
    exact add_left_cancel cancel
  exact zeroEq.symm

/-! ## Selection defers; only admitted pruning removes -/

/-- Transient activation followed by an admitted prune of deferred work
preserves the client observation at the prune boundary and conserves every
exact event occurrence across active, retained, and receipted-removed
classes. -/
theorem defer_then_prune_conserves
    (control : ObserverRelativeControlFactorization architecture Identity
      Guard View Score)
    {ActivationReceipt : Type uActivationReceipt}
    (activation : ActivationPartition control.ExecutionEvent ActivationReceipt)
    {Receipt : Type uReceipt}
    (pruning : control.AdmittedPruning Receipt)
    (prunesDeferred : pruning.1.source = activation.deferred) :
    control.contract.observer.observe pruning.1.source =
        control.contract.observer.observe pruning.1.target ∧
      ((activation.active ++ pruning.1.target : List control.ExecutionEvent) :
          Multiset control.ExecutionEvent) + pruning.1.removed =
        (activation.source : Multiset control.ExecutionEvent) := by
  constructor
  · exact pruning.2
  · have deferredAccounting :
        (activation.deferred : Multiset control.ExecutionEvent) =
          (pruning.1.target : Multiset control.ExecutionEvent) + pruning.1.removed := by
      rw [← prunesDeferred]
      exact pruning.1.accounting
    calc
      ((activation.active ++ pruning.1.target : List control.ExecutionEvent) :
          Multiset control.ExecutionEvent) + pruning.1.removed =
          (activation.active : Multiset control.ExecutionEvent) +
            (pruning.1.target : Multiset control.ExecutionEvent) +
              pruning.1.removed := by simp
      _ = (activation.active : Multiset control.ExecutionEvent) +
            ((pruning.1.target : Multiset control.ExecutionEvent) +
              pruning.1.removed) := by ac_rfl
      _ = (activation.active : Multiset control.ExecutionEvent) +
            (activation.deferred : Multiset control.ExecutionEvent) := by
              rw [deferredAccounting]
      _ = ((activation.active ++ activation.deferred : List control.ExecutionEvent) :
            Multiset control.ExecutionEvent) := by simp
      _ = (activation.source : Multiset control.ExecutionEvent) :=
        activation.recombinedBag

/-! ## Exhaustion is not refutation -/

/-- An exhausted observation with an admitted captured residual remains
resumable at exactly the captured revision. -/
@[simp] theorem exhaustedCaptured_resume?
    {Occurrence Residual Revision Coverage Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual → Revision → Prop}
    (occurrences : List Occurrence) (bound : Bound) (receipt : Receipt)
    (residual : Residual) (revision : Revision)
    (admitted : CaptureAdmitted residual revision) :
    (Observation.exhaustedCaptured (Coverage := Coverage) (Fault := Fault)
      occurrences bound receipt residual revision admitted).resume? =
        some (residual, revision) :=
  rfl

/-- Empty output plus budget exhaustion still cannot authorize a closed
absence conclusion. -/
theorem exhausted_empty_not_closed_absence
    {Occurrence Residual Revision Coverage Bound Receipt Fault : Type*}
    {CaptureAdmitted : Residual → Revision → Prop}
    (bound : Bound) (receipt : Receipt) :
    ¬ Observation.EstablishesClosedAbsence
      (Observation.withoutCapture (Residual := Residual)
        (Revision := Revision) (Coverage := Coverage) (Fault := Fault)
        (CaptureAdmitted := CaptureAdmitted) ([] : List Occurrence)
        (.exhausted bound receipt)) :=
  Observation.exhausted_not_establishesClosedAbsence [] bound receipt

end ObserverRelativeControlFactorization

/-! ## Separating canaries -/

namespace ObserverRelativeControlFactorizationCanary

open CapabilityIndexedObservationArchitecture
open CapabilityIndexedObservationCanary
open ObserverRelativeControlFactorization

abbrev CanaryEvent := Mettapedia.GSLT.Dynamics.Canary.Event

def identityIndex : OccurrenceIndex CanaryEvent CanaryEvent where
  identify := id

theorem identityIndex_exact : identityIndex.Exact :=
  Function.injective_id

def eventBagContract : Contract CanaryEvent Unit (Multiset CanaryEvent) where
  observer := { observe := fun events => (events : Multiset CanaryEvent) }
  demand := { completion := .completeBag }

def control : ObserverRelativeControlFactorization provenanceArchitecture
    CanaryEvent Unit (Multiset CanaryEvent) Nat where
  occurrence := identityIndex
  contract := eventBagContract
  schedule := lengthScheduler

def reverseChange : Change CanaryEvent Unit where
  source := [.left, .right]
  target := [.right, .left]
  receipt := ()

def dropLeft : PruningChange CanaryEvent Unit where
  source := [.left]
  target := []
  receipt := ()
  removed := {.left}
  accounting := by simp

private theorem reverse_event_bag_eq :
    (([Canary.Event.left, Canary.Event.right] : List CanaryEvent) :
        Multiset CanaryEvent) =
      (([Canary.Event.right, Canary.Event.left] : List CanaryEvent) :
        Multiset CanaryEvent) :=
  Quot.sound (by decide)

/-- Bag semantics admits permutation at the base observer. -/
theorem reverse_admitted_at_event_bag :
    control.contract.Preserves reverseChange := by
  simpa [control, eventBagContract, Contract.Preserves, LawfulAt,
    reverseChange] using reverse_event_bag_eq

/-- Adding ordered occurrence identity rejects the same permutation. -/
theorem reverse_refused_at_occurrence_stream :
    ¬ control.withOccurrenceStream.contract.Preserves reverseChange := by
  intro preserves
  have unchanged := control.source_eq_target_of_exact_occurrence_stream
    identityIndex_exact ⟨reverseChange, preserves⟩
  have heads : Canary.Event.left = Canary.Event.right :=
    (List.cons.inj unchanged).1
  exact (by decide : Canary.Event.left ≠ Canary.Event.right) heads

/-- Adding multiplicity-sensitive occurrence identity still permits the
permutation. -/
theorem reverse_admitted_at_occurrence_bag :
    control.withOccurrenceBag.contract.Preserves reverseChange := by
  exact
    (control.contract.preserves_addAxis_iff
      identityIndex.bagObserver reverseChange).2
      ⟨reverse_admitted_at_event_bag, by
        simpa [LawfulAt, OccurrenceIndex.bagObserver, identityIndex,
          reverseChange] using reverse_event_bag_eq⟩

/-- Exact occurrence-bag observation refuses permanent loss. -/
theorem drop_refused_at_occurrence_bag :
    ¬ control.withOccurrenceBag.contract.Preserves dropLeft.toChange := by
  intro preserves
  have noRemoval := control.removed_eq_zero_of_exact_occurrence_bag
    identityIndex_exact ⟨dropLeft, preserves⟩
  have nonempty : ({Canary.Event.left} : Multiset CanaryEvent) ≠ 0 := by
    simp
  exact nonempty noRemoval

def deferredLeft : ActivationPartition CanaryEvent Unit where
  source := [.left, .right]
  active := [.right]
  deferred := [.left]
  receipt := ()
  complete := by decide

/-- Choosing one active occurrence does not destroy the other: it remains in
the deferred partition. -/
theorem transient_selection_retains_both :
    ((deferredLeft.active ++ deferredLeft.deferred : List CanaryEvent) :
      Multiset CanaryEvent) = (deferredLeft.source : Multiset CanaryEvent) :=
  deferredLeft.recombinedBag

/-- The lossy length scheduler remains accepted for length-sensitive control
and refused for order-sensitive control on the same architecture. -/
theorem scheduling_authority_is_readout_relative :
    control.schedule.SupportsPolicy List.length ∧
      ¬ control.schedule.SupportsPolicy beginsLeft :=
  ⟨lengthScheduler_supports_lengthPolicy,
    lengthScheduler_not_supports_beginsLeft⟩

end ObserverRelativeControlFactorizationCanary

#print axioms OccurrenceIndex.source_eq_target_of_stream_lawful
#print axioms OccurrenceIndex.source_bag_eq_target_bag_of_bag_lawful
#print axioms OccurrenceIndexCanary.collapseBool_pullback_not_exact
#print axioms OccurrenceIndexCanary.identity_pullback_exact
#print axioms ObserverRelativeControlFactorization.removed_eq_zero_of_exact_occurrence_bag
#print axioms ObserverRelativeControlFactorization.defer_then_prune_conserves
#print axioms ObserverRelativeControlFactorization.exhaustedCaptured_resume?
#print axioms ObserverRelativeControlFactorization.exhausted_empty_not_closed_absence
#print axioms ObserverRelativeControlFactorizationCanary.reverse_refused_at_occurrence_stream
#print axioms ObserverRelativeControlFactorizationCanary.drop_refused_at_occurrence_bag
#print axioms ObserverRelativeControlFactorizationCanary.transient_selection_retains_both
#print axioms ObserverRelativeControlFactorizationCanary.scheduling_authority_is_readout_relative

end Mettapedia.GSLT.Dynamics
