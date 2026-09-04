import Mettapedia.GSLT.Core.ObservationIndexedPruning
import Mettapedia.GSLT.Dynamics.ObservationDiscipline
import Mettapedia.GSLT.Dynamics.PartialObservationProduct

/-!
# Products of partial witness collections

Witness collection has two lawful product readings.

* `WitnessCollector.prod` is synchronized: it returns a pair only when both
  collectors accept the same history.
* `independentProduct` is total at the outer collection layer and retains the
  two optional component results inside its witness container.

The synchronized and independent observations coincide exactly on histories
where both components are defined together.  The same criterion controls
whether an observer-indexed optimization guard can be transported between
the two readings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WitnessCollectionProduct

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Dynamics.PartialObservationProduct

universe uEvent uLeftContainer uRightContainer uLeftValue uRightValue uReceipt

namespace WitnessCollector

/-- The pointwise product that retains each collector result independently. -/
def independentResult {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event)
    (events : List Event) :
    Option left.Container × Option right.Container :=
  (left.collect events, right.collect events)

/-- The existing collector product viewed as one synchronized partial result. -/
def synchronizedResult {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event)
    (events : List Event) : Option (left.Container × right.Container) :=
  (left.prod right).collect events

@[simp] theorem synchronizedResult_eq_synchronize
    {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event)
    (events : List Event) :
    synchronizedResult left right events =
      synchronize (independentResult left right events) :=
  rfl

/-- Both collectors accept exactly the same histories. -/
def FailureAligned {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event) : Prop :=
  ∀ events, DefinedTogether (left.collect events) (right.collect events)

/-- Splitting synchronized collection recovers both independent component
results on every history. -/
def PreservesIndependentResult {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event) : Prop :=
  ∀ events,
    split (synchronizedResult left right events) =
      independentResult left right events

theorem preservesIndependentResult_iff_failureAligned
    {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event) :
    PreservesIndependentResult left right ↔ FailureAligned left right := by
  constructor
  · intro preserves events
    have comparison := preserves events
    rw [synchronizedResult_eq_synchronize] at comparison
    exact (split_synchronize_eq_iff_definedTogether
      (left.collect events) (right.collect events)).1
        (by simpa [independentResult] using comparison)
  · intro aligned events
    exact (split_synchronize_eq_iff_definedTogether
      (left.collect events) (right.collect events)).2 (aligned events)

/-- A genuine independent-failure witness collector.  The outer collection
always succeeds; each component's success or failure remains explicit inside
the retained container. -/
def independentProduct {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event) :
    WitnessCollector Event where
  Container := Option left.Container × Option right.Container
  collect := fun events => some (independentResult left right events)

@[simp] theorem independentProduct_collect
    {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event)
    (events : List Event) :
    (independentProduct left right).collect events =
      some (left.collect events, right.collect events) :=
  rfl

theorem independentProduct_total {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event) :
    (independentProduct left right).Total := by
  intro events
  exact ⟨independentResult left right events, rfl⟩

/-- Synchronization is an explicit partial channel out of the independent
container.  It is always sound in this information-losing direction. -/
theorem synchronized_collect_channel {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uLeftContainer} Event)
    (right : WitnessCollector.{uEvent, uRightContainer} Event)
    (events : List Event) :
    ((independentProduct left right).collect events).bind synchronize =
      (left.prod right).collect events :=
  rfl

end WitnessCollector

namespace ObservationDiscipline

/-- Both optional value observations retained pointwise. -/
def independentResult {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event)
    (events : List Event) : Option left.Value × Option right.Value :=
  (left.observe events, right.observe events)

/-- Split the joint failure of the existing synchronized discipline product. -/
def synchronizedSplitResult {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event)
    (events : List Event) : Option left.Value × Option right.Value :=
  split ((left.prod right).observe events)

/-- Both disciplines produce a value on exactly the same histories. -/
def FailureAligned {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    Prop :=
  ∀ events, DefinedTogether (left.observe events) (right.observe events)

/-- The exact pointwise comparison between synchronized and independent value
observations. -/
def PreservesIndependentResult {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    Prop :=
  ∀ events,
    synchronizedSplitResult left right events =
      independentResult left right events

theorem preservesIndependentResult_iff_failureAligned
    {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    PreservesIndependentResult left right ↔ FailureAligned left right := by
  constructor
  · intro preserves events
    have comparison := preserves events
    unfold synchronizedSplitResult independentResult at comparison
    rw [ObservationDiscipline.prod_observe] at comparison
    exact (split_synchronize_eq_iff_definedTogether
      (left.observe events) (right.observe events)).1 comparison
  · intro aligned events
    unfold synchronizedSplitResult independentResult
    rw [ObservationDiscipline.prod_observe]
    exact (split_synchronize_eq_iff_definedTogether
      (left.observe events) (right.observe events)).2 (aligned events)

/-- A discipline whose outer collection never discards unilateral failure.
Its value retains each optional component observation independently. -/
def independentProduct {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    ObservationDiscipline Event where
  collection := WitnessCollector.independentProduct
    left.collection right.collection
  Value := Option left.Value × Option right.Value
  readout := fun containers =>
    (containers.1.map left.readout, containers.2.map right.readout)

@[simp] theorem independentProduct_observe
    {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event)
    (events : List Event) :
    (independentProduct left right).observe events =
      some (left.observe events, right.observe events) :=
  rfl

/-- The synchronized discipline is obtained by the same explicit partial
channel from the independent optional-value pair. -/
theorem synchronized_observe_channel
    {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event)
    (events : List Event) :
    ((independentProduct left right).observe events).bind synchronize =
      (left.prod right).observe events := by
  rw [independentProduct_observe, ObservationDiscipline.prod_observe]
  rfl

/-- The observer that exposes independent optional values directly. -/
def independentObserver {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    Observer (List Event) (Option left.Value × Option right.Value) where
  observe := independentResult left right

/-- The observer that first uses synchronized collection and then attempts to
split the joint optional result. -/
def synchronizedSplitObserver {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    Observer (List Event) (Option left.Value × Option right.Value) where
  observe := synchronizedSplitResult left right

theorem synchronizedSplitObserver_eq_iff_failureAligned
    {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event) :
    synchronizedSplitObserver left right = independentObserver left right ↔
      FailureAligned left right := by
  rw [← preservesIndependentResult_iff_failureAligned]
  constructor
  · intro equal events
    exact congrArg (fun observer => observer.observe events) equal
  · intro preserves
    cases left
    cases right
    simp only [synchronizedSplitObserver, independentObserver]
    congr
    funext events
    exact preserves events

/-- Failure alignment is precisely the side condition needed to transfer the
observer-indexed control law between synchronized and independent readings. -/
theorem lawfulAt_synchronized_iff_independent_of_aligned
    {Event : Type uEvent} {Receipt : Type uReceipt}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event)
    (aligned : FailureAligned left right)
    (change : Change Event Receipt) :
    LawfulAt (synchronizedSplitObserver left right) change ↔
      LawfulAt (independentObserver left right) change := by
  rw [(synchronizedSplitObserver_eq_iff_failureAligned left right).2 aligned]

/-- A synchronized optimization guard can authorize the independent observer
only after failure alignment has been proved. -/
def guardForIndependentOfAligned
    {Event : Type uEvent} {Receipt : Type uReceipt}
    (left : ObservationDiscipline.{uEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uEvent, uRightContainer, uRightValue} Event)
    (aligned : FailureAligned left right)
    (guard : Guard (synchronizedSplitObserver left right) Receipt) :
    Guard (independentObserver left right) Receipt where
  accepts := guard.accepts
  sound change accepted :=
    (lawfulAt_synchronized_iff_independent_of_aligned
      left right aligned change).1 (guard.sound change accepted)

end ObservationDiscipline

/-! ## Positive and adversarial controls -/

namespace Canary

def atMostOneCollector : WitnessCollector Bool where
  Container := Unit
  collect := fun events => if events.length ≤ 1 then some () else none

def countCollector : WitnessCollector Bool where
  Container := Nat
  collect := fun events => some events.length

def atMostOne : ObservationDiscipline Bool where
  collection := atMostOneCollector
  Value := Unit
  readout := id

def count : ObservationDiscipline Bool where
  collection := countCollector
  Value := Nat
  readout := id

theorem independent_product_retains_unilateral_success :
    (ObservationDiscipline.independentProduct atMostOne count).observe
        [false, true] =
      some ((none : Option Unit), some (2 : Nat)) :=
  rfl

theorem same_partial_discipline_is_failureAligned :
    ObservationDiscipline.FailureAligned atMostOne atMostOne := by
  intro events
  rfl

def mismatchedVisibilityChange : Change Bool Unit where
  source := [false, true]
  target := [false, true, false]
  receipt := ()

theorem mismatched_change_lawful_synchronized :
    LawfulAt
      (ObservationDiscipline.synchronizedSplitObserver atMostOne count)
      mismatchedVisibilityChange :=
  rfl

theorem mismatched_change_not_lawful_independent :
    ¬ LawfulAt
      (ObservationDiscipline.independentObserver atMostOne count)
      mismatchedVisibilityChange := by
  simp [LawfulAt, mismatchedVisibilityChange,
    ObservationDiscipline.independentObserver,
    ObservationDiscipline.independentResult,
    ObservationDiscipline.observe, atMostOne, count,
    atMostOneCollector, countCollector]

end Canary

/-! ## Axiom audit -/

#print axioms WitnessCollector.preservesIndependentResult_iff_failureAligned
#print axioms WitnessCollector.independentProduct_total
#print axioms WitnessCollector.synchronized_collect_channel
#print axioms ObservationDiscipline.preservesIndependentResult_iff_failureAligned
#print axioms ObservationDiscipline.synchronized_observe_channel
#print axioms ObservationDiscipline.synchronizedSplitObserver_eq_iff_failureAligned
#print axioms ObservationDiscipline.lawfulAt_synchronized_iff_independent_of_aligned
#print axioms ObservationDiscipline.guardForIndependentOfAligned
#print axioms Canary.independent_product_retains_unilateral_success
#print axioms Canary.same_partial_discipline_is_failureAligned
#print axioms Canary.mismatched_change_lawful_synchronized
#print axioms Canary.mismatched_change_not_lawful_independent

end Mettapedia.GSLT.Dynamics.WitnessCollectionProduct
