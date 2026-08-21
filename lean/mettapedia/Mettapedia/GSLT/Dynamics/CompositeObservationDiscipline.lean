import Mettapedia.GSLT.Dynamics.ObservationDiscipline

/-!
# Parallel composition of observation disciplines

Two observers may consume different event types and retain genuinely different
witness containers.  Their parallel composition does not require a distributive
law that merges those containers into one collection monad.  Instead, a joint
history is an interleaving of the two event types, each observer receives its
own projection, and the composite retains the product of both observations.

This is the minimal positive construction behind a composite learner with
separate observational capabilities.  It proves that each total component is
recoverable from the composite and that any distinction visible to either
component remains visible jointly.  It deliberately makes no claim that the
two collection disciplines support a monad distributive law or a single merged
logic.
-/

namespace Mettapedia.GSLT.Dynamics

universe uLeftEvent uRightEvent uLeftContainer uRightContainer
  uLeftValue uRightValue

/-- The left-hand event history visible inside an interleaving. -/
def leftProjection {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent} :
    List (Sum LeftEvent RightEvent) -> List LeftEvent :=
  List.filterMap fun
    | .inl event => some event
    | .inr _ => none

/-- The right-hand event history visible inside an interleaving. -/
def rightProjection {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent} :
    List (Sum LeftEvent RightEvent) -> List RightEvent :=
  List.filterMap fun
    | .inl _ => none
    | .inr event => some event

@[simp] theorem leftProjection_nil
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent} :
    leftProjection ([] : List (Sum LeftEvent RightEvent)) = [] :=
  rfl

@[simp] theorem leftProjection_inl_cons
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (event : LeftEvent) (events : List (Sum LeftEvent RightEvent)) :
    leftProjection (.inl event :: events) = event :: leftProjection events :=
  rfl

@[simp] theorem leftProjection_inr_cons
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (event : RightEvent) (events : List (Sum LeftEvent RightEvent)) :
    leftProjection (.inr event :: events) = leftProjection events :=
  rfl

@[simp] theorem rightProjection_nil
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent} :
    rightProjection ([] : List (Sum LeftEvent RightEvent)) = [] :=
  rfl

@[simp] theorem rightProjection_inl_cons
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (event : LeftEvent) (events : List (Sum LeftEvent RightEvent)) :
    rightProjection (.inl event :: events) = rightProjection events :=
  rfl

@[simp] theorem rightProjection_inr_cons
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (event : RightEvent) (events : List (Sum LeftEvent RightEvent)) :
    rightProjection (.inr event :: events) = event :: rightProjection events :=
  rfl

@[simp] theorem leftProjection_append
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (first second : List (Sum LeftEvent RightEvent)) :
    leftProjection (first ++ second) =
      leftProjection first ++ leftProjection second := by
  simp [leftProjection]

@[simp] theorem rightProjection_append
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (first second : List (Sum LeftEvent RightEvent)) :
    rightProjection (first ++ second) =
      rightProjection first ++ rightProjection second := by
  simp [rightProjection]

namespace WitnessCollector

/-- Run a left observer on the left projection of a joint history. -/
def onLeft {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (collector : WitnessCollector.{uLeftEvent, uLeftContainer} LeftEvent) :
    WitnessCollector (Sum LeftEvent RightEvent) where
  Container := collector.Container
  collect := fun events => collector.collect (leftProjection events)

/-- Run a right observer on the right projection of a joint history. -/
def onRight {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (collector : WitnessCollector.{uRightEvent, uRightContainer} RightEvent) :
    WitnessCollector (Sum LeftEvent RightEvent) where
  Container := collector.Container
  collect := fun events => collector.collect (rightProjection events)

@[simp] theorem onLeft_collect
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (collector : WitnessCollector.{uLeftEvent, uLeftContainer} LeftEvent)
    (events : List (Sum LeftEvent RightEvent)) :
    (collector.onLeft (RightEvent := RightEvent)).collect events =
      collector.collect (leftProjection events) :=
  rfl

@[simp] theorem onRight_collect
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (collector : WitnessCollector.{uRightEvent, uRightContainer} RightEvent)
    (events : List (Sum LeftEvent RightEvent)) :
    (collector.onRight (LeftEvent := LeftEvent)).collect events =
      collector.collect (rightProjection events) :=
  rfl

/-- Totality is preserved when an observer is run on one projection. -/
theorem total_onLeft
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    {collector : WitnessCollector.{uLeftEvent, uLeftContainer} LeftEvent}
    (total : collector.Total) :
    (collector.onLeft (RightEvent := RightEvent)).Total := by
  intro events
  exact total (leftProjection events)

/-- Symmetric totality theorem for the right projection. -/
theorem total_onRight
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    {collector : WitnessCollector.{uRightEvent, uRightContainer} RightEvent}
    (total : collector.Total) :
    (collector.onRight (LeftEvent := LeftEvent)).Total := by
  intro events
  exact total (rightProjection events)

end WitnessCollector

namespace ObservationDiscipline

/-- Lift a left discipline to joint histories without changing its container
or value dial. -/
def onLeft {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (discipline :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent) :
    ObservationDiscipline (Sum LeftEvent RightEvent) where
  collection := discipline.collection.onLeft
  Value := discipline.Value
  readout := discipline.readout

/-- Lift a right discipline to joint histories without changing its container
or value dial. -/
def onRight {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (discipline :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent) :
    ObservationDiscipline (Sum LeftEvent RightEvent) where
  collection := discipline.collection.onRight
  Value := discipline.Value
  readout := discipline.readout

@[simp] theorem onLeft_observe
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (discipline :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (events : List (Sum LeftEvent RightEvent)) :
    (discipline.onLeft (RightEvent := RightEvent)).observe events =
      discipline.observe (leftProjection events) :=
  rfl

@[simp] theorem onRight_observe
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (discipline :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (events : List (Sum LeftEvent RightEvent)) :
    (discipline.onRight (LeftEvent := LeftEvent)).observe events =
      discipline.observe (rightProjection events) :=
  rfl

/-- Parallel composition runs two observers on their respective projections
and retains both witness and value coordinates. -/
def parallelComposite
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent) :
    ObservationDiscipline (Sum LeftEvent RightEvent) :=
  (left.onLeft (RightEvent := RightEvent)).prod
    (right.onRight (LeftEvent := LeftEvent))

@[simp] theorem parallelComposite_observe
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (events : List (Sum LeftEvent RightEvent)) :
    (parallelComposite left right).observe events =
      (left.observe (leftProjection events)).bind fun leftValue =>
        (right.observe (rightProjection events)).bind fun rightValue =>
          some (leftValue, rightValue) := by
  exact ObservationDiscipline.prod_observe
    (left.onLeft (RightEvent := RightEvent))
    (right.onRight (LeftEvent := LeftEvent)) events

/-- Symmetric form of the existing product projection theorem. -/
theorem map_snd_prod_observe_of_left_total
    {Event : Type uLeftEvent}
    (left : ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} Event)
    (right : ObservationDiscipline.{uLeftEvent, uRightContainer, uRightValue} Event)
    (total : left.collection.Total) (events : List Event) :
    Option.map Prod.snd ((left.prod right).observe events) =
      right.observe events := by
  rw [prod_observe]
  obtain ⟨leftContainer, leftEquation⟩ := total events
  unfold observe
  rw [leftEquation]
  cases right.collection.collect events <;> rfl

/-- If the other component is total, the left observation is exactly
recoverable from the composite. -/
theorem map_fst_parallelComposite_observe_of_right_total
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (rightTotal : right.collection.Total)
    (events : List (Sum LeftEvent RightEvent)) :
    Option.map Prod.fst ((parallelComposite left right).observe events) =
      left.observe (leftProjection events) := by
  exact ObservationDiscipline.map_fst_prod_observe_of_right_total
    (left.onLeft (RightEvent := RightEvent))
    (right.onRight (LeftEvent := LeftEvent))
    (WitnessCollector.total_onRight rightTotal) events

/-- Symmetrically, a total left component cannot alter or hide the right
observation. -/
theorem map_snd_parallelComposite_observe_of_left_total
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (leftTotal : left.collection.Total)
    (events : List (Sum LeftEvent RightEvent)) :
    Option.map Prod.snd ((parallelComposite left right).observe events) =
      right.observe (rightProjection events) := by
  exact map_snd_prod_observe_of_left_total
    (left.onLeft (RightEvent := RightEvent))
    (right.onRight (LeftEvent := LeftEvent))
    (WitnessCollector.total_onLeft leftTotal) events

/-- A distinction made by the left observer survives in the composite. -/
theorem parallelComposite_distinguishes_of_left
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (rightTotal : right.collection.Total)
    {first second : List (Sum LeftEvent RightEvent)}
    (distinguishes :
      left.observe (leftProjection first) ≠
        left.observe (leftProjection second)) :
    (parallelComposite left right).observe first ≠
      (parallelComposite left right).observe second := by
  intro equal
  apply distinguishes
  rw [← map_fst_parallelComposite_observe_of_right_total
      left right rightTotal first]
  rw [equal]
  exact map_fst_parallelComposite_observe_of_right_total
    left right rightTotal second

/-- A distinction made by the right observer also survives jointly. -/
theorem parallelComposite_distinguishes_of_right
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (leftTotal : left.collection.Total)
    {first second : List (Sum LeftEvent RightEvent)}
    (distinguishes :
      right.observe (rightProjection first) ≠
        right.observe (rightProjection second)) :
    (parallelComposite left right).observe first ≠
      (parallelComposite left right).observe second := by
  intro equal
  apply distinguishes
  rw [← map_snd_parallelComposite_observe_of_left_total
      left right leftTotal first]
  rw [equal]
  exact map_snd_parallelComposite_observe_of_left_total
    left right leftTotal second

/-- Independent interleaving order is invisible to a composite whose two
components observe only their own projected histories. -/
theorem parallelComposite_commutes_adjacent_cross_events
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (front back : List (Sum LeftEvent RightEvent))
    (leftEvent : LeftEvent) (rightEvent : RightEvent) :
    (parallelComposite left right).observe
        (front ++ [.inl leftEvent, .inr rightEvent] ++ back) =
      (parallelComposite left right).observe
        (front ++ [.inr rightEvent, .inl leftEvent] ++ back) := by
  simp [parallelComposite_observe]

end ObservationDiscipline

end Mettapedia.GSLT.Dynamics
