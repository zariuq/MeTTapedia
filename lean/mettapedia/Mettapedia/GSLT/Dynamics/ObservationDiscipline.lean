import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Dynamics.IndexedEventValuation

/-!
# Observation disciplines over proof-relevant event histories

A transition system determines which events can occur.  An observation
discipline adds two independent choices without adding or removing events:

* a witness container `S`, populated from an event history;
* a value type `V`, read from the retained container.

The factorization is therefore `history -> Option S -> Option V`.  The
container may retain more information than any particular readout.  In
particular, a scalar scheduling score is a map out of `V`, not a replacement
for the witness container or for the execution that produced it.

No algebra is required by the basic definition.  Chronological composition,
independent parallel composition, and ordering are separate capabilities.
This lets evidence, provenance, work/span, and partial resource authority use
the same interface without pretending that they share one semiring or
quantale.
-/

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uEvent uContainer uValue uOtherContainer uOtherValue

/-- The `S` dial of an observation discipline.  Failure is explicit: a
discipline may decline to collect a history whose resource claims cannot be
combined. -/
structure WitnessCollector (Event : Type uEvent) where
  Container : Type uContainer
  collect : List Event -> Option Container

namespace WitnessCollector

/-- A collector is total when it accepts every finite history. -/
def Total {Event : Type uEvent}
    (collector : WitnessCollector Event) : Prop :=
  forall events, Exists fun result => collector.collect events = some result

/-- Independent collectors retain both witness coordinates.  Acceptance is
componentwise: failure of either coordinate remains visible. -/
def prod {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uContainer} Event)
    (right : WitnessCollector.{uEvent, uOtherContainer} Event) :
    WitnessCollector Event where
  Container := left.Container × right.Container
  collect := fun events =>
    (left.collect events).bind fun leftContainer =>
      (right.collect events).bind fun rightContainer =>
        some (leftContainer, rightContainer)

/-- Postcompose collection with a container map.  This may deliberately
forget witness information. -/
def map {Event : Type uEvent}
    (collector : WitnessCollector.{uEvent, uContainer} Event)
    (translate : collector.Container -> Other) : WitnessCollector Event where
  Container := Other
  collect := fun events => (collector.collect events).map translate

@[simp] theorem prod_collect {Event : Type uEvent}
    (left : WitnessCollector.{uEvent, uContainer} Event)
    (right : WitnessCollector.{uEvent, uOtherContainer} Event)
    (events : List Event) :
    (left.prod right).collect events =
      (left.collect events).bind fun leftContainer =>
        (right.collect events).bind fun rightContainer =>
          some (leftContainer, rightContainer) :=
  rfl

@[simp] theorem map_collect {Event : Type uEvent}
    (collector : WitnessCollector.{uEvent, uContainer} Event)
    (translate : collector.Container -> Other) (events : List Event) :
    (collector.map translate).collect events =
      (collector.collect events).map translate :=
  rfl

/-- One collector factors through another when a fixed container map recovers
its result for every history. -/
def FactorsThrough {Event : Type uEvent}
    (source : WitnessCollector.{uEvent, uContainer} Event)
    (target : WitnessCollector.{uEvent, uOtherContainer} Event)
    (translate : source.Container -> target.Container) : Prop :=
  forall events,
    (source.collect events).map translate = target.collect events

/-- The event valuation interface already in the tree is the special case in
which the chronological witness container is also the grade carrier. -/
def ofValuation {Event : Type uEvent}
    (valuation : Valuation.{uEvent, uContainer} Event) :
    WitnessCollector Event where
  Container := valuation.Grade
  collect := valuation.historyGrade

end WitnessCollector

/-- An observation discipline factors event histories through a witness
container `S` before reading a value in `V`. -/
structure ObservationDiscipline (Event : Type uEvent) where
  collection : WitnessCollector.{uEvent, uContainer} Event
  Value : Type uValue
  readout : collection.Container -> Value

/-- A discipline over the proof-relevant one-step occurrences of a GSLT.
The GSLT remains a parameter, so adding a discipline cannot add a rewrite. -/
abbrev GSLTObservation (system : GSLT) :=
  ObservationDiscipline system.LabeledStep

/-- A proof-relevant event presentation over a fixed GSLT, together with an
observation discipline on those richer events.  Several events may erase to
the same base step, retaining occurrence identity or authority evidence that
the GSLT relation alone does not record. -/
structure PresentedObservation (system : GSLT) where
  Event : Type uEvent
  erase : Event -> system.LabeledStep
  discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event

namespace ObservationDiscipline

/-- Observe a history by collecting its witnesses and then applying the value
readout. -/
def observe {Event : Type uEvent}
    (discipline : ObservationDiscipline Event) (events : List Event) :
    Option discipline.Value :=
  (discipline.collection.collect events).map discipline.readout

/-- Change only the value dial, retaining the exact same witness container. -/
def mapValue {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (translate : discipline.Value -> OtherValue) :
    ObservationDiscipline Event where
  collection := discipline.collection
  Value := OtherValue
  readout := translate ∘ discipline.readout

/-- Combine two disciplines without identifying either witness or value
coordinate. -/
def prod {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (right : ObservationDiscipline.{uEvent, uOtherContainer, uOtherValue} Event) :
    ObservationDiscipline Event where
  collection := left.collection.prod right.collection
  Value := left.Value × right.Value
  readout := fun containers =>
    (left.readout containers.1, right.readout containers.2)

@[simp] theorem mapValue_observe {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (translate : discipline.Value -> OtherValue) (events : List Event) :
    (discipline.mapValue translate).observe events =
      (discipline.observe events).map translate := by
  unfold observe mapValue
  cases discipline.collection.collect events <;> rfl

@[simp] theorem prod_observe {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (right : ObservationDiscipline.{uEvent, uOtherContainer, uOtherValue} Event)
    (events : List Event) :
    (left.prod right).observe events =
      (left.observe events).bind fun leftValue =>
        (right.observe events).bind fun rightValue =>
          some (leftValue, rightValue) := by
  cases leftEquation : left.collection.collect events <;>
    cases rightEquation : right.collection.collect events <;>
      simp [observe, prod, WitnessCollector.prod, leftEquation, rightEquation]

/-- Adding a total right-hand observation axis cannot change acceptance or
the value of the left axis. -/
theorem map_fst_prod_observe_of_right_total {Event : Type uEvent}
    (left : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (right : ObservationDiscipline.{uEvent, uOtherContainer, uOtherValue} Event)
    (total : right.collection.Total) (events : List Event) :
    Option.map Prod.fst ((left.prod right).observe events) =
      left.observe events := by
  rw [prod_observe]
  obtain ⟨rightContainer, rightEquation⟩ := total events
  unfold observe
  rw [rightEquation]
  cases left.collection.collect events <;> rfl

/-- The existing event valuation is an identity-valued observation
discipline. -/
def ofValuation {Event : Type uEvent}
    (valuation : Valuation.{uEvent, uContainer} Event) :
    ObservationDiscipline Event where
  collection := WitnessCollector.ofValuation valuation
  Value := valuation.Grade
  readout := id

@[simp] theorem observe_ofValuation {Event : Type uEvent}
    (valuation : Valuation.{uEvent, uContainer} Event) (events : List Event) :
    (ofValuation valuation).observe events = valuation.historyGrade events := by
  simp [observe, ofValuation, WitnessCollector.ofValuation]

/-- A readout is faithful when it retains every distinction in its witness
container. -/
def Faithful {Event : Type uEvent}
    (discipline : ObservationDiscipline Event) : Prop :=
  Function.Injective discipline.readout

/-- A lossy readout identifies at least two witness containers. -/
def Lossy {Event : Type uEvent}
    (discipline : ObservationDiscipline Event) : Prop :=
  Not discipline.Faithful

/-- One readout collision proves lossiness. -/
theorem lossy_of_collision {Event : Type uEvent}
    (discipline : ObservationDiscipline Event)
    {first second : discipline.collection.Container}
    (distinct : first ≠ second)
    (collision : discipline.readout first = discipline.readout second) :
    discipline.Lossy := by
  intro injective
  exact distinct (injective collision)

/-- A lossy value cannot reconstruct the retained witness container. -/
theorem no_reconstruction_of_lossy {Event : Type uEvent}
    (discipline : ObservationDiscipline Event) (lossy : discipline.Lossy) :
    Not (Exists fun recover : discipline.Value -> discipline.collection.Container =>
      Function.LeftInverse recover discipline.readout) := by
  rintro ⟨recover, leftInverse⟩
  exact lossy leftInverse.injective

/-- A scalar scheduler score is another value readout, never a replacement
for the underlying discipline. -/
abbrev scalarize {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.Value -> Scalar) : ObservationDiscipline Event :=
  discipline.mapValue score

end ObservationDiscipline

namespace PresentedObservation

/-- Completeness is optional: every base step has at least one rich event.
Partial authority presentations deliberately need not satisfy it. -/
def Complete {system : GSLT}
    (presentation : PresentedObservation system) : Prop :=
  forall step : system.LabeledStep,
    Nonempty { event : presentation.Event // presentation.erase event = step }

/-- Change only the value dial of a presented observation.  The base GSLT,
event type, and erasure map remain definitionally unchanged. -/
def mapValue {system : GSLT}
    (presentation : PresentedObservation.{uEvent, uContainer, uValue} system)
    (translate : presentation.discipline.Value -> OtherValue) :
    PresentedObservation system where
  Event := presentation.Event
  erase := presentation.erase
  discipline := presentation.discipline.mapValue translate

@[simp] theorem mapValue_erase {system : GSLT}
    (presentation : PresentedObservation.{uEvent, uContainer, uValue} system)
    (translate : presentation.discipline.Value -> OtherValue)
    (event : presentation.Event) :
    (presentation.mapValue translate).erase event = presentation.erase event :=
  rfl

end PresentedObservation

/-! ## Optional algebraic capabilities -/

/-- Chronological compositionality is an optional capability of a witness
collector, not a requirement on every observation discipline. -/
structure ChronologicalCapability {Event : Type uEvent}
    (collector : WitnessCollector Event) where
  algebra : PartialMonoid collector.Container
  collect_nil : collector.collect [] = some algebra.unit
  collect_append : forall first second,
    collector.collect (first ++ second) =
      (collector.collect first).bind fun left =>
        (collector.collect second).bind fun right =>
          algebra.op left right

/-- Independent-parallel composition is a separate, commutative partial
capability on retained containers.  Its use presupposes an independent-
execution certificate supplied by the operational theory. -/
structure IndependentParallelCapability {Event : Type uEvent}
    (collector : WitnessCollector Event) where
  algebra : PartialMonoid collector.Container
  commutative : forall left right,
    algebra.op left right = algebra.op right left

/-- Ordering is a capability of a value dial, needed by ranking or scheduling
but absent from the basic observation interface. -/
structure OrderedValueCapability {Event : Type uEvent}
    (discipline : ObservationDiscipline Event) where
  order : Preorder discipline.Value

/-- Existing compositional event valuations supply chronological capability
without adding any new algebra. -/
def chronologicalCapabilityOfValuation {Event : Type uEvent}
    (valuation : Valuation.{uEvent, uContainer} Event) :
    ChronologicalCapability
      (WitnessCollector.ofValuation valuation) where
  algebra := valuation.algebra
  collect_nil := Valuation.historyGrade_nil valuation
  collect_append := Valuation.historyGrade_append valuation

/-! ## Work/span as one declared valuation -/

namespace WorkSpanObservation

open Mettapedia.Algebra

/-- Sequential work/span composition supplies the history algebra. -/
def sequentialAlgebra : PartialMonoid WorkSpan where
  unit := 0
  op := fun first second => some (WorkSpan.sequential first second)
  unit_op := by simp
  op_unit := by simp
  op_assoc := by simp [WorkSpan.sequential_assoc]

/-- Independent work/span composition is a different algebra on the same
container. -/
def parallelAlgebra : PartialMonoid WorkSpan where
  unit := 0
  op := fun first second => some (WorkSpan.parallel first second)
  unit_op := by simp
  op_unit := by simp
  op_assoc := by simp [WorkSpan.parallel_assoc]

/-- Assign a declared work/span cost to each event and collect histories
sequentially. -/
def valuation {Event : Type uEvent} (eventCost : Event -> WorkSpan) :
    Valuation Event where
  Grade := WorkSpan
  algebra := sequentialAlgebra
  grade := fun event => some (eventCost event)

/-- Work/span is interpreted as a value of retained operational events. -/
def discipline {Event : Type uEvent} (eventCost : Event -> WorkSpan) :
    ObservationDiscipline Event :=
  ObservationDiscipline.ofValuation (valuation eventCost)

/-- The same work/span container has chronological composition. -/
def chronological {Event : Type uEvent} (eventCost : Event -> WorkSpan) :
    ChronologicalCapability (discipline eventCost).collection :=
  chronologicalCapabilityOfValuation (valuation eventCost)

/-- The same work/span container also has a distinct operation for already
certified independent branches. -/
def independentParallel {Event : Type uEvent} (eventCost : Event -> WorkSpan) :
    IndependentParallelCapability (discipline eventCost).collection where
  algebra := parallelAlgebra
  commutative := by
    intro left right
    simp [parallelAlgebra, WorkSpan.parallel_comm]

/-- A work-only scheduler score forgets critical-path span. -/
def workOnly {Event : Type uEvent} (eventCost : Event -> WorkSpan) :
    ObservationDiscipline Event :=
  (discipline eventCost).scalarize WorkSpan.work

end WorkSpanObservation

/-! ## Separating examples for the `S` and `V` dials -/

namespace Canary

inductive Event where
  | left
  | right
  deriving DecidableEq, Repr

/-- Exact chronological provenance retains order and multiplicity. -/
def provenanceCollection : WitnessCollector Event where
  Container := List Event
  collect := some

def provenance : ObservationDiscipline Event where
  collection := provenanceCollection
  Value := List Event
  readout := id

/-- Reading only the length changes `V` while retaining exactly the same
container `S`. -/
def provenanceLength : ObservationDiscipline Event :=
  provenance.mapValue List.length

/-- Direct counting changes the container `S` while returning the same value
as `provenanceLength`. -/
def countCollection : WitnessCollector Event where
  Container := Nat
  collect := fun events => some events.length

def directCount : ObservationDiscipline Event where
  collection := countCollection
  Value := Nat
  readout := id

@[simp] theorem provenance_observe (events : List Event) :
    provenance.observe events = some events :=
  rfl

@[simp] theorem provenanceLength_observe (events : List Event) :
    provenanceLength.observe events = some events.length :=
  rfl

@[simp] theorem directCount_observe (events : List Event) :
    directCount.observe events = some events.length :=
  rfl

/-- Distinct witness containers can induce the same value observation.  Thus
`V` does not determine `S`. -/
theorem provenanceLength_eq_directCount (events : List Event) :
    provenanceLength.observe events = directCount.observe events :=
  rfl

/-- Event count cannot reconstruct chronological provenance.  This is a
container-level obstruction, independent of the later value readout. -/
theorem no_count_to_provenance_factorization :
    Not (Exists fun recover : Nat -> List Event =>
      countCollection.FactorsThrough provenanceCollection recover) := by
  rintro ⟨recover, factors⟩
  have leftRight := factors [Event.left, Event.right]
  have rightLeft := factors [Event.right, Event.left]
  simp [countCollection, provenanceCollection] at leftRight rightLeft
  have impossible : [Event.left, Event.right] = [Event.right, Event.left] :=
    leftRight.symm.trans rightLeft
  simp at impossible

def unitWork : Event -> Mettapedia.Algebra.WorkSpan :=
  fun _ => ⟨1, 1⟩

@[simp] theorem two_events_sequential_workSpan :
    (WorkSpanObservation.discipline unitWork).observe
        [Event.left, Event.right] = some ⟨2, 2⟩ :=
  rfl

@[simp] theorem two_events_parallel_workSpan :
    (WorkSpanObservation.independentParallel unitWork).algebra.op
        ⟨1, 1⟩ ⟨1, 1⟩ = some ⟨2, 1⟩ :=
  rfl

/-- The parallel capability is not a second spelling of chronological
composition. -/
theorem parallel_workSpan_ne_sequential_workSpan :
    (WorkSpanObservation.independentParallel unitWork).algebra.op
        ⟨1, 1⟩ ⟨1, 1⟩ ≠
      (WorkSpanObservation.chronological unitWork).algebra.op
        ⟨1, 1⟩ ⟨1, 1⟩ := by
  intro equal
  have values : (⟨2, 1⟩ : Mettapedia.Algebra.WorkSpan) = ⟨2, 2⟩ :=
    Option.some.inj equal
  have spans := congrArg Mettapedia.Algebra.WorkSpan.span values
  norm_num at spans

/-- A scalar work score cannot reconstruct span. -/
theorem workOnly_isLossy :
    (WorkSpanObservation.workOnly unitWork).Lossy := by
  unfold WorkSpanObservation.workOnly ObservationDiscipline.scalarize
    ObservationDiscipline.mapValue ObservationDiscipline.Lossy
    ObservationDiscipline.Faithful
  intro injective
  have equal : (⟨2, 1⟩ : Mettapedia.Algebra.WorkSpan) = ⟨2, 2⟩ :=
    injective rfl
  have spans := congrArg Mettapedia.Algebra.WorkSpan.span equal
  norm_num at spans

/-- Consequently no decoder from a work-only scheduler score recovers the
full work/span value. -/
theorem no_workOnly_reconstruction :
    Not (Exists fun recover : Nat -> Mettapedia.Algebra.WorkSpan =>
      Function.LeftInverse recover
        (WorkSpanObservation.workOnly unitWork).readout) :=
  ObservationDiscipline.no_reconstruction_of_lossy
    (WorkSpanObservation.workOnly unitWork) workOnly_isLossy

end Canary

end Mettapedia.GSLT.Dynamics
