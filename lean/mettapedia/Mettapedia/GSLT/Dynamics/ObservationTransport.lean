import Mettapedia.GSLT.Dynamics.ExecutionPathObservation

/-!
# Observation transport along operational translations

An operational translation maps proof-relevant execution steps and complete
paths.  An observation discipline on the target can therefore be pulled back
to the source without changing either language's execution relation.

The main square says that observing a translated path in the target is exactly
the same as observing the original path with the pulled-back discipline.  The
construction acts separately on events, witness collection, and values.  It
does not assert that a lossy observation reflects paths.
-/

namespace Mettapedia.GSLT.Dynamics.ObservationTransport

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite

universe uSourceTerm uTargetTerm uSourceEvent uTargetEvent
  uContainer uValue

/-- Map one proof-relevant labeled step along an operational translation. -/
def mapEvent {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target) :
    source.LabeledStep -> target.LabeledStep
  | event =>
      { source := translation.mapTerm event.source
        target := translation.mapTerm event.target
        step := translation.mapStep event.step }

@[simp] theorem mapEvent_id {system : GSLT.{uSourceTerm}}
    (event : system.LabeledStep) :
    mapEvent (OperationalTranslation.id system) event = event := by
  cases event
  rfl

@[simp] theorem mapEvent_comp
    {first : GSLT.{uSourceTerm}} {middle : GSLT} {last : GSLT.{uTargetTerm}}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (event : first.LabeledStep) :
    mapEvent (earlier.comp later) event =
      mapEvent later (mapEvent earlier event) := by
  cases event
  rfl

namespace WitnessCollector

/-- Pull a witness collector back along a map of operational events. -/
def pullback (eventMap : SourceEvent -> TargetEvent)
    (collector : WitnessCollector.{uTargetEvent, uContainer} TargetEvent) :
    WitnessCollector SourceEvent where
  Container := collector.Container
  collect := fun events => collector.collect (events.map eventMap)

@[simp] theorem pullback_collect (eventMap : SourceEvent -> TargetEvent)
    (collector : WitnessCollector.{uTargetEvent, uContainer} TargetEvent)
    (events : List SourceEvent) :
    (pullback eventMap collector).collect events =
      collector.collect (events.map eventMap) :=
  rfl

/-- Pullback preserves chronological collection because mapping events
commutes with list concatenation. -/
def pullbackChronological (eventMap : SourceEvent -> TargetEvent)
    (collector : WitnessCollector.{uTargetEvent, uContainer} TargetEvent)
    (chronological : ChronologicalCapability collector) :
    ChronologicalCapability (pullback eventMap collector) where
  algebra := chronological.algebra
  collect_nil := chronological.collect_nil
  collect_append := by
    intro first second
    change
      collector.collect ((first ++ second).map eventMap) =
        (collector.collect (first.map eventMap)).bind fun left =>
          (collector.collect (second.map eventMap)).bind fun right =>
            chronological.algebra.op left right
    rw [List.map_append]
    exact chronological.collect_append (first.map eventMap) (second.map eventMap)

/-- Pullback also preserves an independently supplied parallel container
algebra.  The certificate that two executions are independent remains an
operational premise; this construction transports only the observation
capability. -/
def pullbackIndependentParallel (eventMap : SourceEvent -> TargetEvent)
    (collector : WitnessCollector.{uTargetEvent, uContainer} TargetEvent)
    (parallel : IndependentParallelCapability collector) :
    IndependentParallelCapability (pullback eventMap collector) where
  algebra := parallel.algebra
  commutative := parallel.commutative

end WitnessCollector

namespace ObservationDiscipline

/-- Pull a target observation discipline back along a map of events.  The
witness container and value type are retained exactly. -/
def pullback (eventMap : SourceEvent -> TargetEvent)
    (discipline : ObservationDiscipline.{uTargetEvent, uContainer, uValue}
      TargetEvent) :
    ObservationDiscipline SourceEvent where
  collection := WitnessCollector.pullback eventMap discipline.collection
  Value := discipline.Value
  readout := discipline.readout

@[simp] theorem pullback_observe (eventMap : SourceEvent -> TargetEvent)
    (discipline : ObservationDiscipline.{uTargetEvent, uContainer, uValue}
      TargetEvent)
    (events : List SourceEvent) :
    (pullback eventMap discipline).observe events =
      discipline.observe (events.map eventMap) :=
  rfl

/-- Pulling back along two event maps agrees extensionally with pulling back
along their composite. -/
theorem pullback_comp_observe
    (first : FirstEvent -> MiddleEvent) (second : MiddleEvent -> LastEvent)
    (discipline : ObservationDiscipline LastEvent)
    (events : List FirstEvent) :
    (pullback first (pullback second discipline)).observe events =
      (pullback (second ∘ first) discipline).observe events := by
  simp only [pullback_observe, List.map_map]

/-- Pullback retains ordering on the value dial exactly; it neither chooses
an order nor imposes one on disciplines that lack it. -/
def pullbackOrderedValue (eventMap : SourceEvent -> TargetEvent)
    (discipline : ObservationDiscipline.{uTargetEvent, uContainer, uValue}
      TargetEvent)
    (ordered : OrderedValueCapability discipline) :
    OrderedValueCapability (pullback eventMap discipline) where
  order := ordered.order

end ObservationDiscipline

/-! ## Naturality on complete execution paths -/

/-- Extracting events from a translated path gives exactly the pointwise
translation of the original event history. -/
theorem events_mapRoute
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    {first last : source.Term}
    (path : ExecutionPath source first last) :
    events (translation.mapRoute path) =
      (events path).map (mapEvent translation) := by
  induction path with
  | refl => rfl
  | @cons first middle last step rest inductionHypothesis =>
      change
        mapEvent translation
            ({ source := first, target := middle, step := step.down } :
              source.LabeledStep) ::
            events (translation.mapRoute rest) =
          mapEvent translation
              ({ source := first, target := middle, step := step.down } :
                source.LabeledStep) ::
            (events rest).map (mapEvent translation)
      rw [inductionHypothesis]

/-- The observation square for a complete proof-relevant path.  Translation
acts on execution; pullback acts on observation; the two orders agree. -/
theorem observe_mapRoute
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    (targetDiscipline : GSLTObservation target)
    {first last : source.Term}
    (path : ExecutionPath source first last) :
    ofDiscipline
        (ObservationDiscipline.pullback (mapEvent translation)
          targetDiscipline) path =
      ofDiscipline targetDiscipline (translation.mapRoute path) := by
  simp only [ofDiscipline_apply, ObservationDiscipline.pullback_observe,
    events_mapRoute]

/-! ## Negative control: naturality is not reflection -/

namespace Canary

abbrev system : GSLT := GSLT.discrete Bool

/-- Event-count observation has the required transport square along the
identity translation. -/
theorem identity_observation_natural (value : Bool) :
    ofDiscipline
        (ObservationDiscipline.pullback
          (mapEvent (OperationalTranslation.id system))
          ExecutionPathObservation.Canary.provenance)
        (.refl value : ExecutionPath system value value) =
      ofDiscipline ExecutionPathObservation.Canary.provenance
        ((OperationalTranslation.id system).mapRoute
          (.refl value : ExecutionPath system value value)) :=
  observe_mapRoute (OperationalTranslation.id system)
    ExecutionPathObservation.Canary.provenance _

/-- Even an exact identity transport cannot make a lossy observation reflect
distinct paths or endpoints. -/
theorem observation_naturality_does_not_imply_path_reflection :
    ofDiscipline ExecutionPathObservation.Canary.provenance
        (.refl false : ExecutionPath system false false) =
      ofDiscipline ExecutionPathObservation.Canary.provenance
        (.refl true : ExecutionPath system true true) :=
  ExecutionPathObservation.Canary.distinct_empty_paths_same_observation

end Canary

#print axioms mapEvent_comp
#print axioms events_mapRoute
#print axioms observe_mapRoute
#print axioms Canary.observation_naturality_does_not_imply_path_reflection

end Mettapedia.GSLT.Dynamics.ObservationTransport
