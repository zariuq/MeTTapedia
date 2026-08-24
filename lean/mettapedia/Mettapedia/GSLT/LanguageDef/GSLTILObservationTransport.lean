import Mettapedia.GSLT.Dynamics.ObservationTransport
import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
import Mettapedia.GSLT.LanguageDef.GSLTILRouteEquipment

/-!
# Observation transport for represented GSLT-IL routes

Loose authored routes retain their relational meaning without a license.
When a route additionally earns proof-relevant representability and step
preservation, it induces a functional execution-path transport.  Target
observation disciplines then pull back canonically along that admitted path
map.

This is an observation theorem, not an admission mechanism.  In particular,
it neither grants representability to arbitrary loose routes nor turns a
lossy observation into reflection of execution histories.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.GSLT.Dynamics.ObservationTransport
open Mettapedia.GSLT.IndexedOperational

universe uTerm

namespace RepresentedOperationalRoute

/-- Pull a target observation discipline back along the direct path map
earned by a represented operational route. -/
def pullbackObservation {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target) :
    GSLTObservation source :=
  ObservationDiscipline.pullback
    (mapEvent route.toOperationalTranslation) targetDiscipline

/-- Chronological combination remains available after observation pullback. -/
def pullbackChronological {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection) :
    ChronologicalCapability
      (route.pullbackObservation targetDiscipline).collection :=
  WitnessCollector.pullbackChronological
    (mapEvent route.toOperationalTranslation) targetDiscipline.collection
      chronological

/-- An existing independent-parallel observation algebra is retained.  Route
representability does not itself certify that two source executions are
independent. -/
def pullbackIndependentParallel {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (parallel : IndependentParallelCapability targetDiscipline.collection) :
    IndependentParallelCapability
      (route.pullbackObservation targetDiscipline).collection :=
  WitnessCollector.pullbackIndependentParallel
    (mapEvent route.toOperationalTranslation) targetDiscipline.collection
      parallel

/-- Ordering of observation values is transported without becoming a
requirement on all disciplines. -/
def pullbackOrderedValue {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (ordered : OrderedValueCapability targetDiscipline) :
    OrderedValueCapability (route.pullbackObservation targetDiscipline) :=
  ObservationDiscipline.pullbackOrderedValue
    (mapEvent route.toOperationalTranslation) targetDiscipline ordered

/-- The observed GSLT-IL transport square on complete proof-relevant paths. -/
theorem observe_path {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {first last : source.Term}
    (path : ExecutionPath source first last) :
    ofDiscipline (route.pullbackObservation targetDiscipline) path =
      ofDiscipline targetDiscipline (route.pathFunctor.map path) :=
  observe_mapRoute route.toOperationalTranslation targetDiscipline path

/-- Observation pullback respects composition of represented routes.  The
intermediate loose witness remains in route semantics; the observation law
concerns the compiled complete-path transport that representability earns. -/
theorem pullbackObservation_comp_observe
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    (discipline : GSLTObservation last)
    (events : List first.LabeledStep) :
    ((comp earlier later).pullbackObservation discipline).observe events =
      (earlier.pullbackObservation
        (later.pullbackObservation discipline)).observe events := by
  change discipline.observe
      (events.map (mapEvent (comp earlier later).toOperationalTranslation)) =
    discipline.observe
      ((events.map (mapEvent earlier.toOperationalTranslation)).map
        (mapEvent later.toOperationalTranslation))
  rw [toOperationalTranslation_comp, List.map_map]
  congr 2

/-! ## The public capability-indexed architecture -/

/-- Collected source paths form the public observation architecture for the
pulled-back discipline.  The execution remains a source GSLT path; only its
event observation is transported. -/
def pullbackCollectedArchitecture {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target) :
    CapabilityIndexedObservationArchitecture source.Term
      (CollectedGSLTPath.CollectedPath source
        (route.pullbackObservation targetDiscipline)) :=
  CollectedGSLTPath.architecture source
    (route.pullbackObservation targetDiscipline)

/-- The corresponding target architecture of accepted paths. -/
def targetCollectedArchitecture {source target : GSLT.{uTerm}}
    (_route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target) :
    CapabilityIndexedObservationArchitecture target.Term
      (CollectedGSLTPath.CollectedPath target targetDiscipline) :=
  CollectedGSLTPath.architecture target targetDiscipline

/-- A collected source path maps to a collected target path with the same
container.  Collection evidence is reconstructed from the observation
naturality square, not postulated. -/
def mapCollectedPath {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {first last : source.Term}
    (execution : CollectedGSLTPath.CollectedPath source
      (route.pullbackObservation targetDiscipline) first last) :
    CollectedGSLTPath.CollectedPath target targetDiscipline
      (route.toOperationalTranslation.mapTerm first)
      (route.toOperationalTranslation.mapTerm last) where
  path := route.pathFunctor.map execution.path
  container := execution.container
  collected := by
    change targetDiscipline.collection.collect
        (ExecutionPathObservation.events
          (route.toOperationalTranslation.mapRoute execution.path)) =
      some execution.container
    rw [ObservationTransport.events_mapRoute]
    exact execution.collected

@[simp] theorem mapCollectedPath_container
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {first last : source.Term}
    (execution : CollectedGSLTPath.CollectedPath source
      (route.pullbackObservation targetDiscipline) first last) :
    (mapCollectedPath route targetDiscipline execution).container =
      execution.container :=
  rfl

/-- Route transport preserves the declared semantic value of a collected
execution while retaining the source execution as a separate object. -/
@[simp] theorem mapCollectedPath_value
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {first last : source.Term}
    (execution : CollectedGSLTPath.CollectedPath source
      (route.pullbackObservation targetDiscipline) first last) :
    (route.targetCollectedArchitecture targetDiscipline).observation.value
        (mapCollectedPath route targetDiscipline execution) =
      (route.pullbackCollectedArchitecture targetDiscipline).observation.value
        execution :=
  rfl

/-- Mapping a collected path places its retained container in the target
operational domain.  A represented route transports observation; it does not
infer a target execution from a bare value. -/
theorem mapCollectedPath_container_mem
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {first last : source.Term}
    (execution : CollectedGSLTPath.CollectedPath source
      (route.pullbackObservation targetDiscipline) first last) :
    (route.targetCollectedArchitecture targetDiscipline).domain.contains
      execution.container := by
  exact
    (route.targetCollectedArchitecture targetDiscipline).observed_container_mem
      (mapCollectedPath route targetDiscipline execution)

/-! ## Positive and negative controls -/

namespace Canary

abbrev system : GSLT := GSLT.discrete Bool

def identityRoute : RepresentedOperationalRoute system system :=
  RepresentedOperationalRoute.id system

/-- A represented route really does transport an observation of a complete
path. -/
theorem identity_route_observes (value : Bool) :
    ofDiscipline
        (identityRoute.pullbackObservation
          ExecutionPathObservation.Canary.provenance)
        (.refl value : ExecutionPath system value value) =
      ofDiscipline ExecutionPathObservation.Canary.provenance
        (identityRoute.pathFunctor.map
          (.refl value : ExecutionPath system value value)) :=
  identityRoute.observe_path ExecutionPathObservation.Canary.provenance _

/-- Even on an admitted route, equality of observed values is weaker than
equality of the original execution endpoints. -/
theorem admitted_observation_does_not_reflect_endpoints :
    false ≠ true ∧
      ofDiscipline ExecutionPathObservation.Canary.provenance
          (.refl false : ExecutionPath system false false) =
        ofDiscipline ExecutionPathObservation.Canary.provenance
          (.refl true : ExecutionPath system true true) :=
  ⟨by decide,
    ExecutionPathObservation.Canary.distinct_empty_paths_same_observation⟩

end Canary

#print axioms observe_path
#print axioms pullbackObservation_comp_observe
#print axioms mapCollectedPath
#print axioms mapCollectedPath_value
#print axioms mapCollectedPath_container_mem
#print axioms Canary.identity_route_observes
#print axioms Canary.admitted_observation_does_not_reflect_endpoints

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
