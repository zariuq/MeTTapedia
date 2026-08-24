import Mettapedia.GSLT.Dynamics.CapabilityGeneratedObservationUniversal
import Mettapedia.GSLT.LanguageDef.GSLTILObservationTransport

/-!
# Capability-generated observation domains along represented GSLT-IL routes

A represented operational route earns a functional map of proof-relevant
events.  A target observation discipline therefore pulls back to the source,
as do its explicitly supplied chronological and parallel container
capabilities.  This module shows that the complete capability-construction
tree realizes back into the target domain.

Representability does not create independence evidence.  The family that
authorizes independent composition remains an explicit parameter, and a
source construction can use a parallel node only when that family is
inhabited for the selected pair.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObservationTransport

universe uTerm uAuthority uDecision

namespace RepresentedOperationalRoute

/-- The capability-generated source domain obtained by pulling a target
discipline and its declared collection capabilities along a represented
route. -/
def pullbackCapabilityDomain {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection)
    (parallel : IndependentParallelCapability targetDiscipline.collection)
    (Independent : targetDiscipline.collection.Container →
      targetDiscipline.collection.Container → Type uAuthority) :
    (route.pullbackObservation targetDiscipline).OperationalDomain :=
  ObservationDiscipline.OperationalDomain.capabilityGenerated
    (route.pullbackObservation targetDiscipline)
    (route.pullbackChronological targetDiscipline chronological)
    (route.pullbackIndependentParallel targetDiscipline parallel)
    Independent

/-- The pulled capability domain has no route-specific extra states: it is
the least source operational domain containing collected source histories and
closed under the pulled chronological and authorized-parallel capabilities. -/
theorem pullbackCapabilityDomain_least
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection)
    (parallel : IndependentParallelCapability targetDiscipline.collection)
    (Independent : targetDiscipline.collection.Container →
      targetDiscipline.collection.Container → Type uAuthority)
    (closed : ObservationDiscipline.OperationalDomain.CapabilityClosed
      (route.pullbackChronological targetDiscipline chronological)
      (route.pullbackIndependentParallel targetDiscipline parallel)
      Independent)
    {container : targetDiscipline.collection.Container}
    (member :
      (route.pullbackCapabilityDomain targetDiscipline chronological parallel
        Independent).contains container) :
    closed.contains container := by
  exact
    ObservationDiscipline.OperationalDomain.capabilityGenerated_least
      (route.pullbackObservation targetDiscipline)
      (route.pullbackChronological targetDiscipline chronological)
      (route.pullbackIndependentParallel targetDiscipline parallel)
      Independent closed member

/-- Exact universal characterization of the represented route's pulled
observation domain.  Membership can be used without inspecting a capability
construction tree: it is membership in every domain closed under precisely
the transported capabilities and the same authorization family. -/
theorem pullbackCapabilityDomain_contains_iff_forall_closed
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection)
    (parallel : IndependentParallelCapability targetDiscipline.collection)
    (Independent : targetDiscipline.collection.Container →
      targetDiscipline.collection.Container → Type uAuthority)
    (container : targetDiscipline.collection.Container) :
    (route.pullbackCapabilityDomain targetDiscipline chronological parallel
      Independent).contains container ↔
      ∀ closed : ObservationDiscipline.OperationalDomain.CapabilityClosed
        (route.pullbackChronological targetDiscipline chronological)
        (route.pullbackIndependentParallel targetDiscipline parallel)
        Independent,
        closed.contains container := by
  exact
    ObservationDiscipline.OperationalDomain.capabilityGenerated_contains_iff_forall_closed
      (route.pullbackObservation targetDiscipline)
      (route.pullbackChronological targetDiscipline chronological)
      (route.pullbackIndependentParallel targetDiscipline parallel)
      Independent container

/-- Every source construction in the pulled domain realizes as a target
construction with the same retained container and independence evidence. -/
theorem pullbackCapabilityDomain_mapsToTarget
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection)
    (parallel : IndependentParallelCapability targetDiscipline.collection)
    (Independent : targetDiscipline.collection.Container →
      targetDiscipline.collection.Container → Type uAuthority)
    {container : targetDiscipline.collection.Container}
    (member :
      (route.pullbackCapabilityDomain targetDiscipline chronological parallel
        Independent).contains container) :
    (ObservationDiscipline.OperationalDomain.capabilityGenerated
      targetDiscipline chronological parallel Independent).contains container := by
  exact ObservationDiscipline.OperationalDomain.capabilityGenerated_pullback_subset
    (mapEvent route.toOperationalTranslation) targetDiscipline chronological
      parallel Independent member

/-- A policy supported by the target capability domain remains supported on
the represented source route's pulled domain.  This is restriction along the
realized domain, not a claim that the readout is globally faithful. -/
theorem supportsPolicy_pullbackCapabilityDomain
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection)
    (parallel : IndependentParallelCapability targetDiscipline.collection)
    (Independent : targetDiscipline.collection.Container →
      targetDiscipline.collection.Container → Type uAuthority)
    (policy : targetDiscipline.collection.Container → Decision)
    (supported :
      (ObservationDiscipline.OperationalDomain.capabilityGenerated
        targetDiscipline chronological parallel Independent).SupportsPolicy
          policy) :
    (route.pullbackCapabilityDomain targetDiscipline chronological parallel
      Independent).SupportsPolicy policy := by
  obtain ⟨observedPolicy, agrees⟩ := supported
  refine ⟨observedPolicy, ?_⟩
  intro container sourceMember
  exact agrees (route.pullbackCapabilityDomain_mapsToTarget targetDiscipline
    chronological parallel Independent sourceMember)

/-- Maximum-score scheduler sufficiency is likewise stable under represented
route pullback. -/
theorem supportsMaxSelection_pullbackCapabilityDomain
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (chronological : ChronologicalCapability targetDiscipline.collection)
    (parallel : IndependentParallelCapability targetDiscipline.collection)
    (Independent : targetDiscipline.collection.Container →
      targetDiscipline.collection.Container → Type uAuthority)
    (score : targetDiscipline.collection.Container → Nat)
    (supported :
      (ObservationDiscipline.OperationalDomain.capabilityGenerated
        targetDiscipline chronological parallel Independent).SupportsMaxSelection
          score) :
    (route.pullbackCapabilityDomain targetDiscipline chronological parallel
      Independent).SupportsMaxSelection score := by
  rw [ObservationDiscipline.OperationalDomain.supportsMaxSelection_iff_constantOnReadoutFibers]
    at supported ⊢
  intro first second firstMember secondMember sameReadout
  exact supported
    (route.pullbackCapabilityDomain_mapsToTarget targetDiscipline chronological
      parallel Independent firstMember)
    (route.pullbackCapabilityDomain_mapsToTarget targetDiscipline chronological
      parallel Independent secondMember)
    sameReadout

/-! ## Positive and refusing controls -/

namespace CapabilityCanary

open Mettapedia.Algebra

abbrev system : GSLT := GSLT.discrete Bool

def route : RepresentedOperationalRoute system system :=
  RepresentedOperationalRoute.id system

def discipline : GSLTObservation system :=
  WorkSpanObservation.discipline (fun _ => ⟨1, 1⟩)

def chronological : ChronologicalCapability discipline.collection :=
  WorkSpanObservation.chronological (fun _ => ⟨1, 1⟩)

def parallel : IndependentParallelCapability discipline.collection :=
  WorkSpanObservation.independentParallel (fun _ => ⟨1, 1⟩)

def permitAll (_ _ : WorkSpan) : Type := Unit
def refuseAll (_ _ : WorkSpan) : Type := Empty

/-- The empty source history is a genuine member of the pulled operational
domain. -/
def sourceEmptyMember :
    (route.pullbackCapabilityDomain discipline chronological parallel permitAll
      ).contains (0 : WorkSpan) :=
  ⟨.history [] rfl⟩

/-- That source construction realizes in the target capability domain. -/
theorem source_empty_maps_to_target :
    (ObservationDiscipline.OperationalDomain.capabilityGenerated discipline
      chronological parallel permitAll).contains (0 : WorkSpan) :=
  route.pullbackCapabilityDomain_mapsToTarget discipline chronological parallel
    permitAll sourceEmptyMember

/-- Even an identity represented route cannot manufacture an independence
authorization that the declared family refuses. -/
theorem represented_route_does_not_mint_independence :
    IsEmpty
      (WitnessCollector.IndependentCombination
        (route.pullbackObservation discipline).collection
        (route.pullbackIndependentParallel discipline parallel)
        refuseAll (0 : WorkSpan) (0 : WorkSpan) (0 : WorkSpan)) :=
  ⟨fun combination => Empty.elim combination.authorization⟩

/-! A domain-level refusal control.  This uses a Boolean observer whose raw
histories and chronological composites always produce `false`; only an
authorized independent-parallel composition could produce `true`. -/

namespace RefusalDomain

open Mettapedia.GSLT.Dynamics.CapabilityGeneratedUniversalCanary

def eventMap (_ : system.LabeledStep) : Unit := ()

def discipline : GSLTObservation system :=
  ObservationTransport.ObservationDiscipline.pullback eventMap
    CapabilityGeneratedUniversalCanary.discipline

def chronological : ChronologicalCapability discipline.collection :=
  ObservationTransport.WitnessCollector.pullbackChronological eventMap
    CapabilityGeneratedUniversalCanary.discipline.collection
    CapabilityGeneratedUniversalCanary.chronological

def parallel : IndependentParallelCapability discipline.collection :=
  ObservationTransport.WitnessCollector.pullbackIndependentParallel eventMap
    CapabilityGeneratedUniversalCanary.discipline.collection
    CapabilityGeneratedUniversalCanary.parallel

/-- A represented route cannot recover a parallel-only observation through a
different construction tree after every independence article is refused. -/
theorem represented_route_refusal_does_not_generate_true :
    ¬ (route.pullbackCapabilityDomain discipline chronological parallel
      CapabilityGeneratedUniversalCanary.refuseAll).contains true := by
  intro sourceMember
  have targetMember :=
    route.pullbackCapabilityDomain_mapsToTarget discipline chronological
      parallel CapabilityGeneratedUniversalCanary.refuseAll sourceMember
  have universalMember :=
    ObservationDiscipline.OperationalDomain.capabilityGenerated_pullback_subset
      eventMap CapabilityGeneratedUniversalCanary.discipline
      CapabilityGeneratedUniversalCanary.chronological
      CapabilityGeneratedUniversalCanary.parallel
      CapabilityGeneratedUniversalCanary.refuseAll targetMember
  exact
    CapabilityGeneratedUniversalCanary.refusal_does_not_generate_true
      universalMember

end RefusalDomain

end CapabilityCanary

#print axioms pullbackCapabilityDomain_mapsToTarget
#print axioms supportsPolicy_pullbackCapabilityDomain
#print axioms supportsMaxSelection_pullbackCapabilityDomain
#print axioms CapabilityCanary.source_empty_maps_to_target
#print axioms CapabilityCanary.represented_route_does_not_mint_independence
#print axioms pullbackCapabilityDomain_least
#print axioms pullbackCapabilityDomain_contains_iff_forall_closed
#print axioms CapabilityCanary.RefusalDomain.represented_route_refusal_does_not_generate_true

end RepresentedOperationalRoute
end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
