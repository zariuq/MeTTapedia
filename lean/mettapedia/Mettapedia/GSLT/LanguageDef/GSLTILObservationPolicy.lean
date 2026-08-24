import Mettapedia.GSLT.LanguageDef.GSLTILObservationTransport
import Mettapedia.GSLT.Dynamics.ObservationPolicyFactorization

/-!
# General observation-policy transport for represented GSLT-IL routes

Observation pullback along a represented operational route retains the target
witness container and readout.  It therefore preserves and reflects support
for every downstream policy on that container, not only scheduler maxima.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics

universe uTerm uDecision

namespace RepresentedOperationalRoute

/-- General policy support is invariant under observation pullback. -/
theorem pullbackObservation_supportsPolicy_iff
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (policy : targetDiscipline.collection.Container -> Decision) :
    (route.pullbackObservation targetDiscipline).SupportsPolicy policy ↔
      targetDiscipline.SupportsPolicy policy :=
  Iff.rfl

/-- A supported target policy remains supported at the source. -/
theorem pullbackObservation_supportsPolicy
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (policy : targetDiscipline.collection.Container -> Decision)
    (supported : targetDiscipline.SupportsPolicy policy) :
    (route.pullbackObservation targetDiscipline).SupportsPolicy policy :=
  (route.pullbackObservation_supportsPolicy_iff
    targetDiscipline policy).2 supported

/-- Pullback cannot manufacture policy support absent at the target. -/
theorem pullbackObservation_not_supportsPolicy
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (policy : targetDiscipline.collection.Container -> Decision)
    (unsupported : ¬ targetDiscipline.SupportsPolicy policy) :
    ¬ (route.pullbackObservation targetDiscipline).SupportsPolicy policy :=
  fun sourceSupport => unsupported
    ((route.pullbackObservation_supportsPolicy_iff
      targetDiscipline policy).1 sourceSupport)

/-- Policy-support transport is coherent with represented-route
composition. -/
theorem pullbackObservation_comp_supportsPolicy_iff
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    (discipline : GSLTObservation last)
    (policy : discipline.collection.Container -> Decision) :
    ((comp earlier later).pullbackObservation discipline
      ).SupportsPolicy policy ↔
      (earlier.pullbackObservation
        (later.pullbackObservation discipline)).SupportsPolicy policy :=
  Iff.rfl

#print axioms pullbackObservation_supportsPolicy_iff
#print axioms pullbackObservation_supportsPolicy
#print axioms pullbackObservation_not_supportsPolicy
#print axioms pullbackObservation_comp_supportsPolicy_iff

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
