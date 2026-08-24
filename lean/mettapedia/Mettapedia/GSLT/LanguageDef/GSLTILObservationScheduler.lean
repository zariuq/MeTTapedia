import Mettapedia.GSLT.LanguageDef.GSLTILObservationPolicy
import Mettapedia.GSLT.Dynamics.ObservationSchedulerSufficiency

/-!
# Scheduler sufficiency along represented GSLT-IL routes

A represented operational GSLT-IL route transports complete execution paths
and pulls target observation disciplines back to its source.  Because this
pullback retains the witness container and value readout exactly, it also
preserves and reflects the information criterion for maximum-selection
policies.

This result grants no new route representation, execution independence, or
scheduler policy.  It only says that an already declared policy can use the
pulled-back readout exactly when it could use the target readout.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics

universe uTerm

namespace RepresentedOperationalRoute

/-- **Exact transport law for scheduler sufficiency.**  Pullback along a
represented route preserves and reflects maximum-selection sufficiency,
because it changes the event history but retains the observation container
and readout. -/
theorem pullbackObservation_supportsMaxSelection_iff
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (score : targetDiscipline.collection.Container -> Nat) :
    (route.pullbackObservation targetDiscipline).SupportsMaxSelection score ↔
      targetDiscipline.SupportsMaxSelection score :=
  Iff.rfl

/-- A policy supported by the target observation remains supported after
pullback to the source. -/
theorem pullbackObservation_supportsMaxSelection
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (score : targetDiscipline.collection.Container -> Nat)
    (supported : targetDiscipline.SupportsMaxSelection score) :
    (route.pullbackObservation targetDiscipline).SupportsMaxSelection score :=
  (route.pullbackObservation_supportsMaxSelection_iff
    targetDiscipline score).2 supported

/-- Conversely, route transport cannot make an insufficient observation
sufficient. -/
theorem pullbackObservation_reflectsMaxSelectionSupport
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (score : targetDiscipline.collection.Container -> Nat)
    (supported :
      (route.pullbackObservation targetDiscipline).SupportsMaxSelection score) :
    targetDiscipline.SupportsMaxSelection score :=
  (route.pullbackObservation_supportsMaxSelection_iff
    targetDiscipline score).1 supported

/-- Insufficiency is therefore stable under pullback as well. -/
theorem pullbackObservation_not_supportsMaxSelection
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    (score : targetDiscipline.collection.Container -> Nat)
    (unsupported : ¬ targetDiscipline.SupportsMaxSelection score) :
    ¬ (route.pullbackObservation targetDiscipline).SupportsMaxSelection score :=
  fun sourceSupport =>
    unsupported (route.pullbackObservation_reflectsMaxSelectionSupport
      targetDiscipline score sourceSupport)

/-- Scheduler-sufficiency transport is coherent with composition of
represented routes.  The theorem concerns the earned functional transport;
the loose relational route still retains its intermediate witness. -/
theorem pullbackObservation_comp_supportsMaxSelection_iff
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    (discipline : GSLTObservation last)
    (score : discipline.collection.Container -> Nat) :
    ((comp earlier later).pullbackObservation discipline
      ).SupportsMaxSelection score ↔
      (earlier.pullbackObservation
        (later.pullbackObservation discipline)).SupportsMaxSelection score :=
  Iff.rfl

/-! ## Positive and negative controls -/

namespace Canary

def unitCost : system.LabeledStep -> WorkSpan :=
  fun _ => ⟨1, 1⟩

def workOnly : GSLTObservation system :=
  WorkSpanObservation.workOnly unitCost

/-- A represented identity route preserves the fact that the work-only
readout supports work selection. -/
theorem identity_workOnly_supports_workSelection :
    (identityRoute.pullbackObservation workOnly
      ).SupportsMaxSelection WorkSpan.work := by
  apply identityRoute.pullbackObservation_supportsMaxSelection workOnly
  rw [ObservationDiscipline.supportsMaxSelection_iff]
  intro first second sameReadout
  exact sameReadout

/-- A represented route cannot upgrade work-only observation into a
span-sufficient observation. -/
theorem identity_workOnly_not_supports_spanSelection :
    ¬ (identityRoute.pullbackObservation workOnly
      ).SupportsMaxSelection WorkSpan.span := by
  apply identityRoute.pullbackObservation_not_supportsMaxSelection workOnly
  apply ObservationDiscipline.not_supportsMaxSelection_of_collision workOnly
      WorkSpan.span (first := (⟨2, 1⟩ : WorkSpan)) (second := ⟨2, 2⟩)
  · rfl
  · norm_num

end Canary

#print axioms pullbackObservation_supportsMaxSelection_iff
#print axioms pullbackObservation_supportsMaxSelection
#print axioms pullbackObservation_reflectsMaxSelectionSupport
#print axioms pullbackObservation_not_supportsMaxSelection
#print axioms pullbackObservation_comp_supportsMaxSelection_iff
#print axioms Canary.identity_workOnly_supports_workSelection
#print axioms Canary.identity_workOnly_not_supports_spanSelection

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
