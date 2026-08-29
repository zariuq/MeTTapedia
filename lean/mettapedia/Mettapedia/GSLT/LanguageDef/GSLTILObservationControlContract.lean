import Mettapedia.GSLT.Dynamics.ObservationControlDiscipline
import Mettapedia.GSLT.LanguageDef.GSLTILObservationTransport

/-!
# Observation-control contracts along represented GSLT-IL routes

A represented operational route maps proof-relevant source steps to target
steps.  It therefore pulls a target observation-control contract back to the
source.  The observer acts on the mapped occurrence history, while completion
demand and semantic guard remain unchanged.

This is the morphism action for contracts.  It preserves composition and
postcomposition of observer views and agrees with the established pullback of
GSLT observation disciplines.  No route receives serializability, filtering,
pruning, or stopping authority merely by being represented.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObservationControlDiscipline
open Mettapedia.GSLT.Dynamics.ObservationTransport

universe uTerm uGuard uView uOtherView

variable {OtherView : Type uOtherView}

namespace RepresentedOperationalRoute

/-- Pull an observer on target occurrence histories back to source occurrence
histories. -/
def pullbackObserver {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {View : Type uView}
    (observer : Observer (List target.LabeledStep) View) :
    Observer (List source.LabeledStep) View where
  observe := fun events =>
    observer.observe
      (events.map (mapEvent route.toOperationalTranslation))

@[simp] theorem pullbackObserver_observe
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {View : Type uView}
    (observer : Observer (List target.LabeledStep) View)
    (events : List source.LabeledStep) :
    (route.pullbackObserver observer).observe events =
      observer.observe
        (events.map (mapEvent route.toOperationalTranslation)) :=
  rfl

/-- Contravariant action of a represented route on an observation-control
contract. -/
def pullbackContract {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract target Guard View) :
    GSLTContract source Guard View where
  observer := route.pullbackObserver contract.observer
  demand := contract.demand

@[simp] theorem pullbackContract_demand
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract target Guard View) :
    (route.pullbackContract contract).demand = contract.demand :=
  rfl

@[simp] theorem pullbackContract_observe
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract target Guard View)
    (events : List source.LabeledStep) :
    (route.pullbackContract contract).observer.observe events =
      contract.observer.observe
        (events.map (mapEvent route.toOperationalTranslation)) :=
  rfl

/-- Contract pullback agrees pointwise with the established observation-
discipline pullback. -/
theorem ofGSLTContract_pullback_observe
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract target Guard View)
    (events : List source.LabeledStep) :
    (ofGSLTContract (route.pullbackContract contract)).observe events =
      (route.pullbackObservation
        (ofGSLTContract contract)).observe events :=
  rfl

/-- Pullback commutes with forgetting an observation coordinate. -/
theorem pullbackContract_postcompose
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract target Guard View)
    (summarize : View -> OtherView) :
    route.pullbackContract (contract.postcompose summarize) =
      (route.pullbackContract contract).postcompose summarize :=
  rfl

/-- Pullback commutes with adding an observation axis.  Both source axes see
the same mapped target history. -/
theorem pullbackContract_addAxis
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract target Guard View)
    (axis : Observer (List target.LabeledStep) OtherView) :
    route.pullbackContract (contract.addAxis axis) =
      (route.pullbackContract contract).addAxis
        (route.pullbackObserver axis) :=
  rfl

/-- Identity route pullback changes neither observation nor demand. -/
theorem pullbackContract_id_observe
    {system : GSLT.{uTerm}} {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract system Guard View)
    (events : List system.LabeledStep) :
    ((RepresentedOperationalRoute.id system).pullbackContract contract
      ).observer.observe events = contract.observer.observe events := by
  change contract.observer.observe
      (events.map
        (mapEvent
          (RepresentedOperationalRoute.id system).toOperationalTranslation)) =
    contract.observer.observe events
  rw [toOperationalTranslation_id]
  apply congrArg contract.observer.observe
  induction events with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.map_cons, mapEvent_id, inductionHypothesis]

/-- Pullback respects composition of represented routes at the exact
observer boundary. -/
theorem pullbackContract_comp_observe
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    {Guard : Type uGuard} {View : Type uView}
    (contract : GSLTContract last Guard View)
    (events : List first.LabeledStep) :
    ((comp earlier later).pullbackContract contract).observer.observe events =
      (earlier.pullbackContract
        (later.pullbackContract contract)).observer.observe events := by
  change contract.observer.observe
      (events.map (mapEvent (comp earlier later).toOperationalTranslation)) =
    contract.observer.observe
      ((events.map (mapEvent earlier.toOperationalTranslation)).map
        (mapEvent later.toOperationalTranslation))
  rw [toOperationalTranslation_comp, List.map_map]
  congr 2

/-! ## A non-authority canary -/

namespace Canary

abbrev contractSystem : GSLT := GSLT.discrete Bool

def emptyStreamContract :
    GSLTContract contractSystem Unit (List contractSystem.LabeledStep) where
  observer := Observer.identity (List contractSystem.LabeledStep)
  demand := { completion := .orderedStream }

/-- Even identity transport preserves the ordered-stream demand; it does not
silently reinterpret it as a complete bag. -/
theorem identity_does_not_mint_completeBag :
    ((RepresentedOperationalRoute.id contractSystem).pullbackContract
      emptyStreamContract).demand.completion = .orderedStream /\
    ((RepresentedOperationalRoute.id contractSystem).pullbackContract
      emptyStreamContract).demand.completion ≠ .completeBag := by
  decide

end Canary

#print axioms pullbackContract_demand
#print axioms ofGSLTContract_pullback_observe
#print axioms pullbackContract_postcompose
#print axioms pullbackContract_addAxis
#print axioms pullbackContract_id_observe
#print axioms pullbackContract_comp_observe
#print axioms Canary.identity_does_not_mint_completeBag

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
