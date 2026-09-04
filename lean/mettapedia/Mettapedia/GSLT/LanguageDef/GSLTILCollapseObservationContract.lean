import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.GSLT.LanguageDef.GSLTILObservationControlContract

/-!
# Collapse contracts along represented GSLT-IL routes

A language presentation contributes only a map from its labeled execution
events to the observations consumed by a collapse algebra.  Pulling a contract
back along a represented operational route composes that map with the route's
event translation.  The collapse algebra, completion demand, and control
authorities are unchanged.

Consequently an evaluator presentation may be replaced while the same
observer implementation and proofs remain valid.  This is the formal seam
between a language-specific syntax or abstract machine and a generic direct
fold over observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.GSLT.Dynamics.CollapseObservationContract
open Mettapedia.GSLT.Dynamics.ObservationTransport

universe uTerm uGuard

namespace RepresentedOperationalRoute

/-- The observation projection induced on source events by a represented
operational route. -/
def pullbackCollapseProject {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O : Type} (project : target.LabeledStep → O) :
    source.LabeledStep → O :=
  project ∘ mapEvent route.toOperationalTranslation

@[simp] theorem pullbackCollapseProject_apply
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O : Type} (project : target.LabeledStep → O)
    (event : source.LabeledStep) :
    route.pullbackCollapseProject project event =
      project (mapEvent route.toOperationalTranslation event) :=
  rfl

/-- Contract transport preserves the completion request exactly. -/
theorem pullback_collapse_contract_demand
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O R Result : Type} {Guard : Type uGuard}
    (project : target.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (demand : ObservationDemand Guard) :
    (route.pullbackContract
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        project algebra demand)
      ).demand = demand :=
  rfl

/-- **Presentation naturality.**  Observing the translated target history is
the same as collapsing source events through the composed projection. -/
theorem pullback_collapse_contract_observe
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O R Result : Type} {Guard : Type uGuard}
    (project : target.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (demand : ObservationDemand Guard)
    (events : List source.LabeledStep) :
    (route.pullbackContract
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        project algebra demand)
      ).observer.observe events =
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        (route.pullbackCollapseProject project) algebra demand
      ).observer.observe events := by
  simp only [pullbackContract_observe,
    Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract_observe,
    pullbackCollapseProject, List.map_map]

/-- Pulling through two represented routes composes the observation
projection in the same order as the routes. -/
theorem pullbackCollapseProject_comp
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    {O : Type} (project : last.LabeledStep → O)
    (event : first.LabeledStep) :
    (comp earlier later).pullbackCollapseProject project event =
      earlier.pullbackCollapseProject
        (later.pullbackCollapseProject project) event := by
  simp only [pullbackCollapseProject_apply, toOperationalTranslation_comp,
    mapEvent_comp]

/-! ## Presentation-independent direct folds -/

/-- An event history is a semantic producer for any event projection. -/
def historyProducer {system : GSLT.{uTerm}} {O : Type}
    (project : system.LabeledStep → O) :
    Producer (List system.LabeledStep) O where
  materialize events := events.map project

/-- A represented operational route presents source histories as target
histories at exactly the selected observation.  Neither evaluator state nor
its stepping representation appears in this interface. -/
def historyPresentation {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O : Type} (project : target.LabeledStep → O) :
    Producer.Presentation
      (historyProducer project)
      (historyProducer (route.pullbackCollapseProject project)) where
  denote events := events.map
    (mapEvent route.toOperationalTranslation)
  exact events := by
    simp [historyProducer, pullbackCollapseProject, List.map_map]

/-- Install a source-native implementation of a target fold.  The semantic
route is used only by the agreement proof; `run` can be a BN machine, CBPV
machine, trie cursor, or another physical realization. -/
def presentDirectFold
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O R Result : Type}
    (project : target.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (fold : DirectFold (historyProducer project) algebra)
    (run : List source.LabeledStep → Result)
    (agrees : ∀ events, run events =
      fold.run (events.map
        (mapEvent route.toOperationalTranslation))) :
    DirectFold
      (historyProducer (route.pullbackCollapseProject project)) algebra :=
  fold.present (route.historyPresentation project) {
    run := run
    agrees := agrees
  }

@[simp] theorem presentDirectFold_run
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O R Result : Type}
    (project : target.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (fold : DirectFold (historyProducer project) algebra)
    (run : List source.LabeledStep → Result)
    (agrees : ∀ events, run events =
      fold.run (events.map
        (mapEvent route.toOperationalTranslation)))
    (events : List source.LabeledStep) :
    (route.presentDirectFold project algebra fold run agrees).run events =
      run events :=
  rfl

/-- A proved target-history fold is reusable on source histories by applying
the represented event translation. -/
def pullbackDirectFold
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O R Result : Type}
    (project : target.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (fold : DirectFold (historyProducer project) algebra) :
    DirectFold
      (historyProducer (route.pullbackCollapseProject project)) algebra :=
  route.presentDirectFold project algebra fold
    (fun events => fold.run
      (events.map (mapEvent route.toOperationalTranslation)))
    (fun _ => rfl)

@[simp] theorem pullbackDirectFold_run
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {O R Result : Type}
    (project : target.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (fold : DirectFold (historyProducer project) algebra)
    (events : List source.LabeledStep) :
    (route.pullbackDirectFold project algebra fold).run events =
      fold.run (events.map (mapEvent route.toOperationalTranslation)) :=
  rfl

/-- A producer-side exclusion certificate transports with the represented
operational route.  Thus provenance admission is a property of the semantic
events, not of the source evaluator's machine representation. -/
theorem pullbackHistoryExcludesFallback
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Answer Receipt : Type}
    (project : target.LabeledStep → Obs Answer Receipt)
    (isFallback : Answer → Bool)
    (excludes :
      Producer.ExcludesFallback (historyProducer project) isFallback) :
    Producer.ExcludesFallback
      (historyProducer (route.pullbackCollapseProject project))
      isFallback := by
  intro events observation member
  apply excludes
    (events.map (mapEvent route.toOperationalTranslation)) observation
  simpa only [historyProducer,
    pullbackCollapseProject, List.map_map] using member

/-- A certified direct counter survives an evaluator-presentation change and
still implements the preferred/fallback observer.  The new presentation may
be a different abstract machine; it supplies only the represented route. -/
def pullbackCertifiedPreferredCount
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Answer Receipt : Type}
    (project : target.LabeledStep → Obs Answer Receipt)
    (isFallback : Answer → Bool)
    (fold : DirectFold
      (historyProducer project) (CountAlg Answer Receipt))
    (excludes :
      Producer.ExcludesFallback (historyProducer project) isFallback) :
    DirectFold
      (historyProducer (route.pullbackCollapseProject project))
      (PreferCountAlg isFallback) :=
  DirectFold.preferCountOfExcludesFallback isFallback
    (route.pullbackDirectFold project (CountAlg Answer Receipt) fold)
    (route.pullbackHistoryExcludesFallback project isFallback excludes)

/-- Pulling a direct fold through two represented routes is coherent with
pulling first through the later route and then through the earlier route. -/
theorem pullbackDirectFold_comp_run
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    {O R Result : Type}
    (project : last.LabeledStep → O)
    (algebra : CollapseAlgebra O R Result)
    (fold : DirectFold (historyProducer project) algebra)
    (events : List first.LabeledStep) :
    ((comp earlier later).pullbackDirectFold project algebra fold).run events =
      (earlier.pullbackDirectFold
        (later.pullbackCollapseProject project) algebra
        (later.pullbackDirectFold project algebra fold)).run events := by
  change fold.run
      (events.map (mapEvent (comp earlier later).toOperationalTranslation)) =
    fold.run
      ((events.map (mapEvent earlier.toOperationalTranslation)).map
        (mapEvent later.toOperationalTranslation))
  rw [toOperationalTranslation_comp, List.map_map]
  congr 2

/-! ## Canaries -/

namespace Canary

abbrev boolSystem : GSLT := GSLT.discrete Bool

def boolObservation (event : boolSystem.LabeledStep) : Obs Bool Unit :=
  ⟨event.source, 1, ()⟩

def anyDemand : ObservationDemand Unit := { completion := .first }

/-- Identity presentation leaves both the fold result and completion demand
unchanged. -/
theorem identity_presentation_is_exact
    (events : List boolSystem.LabeledStep) :
    (((RepresentedOperationalRoute.id boolSystem).pullbackContract
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        boolObservation
        (AnyAlg Bool Unit) anyDemand)).observer.observe events =
      collapseWith (AnyAlg Bool Unit) (events.map boolObservation)) ∧
    (((RepresentedOperationalRoute.id boolSystem).pullbackContract
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        boolObservation
        (AnyAlg Bool Unit) anyDemand)).demand.completion = .first) := by
  constructor
  · rw [pullback_collapse_contract_observe]
    change collapseWith (AnyAlg Bool Unit)
        (events.map (boolObservation ∘ mapEvent
          (RepresentedOperationalRoute.id boolSystem).toOperationalTranslation)) =
      collapseWith (AnyAlg Bool Unit) (events.map boolObservation)
    rw [toOperationalTranslation_id]
    rfl
  · rfl

/-- A represented route cannot reinterpret an ordered collection request as
an existence request. -/
theorem identity_does_not_change_ordered_demand :
    (((RepresentedOperationalRoute.id boolSystem).pullbackContract
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        boolObservation
        (Collect Bool Unit)
        ({ completion := .orderedStream } : ObservationDemand Unit))
      ).demand.completion = .orderedStream) ∧
    (((RepresentedOperationalRoute.id boolSystem).pullbackContract
      (Mettapedia.GSLT.Dynamics.CollapseObservationContract.contract
        boolObservation
        (Collect Bool Unit)
        ({ completion := .orderedStream } : ObservationDemand Unit))
      ).demand.completion ≠ .first) := by
  decide

end Canary

/-! ## Axiom audit -/

#print axioms pullback_collapse_contract_demand
#print axioms pullback_collapse_contract_observe
#print axioms pullbackCollapseProject_comp
#print axioms historyPresentation
#print axioms presentDirectFold
#print axioms pullbackDirectFold
#print axioms pullbackHistoryExcludesFallback
#print axioms pullbackCertifiedPreferredCount
#print axioms pullbackDirectFold_comp_run
#print axioms Canary.identity_presentation_is_exact
#print axioms Canary.identity_does_not_change_ordered_demand

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
