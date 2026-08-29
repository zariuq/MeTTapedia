import Mettapedia.GSLT.Dynamics.ObserverRelativeControlFactorization
import Mettapedia.GSLT.LanguageDef.GSLTILObservationControlContract

/-!
# Observer-relative control along represented GSLT-IL routes

A represented operational route already transports proof-relevant execution
paths and pulls target observation disciplines back to the source.  This
module transports the remaining control boundary without adding authority:

* target occurrence identity is reindexed along the mapped source event;
* the target client contract is pulled back to mapped event histories;
* the scheduler reads the same semantic value as before.

The action is contravariant on observers and occurrence names.  Exact source
occurrence identity is available only when the route's event action is
injective; a many-to-one compiler map cannot acquire reflection merely because
the target index is exact.  Completion demand, semantic value, and scheduler
readout are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObservationTransport

universe uTerm uIdentity uGuard uView uScore uReceipt

namespace RepresentedOperationalRoute

/-- Reindex a target occurrence name along the represented route's event
action. -/
def pullbackOccurrenceIndex {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Identity : Type uIdentity}
    (index : OccurrenceIndex target.LabeledStep Identity) :
    OccurrenceIndex source.LabeledStep Identity :=
  index.pullback (mapEvent route.toOperationalTranslation)

@[simp] theorem pullbackOccurrenceIndex_identify
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Identity : Type uIdentity}
    (index : OccurrenceIndex target.LabeledStep Identity)
    (event : source.LabeledStep) :
    (route.pullbackOccurrenceIndex index).identify event =
      index.identify (mapEvent route.toOperationalTranslation event) :=
  rfl

/-- Target exactness pulls back exactly when the represented event action is
injective.  Representability and one-way step preservation alone do not imply
this reflection property. -/
theorem pullbackOccurrenceIndex_exact_iff
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Identity : Type uIdentity}
    (index : OccurrenceIndex target.LabeledStep Identity)
    (exact : index.Exact) :
    (route.pullbackOccurrenceIndex index).Exact ↔
      Function.Injective (mapEvent route.toOperationalTranslation) :=
  index.pullback_exact_iff _ exact

/-- Pull the complete observer-relative control boundary back along a
represented route.  The source architecture is the canonical architecture of
collected source paths for the pulled-back observation discipline. -/
def pullbackControl {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score) :
    ObserverRelativeControlFactorization
      (route.pullbackCollectedArchitecture targetDiscipline)
      Identity Guard View Score where
  occurrence := route.pullbackOccurrenceIndex control.occurrence
  contract := route.pullbackContract control.contract
  schedule := { readout := control.schedule.readout }

@[simp] theorem pullbackControl_demand
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score) :
    (route.pullbackControl targetDiscipline control).contract.demand =
      control.contract.demand :=
  rfl

@[simp] theorem pullbackControl_occurrence_identify
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    (event : source.LabeledStep) :
    (route.pullbackControl targetDiscipline control).occurrence.identify event =
      control.occurrence.identify
        (mapEvent route.toOperationalTranslation event) :=
  rfl

@[simp] theorem pullbackControl_observe
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    (events : List source.LabeledStep) :
    (route.pullbackControl targetDiscipline control).contract.observer.observe
        events =
      control.contract.observer.observe
        (events.map (mapEvent route.toOperationalTranslation)) :=
  rfl

@[simp] theorem pullbackControl_schedule_readout
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    (value : targetDiscipline.Value) :
    (route.pullbackControl targetDiscipline control).schedule.readout value =
      control.schedule.readout value :=
  rfl

/-- Map a concrete source change to the target event type.  This is only a
change of event representation; observer-relative admission remains a
separate proposition. -/
def mapEventChange {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Receipt : Type uReceipt}
    (change : Change source.LabeledStep Receipt) :
    Change target.LabeledStep Receipt where
  source := change.source.map (mapEvent route.toOperationalTranslation)
  target := change.target.map (mapEvent route.toOperationalTranslation)
  receipt := change.receipt

/-- Map a source pruning ledger to target events.  Accounting is preserved by
the additive action of `Multiset.map`; this does not claim that a noninjective
event translation reflects individual source identities. -/
def mapEventPruning {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Receipt : Type uReceipt}
    (pruning : PruningChange source.LabeledStep Receipt) :
    PruningChange target.LabeledStep Receipt where
  source := pruning.source.map (mapEvent route.toOperationalTranslation)
  target := pruning.target.map (mapEvent route.toOperationalTranslation)
  receipt := pruning.receipt
  removed := pruning.removed.map (mapEvent route.toOperationalTranslation)
  accounting := by
    simpa using congrArg
      (Multiset.map (mapEvent route.toOperationalTranslation))
      pruning.accounting

@[simp] theorem mapEventPruning_removed
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    {Receipt : Type uReceipt}
    (pruning : PruningChange source.LabeledStep Receipt) :
    (route.mapEventPruning pruning).removed =
      pruning.removed.map (mapEvent route.toOperationalTranslation) :=
  rfl

/-- Source preservation at the pulled-back observer is exactly target
preservation of the mapped occurrence change. -/
theorem pullbackControl_preserves_iff
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (change : Change source.LabeledStep Receipt) :
    (route.pullbackControl targetDiscipline control).contract.Preserves change ↔
      control.contract.Preserves (route.mapEventChange change) :=
  Iff.rfl

/-- An observer-admitted source prune maps to an observer-admitted target
prune with the mapped removed-occurrence ledger.  Route transport consumes
the existing source admission; it does not mint pruning authority. -/
def mapAdmittedPruning
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (pruning :
      (route.pullbackControl targetDiscipline control).AdmittedPruning Receipt) :
    control.AdmittedPruning Receipt where
  val := route.mapEventPruning pruning.1
  property := by
    change control.contract.Preserves
      (route.mapEventChange pruning.1.toChange)
    exact
      (route.pullbackControl_preserves_iff targetDiscipline control
        pruning.1.toChange).1 pruning.2

@[simp] theorem mapAdmittedPruning_removed
    {source target : GSLT.{uTerm}}
    (route : RepresentedOperationalRoute source target)
    (targetDiscipline : GSLTObservation target)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (route.targetCollectedArchitecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (pruning :
      (route.pullbackControl targetDiscipline control).AdmittedPruning Receipt) :
    (route.mapAdmittedPruning targetDiscipline control pruning).1.removed =
      pruning.1.removed.map (mapEvent route.toOperationalTranslation) :=
  rfl

/-- Identity-route pullback leaves occurrence identity pointwise unchanged. -/
theorem pullbackControl_id_occurrence
    {system : GSLT.{uTerm}}
    (discipline : GSLTObservation system)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      ((RepresentedOperationalRoute.id system).targetCollectedArchitecture
        discipline) Identity Guard View Score)
    (event : system.LabeledStep) :
    ((RepresentedOperationalRoute.id system).pullbackControl discipline control
      ).occurrence.identify event = control.occurrence.identify event := by
  simp only [pullbackControl_occurrence_identify, toOperationalTranslation_id,
    mapEvent_id]

/-- Occurrence reindexing respects route composition pointwise. -/
theorem pullbackControl_comp_occurrence
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    (discipline : GSLTObservation last)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (later.targetCollectedArchitecture discipline)
      Identity Guard View Score)
    (event : first.LabeledStep) :
    ((comp earlier later).pullbackControl discipline control
      ).occurrence.identify event =
      (earlier.pullbackControl (later.pullbackObservation discipline)
        (later.pullbackControl discipline control)).occurrence.identify event := by
  simp only [pullbackControl_occurrence_identify,
    toOperationalTranslation_comp, mapEvent_comp]

/-- Client observation pullback respects composition at the same boundary. -/
theorem pullbackControl_comp_observe
    {first middle last : GSLT.{uTerm}}
    (earlier : RepresentedOperationalRoute first middle)
    (later : RepresentedOperationalRoute middle last)
    (discipline : GSLTObservation last)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (later.targetCollectedArchitecture discipline)
      Identity Guard View Score)
    (events : List first.LabeledStep) :
    ((comp earlier later).pullbackControl discipline control
      ).contract.observer.observe events =
      (earlier.pullbackControl (later.pullbackObservation discipline)
        (later.pullbackControl discipline control)).contract.observer.observe
          events :=
  pullbackContract_comp_observe earlier later control.contract events

#print axioms pullbackOccurrenceIndex_exact_iff
#print axioms pullbackControl_demand
#print axioms pullbackControl_observe
#print axioms pullbackControl_schedule_readout
#print axioms pullbackControl_preserves_iff
#print axioms mapEventPruning
#print axioms mapAdmittedPruning
#print axioms mapAdmittedPruning_removed
#print axioms pullbackControl_id_occurrence
#print axioms pullbackControl_comp_occurrence
#print axioms pullbackControl_comp_observe

end RepresentedOperationalRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
