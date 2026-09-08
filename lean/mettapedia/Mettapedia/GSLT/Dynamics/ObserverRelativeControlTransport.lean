import Mettapedia.GSLT.Dynamics.ObservationTransport
import Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

/-!
# Observer-relative control transport along event maps

An implementation or theory route maps proof-relevant events forward.  Every
observer and control contract on the target can therefore be pulled back to
source histories.  This construction needs only the event map: it is
independent of the syntax, equational theory, or language family that produced
the events.

The action is contravariant on observations and covariant on concrete changes.
An admitted source transformation maps to an admitted target transformation
with its complete removal ledger.  Exact occurrence identity is deliberately
separate: it pulls back precisely when the event map is injective.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObserverRelativeControlTransport

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObservationTransport
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

universe uSourceEvent uTargetEvent uContainer uValue
  uIdentity uGuard uView uScore uReceipt
universe uSourceState uSourceExecution uTargetState uTargetExecution

/-- The canonical accepted-history architecture after pulling an observation
discipline back along an event map. -/
def pullbackArchitecture
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent) :=
  CollectedEventHistory.architecture
    (ObservationDiscipline.pullback eventMap targetDiscipline)

/-- Pull a target client contract back to source event histories. -/
def pullbackContract
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Guard : Type uGuard} {View : Type uView}
    (contract : Contract TargetEvent Guard View) :
    Contract SourceEvent Guard View where
  observer :=
    { observe := fun events => contract.observer.observe (events.map eventMap) }
  demand := contract.demand

@[simp] theorem pullbackContract_observe
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Guard : Type uGuard} {View : Type uView}
    (contract : Contract TargetEvent Guard View)
    (events : List SourceEvent) :
    (pullbackContract eventMap contract).observer.observe events =
      contract.observer.observe (events.map eventMap) :=
  rfl

@[simp] theorem pullbackContract_demand
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Guard : Type uGuard} {View : Type uView}
    (contract : Contract TargetEvent Guard View) :
    (pullbackContract eventMap contract).demand = contract.demand :=
  rfl

/-! ## The architecture-independent control action -/

/-- Pull observer-relative control between arbitrary proof-relevant execution
architectures.  Event identity and semantic value are transported by separate
maps; no relationship between the two execution families is assumed here. -/
def pullbackControlAlong
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score) :
    ObserverRelativeControlFactorization sourceArchitecture
      Identity Guard View Score where
  occurrence := control.occurrence.pullback eventMap
  contract := pullbackContract eventMap control.contract
  schedule := { readout := control.schedule.readout ∘ valueMap }

@[simp] theorem pullbackControlAlong_occurrence_identify
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score)
    (event : sourceArchitecture.Event) :
    (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
      valueMap control).occurrence.identify event =
        control.occurrence.identify (eventMap event) :=
  rfl

@[simp] theorem pullbackControlAlong_observe
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score)
    (events : List sourceArchitecture.Event) :
    (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
      valueMap control).contract.observer.observe events =
        control.contract.observer.observe (events.map eventMap) :=
  rfl

@[simp] theorem pullbackControlAlong_schedule_readout
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score)
    (value : sourceArchitecture.Value) :
    (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
      valueMap control).schedule.readout value =
        control.schedule.readout (valueMap value) :=
  rfl

/-- Pull the complete observer-relative control boundary back along a map of
proof-relevant events. -/
def pullbackControl
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score) :
    ObserverRelativeControlFactorization
      (pullbackArchitecture eventMap targetDiscipline)
      Identity Guard View Score :=
  pullbackControlAlong
    (pullbackArchitecture eventMap targetDiscipline)
    (CollectedEventHistory.architecture targetDiscipline)
    eventMap id control

@[simp] theorem pullbackControl_occurrence_identify
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    (event : SourceEvent) :
    (pullbackControl eventMap targetDiscipline control).occurrence.identify event =
      control.occurrence.identify (eventMap event) :=
  rfl

@[simp] theorem pullbackControl_observe
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    (events : List SourceEvent) :
    (pullbackControl eventMap targetDiscipline control).contract.observer.observe
        events =
      control.contract.observer.observe (events.map eventMap) :=
  rfl

@[simp] theorem pullbackControl_demand
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score) :
    (pullbackControl eventMap targetDiscipline control).contract.demand =
      control.contract.demand :=
  rfl

@[simp] theorem pullbackControl_schedule_readout
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    (value : targetDiscipline.Value) :
    (pullbackControl eventMap targetDiscipline control).schedule.readout value =
      control.schedule.readout value :=
  rfl

/-- Exact target occurrence identity remains exact at the source exactly when
the event map itself retains all source occurrences. -/
theorem pullbackOccurrence_exact_iff
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Identity : Type uIdentity}
    (index : OccurrenceIndex TargetEvent Identity)
    (exact : index.Exact) :
    (index.pullback eventMap).Exact <-> Function.Injective eventMap :=
  index.pullback_exact_iff eventMap exact

/-- Map the event coordinates of a concrete change. -/
def mapChange
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Receipt : Type uReceipt} (change : Change SourceEvent Receipt) :
    Change TargetEvent Receipt where
  source := change.source.map eventMap
  target := change.target.map eventMap
  receipt := change.receipt

/-- Observer preservation for arbitrary architectures depends only on the
event action; the semantic-value map affects scheduling, not client views. -/
theorem pullbackControlAlong_preserves_iff
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (change : Change sourceArchitecture.Event Receipt) :
    (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
      valueMap control).contract.Preserves change <->
        control.contract.Preserves (mapChange eventMap change) :=
  Iff.rfl

/-- Map a pruning change without losing its removal ledger. -/
def mapPruning
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Receipt : Type uReceipt} (pruning : PruningChange SourceEvent Receipt) :
    PruningChange TargetEvent Receipt where
  source := pruning.source.map eventMap
  target := pruning.target.map eventMap
  receipt := pruning.receipt
  removed := pruning.removed.map eventMap
  accounting := by
    simpa using congrArg (Multiset.map eventMap) pruning.accounting

@[simp] theorem mapPruning_removed
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    {Receipt : Type uReceipt} (pruning : PruningChange SourceEvent Receipt) :
    (mapPruning eventMap pruning).removed = pruning.removed.map eventMap :=
  rfl

/-- Map an admitted pruning between arbitrary execution architectures. -/
def mapAdmittedPruningAlong
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (pruning :
      (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
        valueMap control).AdmittedPruning Receipt) :
    control.AdmittedPruning Receipt where
  val := mapPruning eventMap pruning.1
  property :=
    (pullbackControlAlong_preserves_iff sourceArchitecture targetArchitecture
      eventMap valueMap control pruning.1.toChange).1 pruning.2

/-- Observer preservation at the pulled source boundary is exactly observer
preservation of the mapped target change. -/
theorem pullbackControl_preserves_iff
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt} (change : Change SourceEvent Receipt) :
    (pullbackControl eventMap targetDiscipline control).contract.Preserves change
      <-> control.contract.Preserves (mapChange eventMap change) :=
  Iff.rfl

/-- Map an admitted source pruning to an admitted target pruning.  The source
admission is consumed; the event map itself grants no pruning authority. -/
def mapAdmittedPruning
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (pruning :
      (pullbackControl eventMap targetDiscipline control).AdmittedPruning
        Receipt) :
    control.AdmittedPruning Receipt :=
  mapAdmittedPruningAlong
    (pullbackArchitecture eventMap targetDiscipline)
    (CollectedEventHistory.architecture targetDiscipline)
    eventMap id control pruning

/-- Mapping complete event histories between arbitrary architectures is an
observer-preserving representation at exactly the pulled-back observer. -/
def eventHistoryRepresentationAlong
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score) :
    ObserverPreservingMap (List sourceArchitecture.Event)
      (List targetArchitecture.Event) View
      (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
        valueMap control).contract.observer
      control.contract.observer where
  transform := List.map eventMap
  preserves := fun _ => rfl

/-- Accepted-history specialization of the architecture-independent history
representation. -/
def eventHistoryRepresentation
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score) :
    ObserverPreservingMap (List SourceEvent) (List TargetEvent) View
      (pullbackControl eventMap targetDiscipline control).contract.observer
      control.contract.observer :=
  eventHistoryRepresentationAlong
    (pullbackArchitecture eventMap targetDiscipline)
    (CollectedEventHistory.architecture targetDiscipline)
    eventMap id control

/-- Transport an admitted, fully accounted transformation between arbitrary
architectures.  Both live and removed events are mapped. -/
def mapAccountedTransformationAlong
    {SourceState : Type uSourceState}
    {SourceExecution : SourceState -> SourceState -> Type uSourceExecution}
    {TargetState : Type uTargetState}
    {TargetExecution : TargetState -> TargetState -> Type uTargetExecution}
    (sourceArchitecture :
      CapabilityIndexedObservationArchitecture SourceState SourceExecution)
    (targetArchitecture :
      CapabilityIndexedObservationArchitecture TargetState TargetExecution)
    (eventMap : sourceArchitecture.Event -> targetArchitecture.Event)
    (valueMap : sourceArchitecture.Value -> targetArchitecture.Value)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization targetArchitecture
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControlAlong sourceArchitecture targetArchitecture eventMap
        valueMap control) Receipt) :
    AccountedTransformation control Receipt :=
  AccountedTransformation.ofPruning
    (mapAdmittedPruningAlong sourceArchitecture targetArchitecture eventMap
      valueMap control transformation.toAdmittedPruning)

/-- Accepted-history specialization of accounted transformation transport. -/
def mapAccountedTransformation
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl eventMap targetDiscipline control) Receipt) :
    AccountedTransformation control Receipt :=
  mapAccountedTransformationAlong
    (pullbackArchitecture eventMap targetDiscipline)
    (CollectedEventHistory.architecture targetDiscipline)
    eventMap id control transformation

@[simp] theorem mapAccountedTransformation_source
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl eventMap targetDiscipline control) Receipt) :
    (mapAccountedTransformation eventMap targetDiscipline control
      transformation).source = transformation.source.map eventMap :=
  rfl

@[simp] theorem mapAccountedTransformation_target
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl eventMap targetDiscipline control) Receipt) :
    (mapAccountedTransformation eventMap targetDiscipline control
      transformation).target = transformation.target.map eventMap :=
  rfl

@[simp] theorem mapAccountedTransformation_removed
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl eventMap targetDiscipline control) Receipt) :
    (mapAccountedTransformation eventMap targetDiscipline control
      transformation).removed = transformation.removed.map eventMap :=
  rfl

theorem mapAccountedTransformation_no_silent_loss
    {SourceEvent : Type uSourceEvent} {TargetEvent : Type uTargetEvent}
    (eventMap : SourceEvent -> TargetEvent)
    (targetDiscipline :
      ObservationDiscipline.{uTargetEvent, uContainer, uValue} TargetEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture targetDiscipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl eventMap targetDiscipline control) Receipt) :
    ((mapAccountedTransformation eventMap targetDiscipline control
        transformation).source : Multiset
          (CollectedEventHistory.architecture targetDiscipline).Event) =
      (mapAccountedTransformation eventMap targetDiscipline control
          transformation).target +
        (mapAccountedTransformation eventMap targetDiscipline control
          transformation).removed :=
  AccountedTransformation.no_silent_occurrence_loss _

/-- Occurrence pullback is pointwise functorial. -/
theorem pullbackControl_comp_occurrence
    {FirstEvent : Type uSourceEvent} {MiddleEvent : Type*}
    {LastEvent : Type uTargetEvent}
    (first : FirstEvent -> MiddleEvent) (second : MiddleEvent -> LastEvent)
    (discipline : ObservationDiscipline LastEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    (event : FirstEvent) :
    (pullbackControl (second ∘ first) discipline control).occurrence.identify
        event =
      (pullbackControl first (ObservationDiscipline.pullback second discipline)
        (pullbackControl second discipline control)).occurrence.identify event :=
  rfl

/-- Client observation pullback is pointwise functorial. -/
theorem pullbackControl_comp_observe
    {FirstEvent : Type uSourceEvent} {MiddleEvent : Type*}
    {LastEvent : Type uTargetEvent}
    (first : FirstEvent -> MiddleEvent) (second : MiddleEvent -> LastEvent)
    (discipline : ObservationDiscipline LastEvent)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    (events : List FirstEvent) :
    (pullbackControl (second ∘ first) discipline control).contract.observer.observe
        events =
      (pullbackControl first (ObservationDiscipline.pullback second discipline)
        (pullbackControl second discipline control)).contract.observer.observe
          events := by
  simp only [pullbackControl_observe]
  exact congrArg control.contract.observer.observe
    (List.map_map (g := second) (f := first) (l := events)).symm

#print axioms pullbackOccurrence_exact_iff
#print axioms pullbackControl_preserves_iff
#print axioms mapPruning
#print axioms mapAdmittedPruning
#print axioms mapAccountedTransformation
#print axioms mapAccountedTransformation_no_silent_loss
#print axioms pullbackControl_comp_occurrence
#print axioms pullbackControl_comp_observe

end Mettapedia.GSLT.Dynamics.ObserverRelativeControlTransport
