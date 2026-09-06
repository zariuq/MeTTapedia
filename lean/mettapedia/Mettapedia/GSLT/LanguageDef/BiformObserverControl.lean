import Mettapedia.GSLT.Dynamics.ObserverRelativeControlTransport
import Mettapedia.GSLT.LanguageDef.BiformTheory

/-!
# Observer-relative control along biform routes

A biform route transports both native meaning and proof-relevant operational
events.  The event action is therefore sufficient to reindex a target
observer, occurrence index, client contract, and scheduler readout.  This
module specializes the generic event-map construction; it adds no authority
to the biform route.

Meaning compatibility and occurrence reflection remain different laws.  The
former is already a field of a biform route.  The latter holds after pullback
exactly when the operational event action is injective.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformObserverControl

open CategoryTheory
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObserverRelativeControlTransport
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.ProofRelevant

universe uSignature uHom uSentence uTerm
  uContainer uValue uIdentity uGuard uView uScore uReceipt

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
  {source target middle :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}

/-- The proof-relevant event action underlying a biform route. -/
def eventMap (route : BiformTheory.Hom source target) :
    source.algorithm.Event -> target.algorithm.Event :=
  route.operational.mapEvent

@[simp] theorem eventMap_apply (route : BiformTheory.Hom source target)
    (event : source.algorithm.Event) :
    eventMap route event = route.operational.mapEvent event :=
  rfl

/-- Pull a target observation discipline back along the operational model of a
biform route. -/
def pullbackDiscipline (route : BiformTheory.Hom source target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event) :
    ObservationDiscipline source.algorithm.Event :=
  ObservationTransport.ObservationDiscipline.pullback
    (eventMap route) discipline

/-- Pull target observer-relative control back to the source biform theory. -/
def pullbackControl (route : BiformTheory.Hom source target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score) :=
  ObserverRelativeControlTransport.pullbackControl
    (eventMap route) discipline control

@[simp] theorem pullbackControl_observe
    (route : BiformTheory.Hom source target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    (events : List source.algorithm.Event) :
    (pullbackControl route discipline control).contract.observer.observe events =
      control.contract.observer.observe (events.map (eventMap route)) :=
  rfl

/-- An exact target occurrence index pulls back exactly when the biform route
retains source event identity. -/
theorem pullbackOccurrence_exact_iff
    (route : BiformTheory.Hom source target)
    {Identity : Type uIdentity}
    (index : OccurrenceIndex target.algorithm.Event Identity)
    (exact : index.Exact) :
    (index.pullback (eventMap route)).Exact <->
      Function.Injective (eventMap route) :=
  ObserverRelativeControlTransport.pullbackOccurrence_exact_iff
    (eventMap route) index exact

/-- Complete event-history translation preserves exactly the target observer
pulled back through the biform route. -/
def eventHistoryRepresentation
    (route : BiformTheory.Hom source target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score) :=
  ObserverRelativeControlTransport.eventHistoryRepresentation
    (eventMap route) discipline control

/-- Transport an observer-admitted, completely accounted source
transformation along the operational model of a biform route. -/
def mapAccountedTransformation
    (route : BiformTheory.Hom source target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl route discipline control) Receipt) :=
  ObserverRelativeControlTransport.mapAccountedTransformation
    (eventMap route) discipline control transformation

@[simp] theorem mapAccountedTransformation_removed
    (route : BiformTheory.Hom source target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    {Receipt : Type uReceipt}
    (transformation : AccountedTransformation
      (pullbackControl route discipline control) Receipt) :
    (mapAccountedTransformation route discipline control
      transformation).removed =
        transformation.removed.map (eventMap route) :=
  rfl

/-- Biform composition induces pointwise composition of the event maps used
by observer transport. -/
theorem eventMap_comp (earlier : BiformTheory.Hom source middle)
    (later : BiformTheory.Hom middle target)
    (event : source.algorithm.Event) :
    eventMap (BiformTheory.Hom.comp earlier later) event =
      eventMap later (eventMap earlier event) :=
  Translation.mapEvent_comp earlier.operational later.operational event

/-- Pulling occurrence identity through a composite biform route agrees
pointwise with pulling it through the two routes in succession. -/
theorem pullbackControl_comp_occurrence
    (earlier : BiformTheory.Hom source middle)
    (later : BiformTheory.Hom middle target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    (event : source.algorithm.Event) :
    (pullbackControl (BiformTheory.Hom.comp earlier later) discipline
      control).occurrence.identify event =
      (pullbackControl earlier (pullbackDiscipline later discipline)
        (pullbackControl later discipline control)).occurrence.identify event := by
  change control.occurrence.identify
      (eventMap (BiformTheory.Hom.comp earlier later) event) =
    control.occurrence.identify
      (eventMap later (eventMap earlier event))
  rw [eventMap_comp]

/-- Pulling a client observer through a composite biform route agrees
pointwise with successive pullback. -/
theorem pullbackControl_comp_observe
    (earlier : BiformTheory.Hom source middle)
    (later : BiformTheory.Hom middle target)
    (discipline :
      ObservationDiscipline.{uTerm, uContainer, uValue}
        target.algorithm.Event)
    {Identity : Type uIdentity} {Guard : Type uGuard}
    {View : Type uView} {Score : Type uScore}
    (control : ObserverRelativeControlFactorization
      (CollectedEventHistory.architecture discipline)
      Identity Guard View Score)
    (events : List source.algorithm.Event) :
    (pullbackControl (BiformTheory.Hom.comp earlier later) discipline
      control).contract.observer.observe events =
      (pullbackControl earlier (pullbackDiscipline later discipline)
        (pullbackControl later discipline control)).contract.observer.observe
          events := by
  change control.contract.observer.observe
      (events.map (eventMap (BiformTheory.Hom.comp earlier later))) =
    control.contract.observer.observe
      ((events.map (eventMap earlier)).map (eventMap later))
  apply congrArg control.contract.observer.observe
  induction events with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.map_cons, eventMap_comp, inductionHypothesis]

#print axioms pullbackOccurrence_exact_iff
#print axioms mapAccountedTransformation
#print axioms mapAccountedTransformation_removed
#print axioms eventMap_comp
#print axioms pullbackControl_comp_occurrence
#print axioms pullbackControl_comp_observe

end Mettapedia.GSLT.LanguageDef.BiformObserverControl
