import Mettapedia.GSLT.LanguageDef.BiformObserverControl
import Mettapedia.GSLT.LanguageDef.BiformTheoryCanary

/-!
# Biform observer-control separation canary

One biform route preserves the native meaning of every event while collapsing
two Boolean proof occurrences to one unit occurrence.  Length observation and
accounted reordering transport correctly, but exact source occurrence identity
does not.  Thus meaning compatibility, observer preservation, and occurrence
reflection are three distinct route properties.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformObserverControlCanary

open CategoryTheory
open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.GSLT.LanguageDef.BiformTheoryCanary
open Mettapedia.GSLT.LanguageDef.HOLHenkinBiformCanary
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HenkinInstitution
open Mettapedia.Logic.HOL.HenkinInstitution.Canary

/-- Collapse the two Boolean evidence occurrences while retaining the unique
extensional endpoint and lifting every target event back to one source event. -/
def boolToUnit : Translation Canary.boolSystem Canary.unitSystem where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapEvidence := fun _ => ()
  liftEvidence := by
    intro sourceTerm targetTerm _evidence
    exact ⟨targetTerm, false, ⟨⟨rfl⟩⟩⟩

/-- The target biform theory gives its single proof occurrence the same native
Henkin theorem as both source occurrences. -/
def unitOccurrenceBiform : BiformTheory henkinConsequence where
  logical := targetLogical
  algorithm := Canary.unitSystem
  meaning := fun _ => targetEquation
  meaning_sound := fun _ => targetEquation_valid

/-- A valid biform route: logical meaning commutes even though proof occurrence
identity is collapsed. -/
def collapseRoute : BiformTheory.Hom occurrenceBiform unitOccurrenceBiform where
  logical := PiInstitution.TheoryHom.identity targetLogical
  operational := boolToUnit
  meaning_natural := by
    intro event
    change henkinConsequence.sentence.map
      (CategoryTheory.CategoryStruct.id targetSignature) targetEquation =
        targetEquation
    exact henkinConsequence.sentence.map_id_apply targetSignature targetEquation

/-- Retain the complete target event list and read its length. -/
def targetDiscipline :
    ObservationDiscipline unitOccurrenceBiform.algorithm.Event where
  collection :=
    { Container := List unitOccurrenceBiform.algorithm.Event
      collect := fun events => some events }
  Value := Nat
  readout := List.length

/-- Target occurrence identity is exact, while the client observes only the
number of retained occurrences. -/
def targetControl : ObserverRelativeControlFactorization
    (CollectedEventHistory.architecture targetDiscipline)
    unitOccurrenceBiform.algorithm.Event Unit Nat Nat where
  occurrence := { identify := id }
  contract :=
    { observer := { observe := List.length }
      demand := { completion := .completeBag } }
  schedule := { readout := id }

theorem targetOccurrence_exact : targetControl.occurrence.Exact :=
  Function.injective_id

/-- Positive control: an identity biform route retains every proof occurrence,
so exact occurrence identity pulls back unchanged. -/
theorem identityRoute_preserves_exact_occurrence :
    (targetControl.occurrence.pullback
      (BiformObserverControl.eventMap
        (BiformTheory.Hom.identity unitOccurrenceBiform))).Exact := by
  rw [BiformObserverControl.pullbackOccurrence_exact_iff
    (BiformTheory.Hom.identity unitOccurrenceBiform)
    targetControl.occurrence targetOccurrence_exact]
  intro left right equalImages
  simpa using equalImages

def falseEvent : occurrenceBiform.algorithm.Event :=
  ⟨(), (), false⟩

def trueEvent : occurrenceBiform.algorithm.Event :=
  ⟨(), (), true⟩

theorem falseEvent_ne_trueEvent : falseEvent ≠ trueEvent := by
  intro equalEvents
  have equalEvidence := congrArg
    (fun event : occurrenceBiform.algorithm.Event => event.evidence) equalEvents
  exact Bool.false_ne_true equalEvidence

/-- The route is deliberately many-to-one on proof occurrences. -/
theorem collapseRoute_event_collision :
    BiformObserverControl.eventMap collapseRoute falseEvent =
      BiformObserverControl.eventMap collapseRoute trueEvent := by
  rfl

theorem collapseRoute_eventMap_not_injective :
    ¬Function.Injective (BiformObserverControl.eventMap collapseRoute) := by
  intro injective
  exact falseEvent_ne_trueEvent (injective collapseRoute_event_collision)

/-- Negative control: exact target occurrence identity cannot be pulled back
through a many-to-one biform route. -/
theorem pulledOccurrence_not_exact :
    ¬(targetControl.occurrence.pullback
      (BiformObserverControl.eventMap collapseRoute)).Exact := by
  rw [BiformObserverControl.pullbackOccurrence_exact_iff collapseRoute
    targetControl.occurrence targetOccurrence_exact]
  exact collapseRoute_eventMap_not_injective

/-- Reordering retains both source occurrences and preserves the pulled-back
length observer. -/
def sourceReorder : AccountedTransformation
    (BiformObserverControl.pullbackControl collapseRoute targetDiscipline
      targetControl) Unit where
  source := [falseEvent, trueEvent]
  target := [trueEvent, falseEvent]
  removed := 0
  receipt := ()
  preserves := rfl
  accounting := by
    change falseEvent ::ₘ trueEvent ::ₘ 0 =
      (trueEvent ::ₘ falseEvent ::ₘ 0) + 0
    rw [add_zero]
    exact Multiset.cons_swap falseEvent trueEvent 0

/-- The same accounted transformation maps through the valid biform route. -/
def targetReorder : AccountedTransformation targetControl Unit :=
  BiformObserverControl.mapAccountedTransformation collapseRoute
    targetDiscipline targetControl sourceReorder

theorem targetReorder_keeps_two_events :
    targetReorder.source.length = 2 ∧ targetReorder.target.length = 2 := by
  decide

theorem targetReorder_has_no_silent_loss :
    (targetReorder.source : Multiset
      (CollectedEventHistory.architecture targetDiscipline).Event) =
      (targetReorder.target : Multiset
        (CollectedEventHistory.architecture targetDiscipline).Event) +
        targetReorder.removed :=
  targetReorder.accounting

/-- Dropping an occurrence is rejected by the length observer, even though
both source evidence tags have the same native meaning theorem. -/
def sourceDrop : Change occurrenceBiform.algorithm.Event Unit where
  source := [falseEvent]
  target := []
  receipt := ()

theorem sourceDrop_not_preserved :
    ¬(BiformObserverControl.pullbackControl collapseRoute targetDiscipline
      targetControl).contract.Preserves sourceDrop := by
  intro preserved
  change 1 = 0 at preserved
  omega

#print axioms falseEvent_ne_trueEvent
#print axioms identityRoute_preserves_exact_occurrence
#print axioms collapseRoute_event_collision
#print axioms collapseRoute_eventMap_not_injective
#print axioms pulledOccurrence_not_exact
#print axioms targetReorder_keeps_two_events
#print axioms targetReorder_has_no_silent_loss
#print axioms sourceDrop_not_preserved

end Mettapedia.GSLT.LanguageDef.BiformObserverControlCanary
