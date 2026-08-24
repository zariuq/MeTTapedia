import Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.WorkSpan

/-!
# Target-native realization of transported parallelism

Linear-effect transport can preserve a separation certificate, but a target
language still owns the operational theorem that separated occurrences
commute.  This module isolates that theorem as a proof-relevant capability.

A contextual occurrence execution explains how an authenticated occurrence
fires inside a larger target state.  A separation realizer then constructs
both chronological orders with one common target.  Only their conjunction
licenses the one-wave WorkSpan observation; resource agreement alone cannot
manufacture execution.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILNativeParallelRealization

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Algebra
open Mettapedia.Languages.MeTTa.Prime.GSLTILInteractionTransport
open Mettapedia.Languages.MeTTa.Prime.GSLTILLinearEffectTransport
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uSite uEvent uResource uSourceResource uTargetResource uContext

/-! ## Generic target-native operational capability -/

/-- A proof-relevant explanation of how an authenticated occurrence may fire
inside a larger state of the same target language. -/
structure ContextualOccurrenceExecution
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory) where
  StepIn : Occurrence presentation → theory.Term → theory.Term → Type uContext
  sound : ∀ {occurrence source target},
    StepIn occurrence source target → theory.Step source target

/-- Two contextual occurrences execute in either order and reach one exact
common target.  The four proof-relevant contextual steps are retained. -/
structure NativePairDiamond
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (execution : ContextualOccurrenceExecution.{uSite, uEvent, uContext}
      presentation)
    (left right : Occurrence presentation)
    (source : theory.Term) : Type _ where
  leftMiddle : theory.Term
  rightMiddle : theory.Term
  target : theory.Term
  leftFirst : execution.StepIn left source leftMiddle
  rightAfter : execution.StepIn right leftMiddle target
  rightFirst : execution.StepIn right source rightMiddle
  leftAfter : execution.StepIn left rightMiddle target

namespace NativePairDiamond

/-- A native pair diamond erases to the four target-language steps. -/
theorem stepSquare
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {execution : ContextualOccurrenceExecution.{uSite, uEvent, uContext}
      presentation}
    {left right : Occurrence presentation}
    {source : theory.Term}
    (diamond : NativePairDiamond execution left right source) :
    theory.Step source diamond.leftMiddle ∧
      theory.Step diamond.leftMiddle diamond.target ∧
      theory.Step source diamond.rightMiddle ∧
      theory.Step diamond.rightMiddle diamond.target :=
  ⟨execution.sound diamond.leftFirst,
    execution.sound diamond.rightAfter,
    execution.sound diamond.rightFirst,
    execution.sound diamond.leftAfter⟩

/-- A certified two-event diamond is one wave with work two and span one. -/
def workSpan
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {execution : ContextualOccurrenceExecution.{uSite, uEvent, uContext}
      presentation}
    {left right : Occurrence presentation}
    {source : theory.Term}
    (_diamond : NativePairDiamond execution left right source) : WorkSpan :=
  ⟨2, 1⟩

@[simp] theorem workSpan_eq_parallel
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {execution : ContextualOccurrenceExecution.{uSite, uEvent, uContext}
      presentation}
    {left right : Occurrence presentation}
    {source : theory.Term}
    (diamond : NativePairDiamond execution left right source) :
    diamond.workSpan = ⟨2, 1⟩ :=
  rfl

end NativePairDiamond

/-- A target language may claim separation-complete native parallelism only
by constructing the operational diamond for every certificate in the stated
effect analysis. -/
structure SeparationRealizer
    {theory : GSLT}
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {Resource : Type uResource}
    (analysis : OccurrenceEffectAnalysis presentation Resource)
    (execution : ContextualOccurrenceExecution.{uSite, uEvent, uContext}
      presentation)
    (state : Multiset Resource → theory.Term) where
  realize : ∀ {inventory : Multiset Resource}
      {left right : Occurrence presentation},
    PairSeparation inventory (analysis.effect left) (analysis.effect right) →
      NativePairDiamond execution left right (state inventory)

/-! ## GSLT-IL transport followed by target-native realization -/

/-- The complete capability needed to turn source separation into a target
diamond: agreement transfers resource ownership, while the target realizer
supplies operational commutation. -/
structure TransportedNativeParallelCapability
    {sourceTheory targetTheory : GSLT}
    (translation : OperationalTranslation sourceTheory targetTheory)
    (sourcePresentation : InteractionPresentation.{uSite, uEvent} sourceTheory)
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    (sourceAnalysis : OccurrenceEffectAnalysis sourcePresentation SourceResource)
    (resourceMap : SourceResource → TargetResource)
    (targetAnalysis : OccurrenceEffectAnalysis
      (transportedPresentation translation sourcePresentation) TargetResource)
    (targetExecution : ContextualOccurrenceExecution
      (transportedPresentation translation sourcePresentation))
    (targetState : Multiset TargetResource → targetTheory.Term) where
  consumptionAgreement : ConsumptionAgreement
    (transportedEffectAnalysis translation sourcePresentation sourceAnalysis
      resourceMap)
    targetAnalysis
  separationRealizer : SeparationRealizer targetAnalysis targetExecution
    targetState

namespace TransportedNativeParallelCapability

/-- A source separation certificate reaches the target operational diamond
without identifying source and target analyses definitionally. -/
def realize
    {sourceTheory targetTheory : GSLT}
    {translation : OperationalTranslation sourceTheory targetTheory}
    {sourcePresentation : InteractionPresentation.{uSite, uEvent} sourceTheory}
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    {sourceAnalysis : OccurrenceEffectAnalysis sourcePresentation SourceResource}
    {resourceMap : SourceResource → TargetResource}
    {targetAnalysis : OccurrenceEffectAnalysis
      (transportedPresentation translation sourcePresentation) TargetResource}
    {targetExecution : ContextualOccurrenceExecution
      (transportedPresentation translation sourcePresentation)}
    {targetState : Multiset TargetResource → targetTheory.Term}
    (capability : TransportedNativeParallelCapability translation
      sourcePresentation sourceAnalysis resourceMap targetAnalysis
      targetExecution targetState)
    {inventory : Multiset SourceResource}
    {left right : Occurrence sourcePresentation}
    (separation : PairSeparation inventory
      (sourceAnalysis.effect left) (sourceAnalysis.effect right)) :
    NativePairDiamond targetExecution
      (transportOccurrence translation sourcePresentation left)
      (transportOccurrence translation sourcePresentation right)
      (targetState (inventory.map resourceMap)) :=
  capability.separationRealizer.realize
    (targetPairSeparationOfConsumptionAgreement translation sourcePresentation
      sourceAnalysis resourceMap targetAnalysis
      capability.consumptionAgreement separation)

/-- The transported native realization exposes the target commuting square. -/
theorem realized_stepSquare
    {sourceTheory targetTheory : GSLT}
    {translation : OperationalTranslation sourceTheory targetTheory}
    {sourcePresentation : InteractionPresentation.{uSite, uEvent} sourceTheory}
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    {sourceAnalysis : OccurrenceEffectAnalysis sourcePresentation SourceResource}
    {resourceMap : SourceResource → TargetResource}
    {targetAnalysis : OccurrenceEffectAnalysis
      (transportedPresentation translation sourcePresentation) TargetResource}
    {targetExecution : ContextualOccurrenceExecution
      (transportedPresentation translation sourcePresentation)}
    {targetState : Multiset TargetResource → targetTheory.Term}
    (capability : TransportedNativeParallelCapability translation
      sourcePresentation sourceAnalysis resourceMap targetAnalysis
      targetExecution targetState)
    {inventory : Multiset SourceResource}
    {left right : Occurrence sourcePresentation}
    (separation : PairSeparation inventory
      (sourceAnalysis.effect left) (sourceAnalysis.effect right)) :
    let diamond := capability.realize separation
    targetTheory.Step (targetState (inventory.map resourceMap))
        diamond.leftMiddle ∧
      targetTheory.Step diamond.leftMiddle diamond.target ∧
      targetTheory.Step (targetState (inventory.map resourceMap))
        diamond.rightMiddle ∧
      targetTheory.Step diamond.rightMiddle diamond.target :=
  (capability.realize separation).stepSquare

@[simp] theorem realized_workSpan
    {sourceTheory targetTheory : GSLT}
    {translation : OperationalTranslation sourceTheory targetTheory}
    {sourcePresentation : InteractionPresentation.{uSite, uEvent} sourceTheory}
    {SourceResource : Type uSourceResource}
    {TargetResource : Type uTargetResource}
    {sourceAnalysis : OccurrenceEffectAnalysis sourcePresentation SourceResource}
    {resourceMap : SourceResource → TargetResource}
    {targetAnalysis : OccurrenceEffectAnalysis
      (transportedPresentation translation sourcePresentation) TargetResource}
    {targetExecution : ContextualOccurrenceExecution
      (transportedPresentation translation sourcePresentation)}
    {targetState : Multiset TargetResource → targetTheory.Term}
    (capability : TransportedNativeParallelCapability translation
      sourcePresentation sourceAnalysis resourceMap targetAnalysis
      targetExecution targetState)
    {inventory : Multiset SourceResource}
    {left right : Occurrence sourcePresentation}
    (separation : PairSeparation inventory
      (sourceAnalysis.effect left) (sourceAnalysis.effect right)) :
    (capability.realize separation).workSpan = ⟨2, 1⟩ :=
  rfl

end TransportedNativeParallelCapability

/-! ## A nontrivial resource-consumption model -/

namespace ResourceModel

variable (Resource : Type uResource)

/-- A language whose states are exact resource occurrence multisets and whose
steps consume one nonempty submultiset. -/
def theory : GSLT where
  Term := Multiset Resource
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    ∃ demand : Multiset Resource, demand ≠ 0 ∧ source = demand + target
  rewrites_resp_left := by
    rintro source source' target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target target' step rfl
    exact step

structure Event (source target : Multiset Resource) where
  demand : Multiset Resource
  nonzero : demand ≠ 0
  source_eq : source = demand + target

def presentation : InteractionPresentation (theory Resource) where
  Site := PUnit
  Event := fun _ source target => Event Resource source target
  sound := by
    intro _ source target event
    exact ⟨event.demand, event.nonzero, event.source_eq⟩

def occurrenceDemand (occurrence : Occurrence (presentation Resource)) :
    Multiset Resource :=
  occurrence.2.evidence.demand

def analysis : OccurrenceEffectAnalysis (presentation Resource) Resource where
  effect := fun occurrence =>
    ⟨PUnit.unit, occurrenceDemand Resource occurrence, 0⟩

/-- The occurrence may be replayed in any larger state containing the same
exact demand; the original event supplies its non-emptiness evidence. -/
def execution : ContextualOccurrenceExecution (presentation Resource) where
  StepIn := fun occurrence (source target : Multiset Resource) =>
    PLift (source = occurrenceDemand Resource occurrence + target)
  sound := by
    intro occurrence source target contextual
    exact ⟨occurrenceDemand Resource occurrence,
      occurrence.2.evidence.nonzero, contextual.down⟩

/-- Exact multiset separation constructs both resource-consumption orders. -/
def realizer : SeparationRealizer (analysis Resource) (execution Resource) id where
  realize := by
    intro inventory left right separation
    refine
      { leftMiddle :=
          occurrenceDemand Resource right + separation.frame
        rightMiddle :=
          occurrenceDemand Resource left + separation.frame
        target := separation.frame
        leftFirst := ⟨?_⟩
        rightAfter := ⟨rfl⟩
        rightFirst := ⟨?_⟩
        leftAfter := ⟨rfl⟩ }
    · simpa [analysis, occurrenceDemand, add_assoc] using separation.source_eq
    · calc
        inventory =
            occurrenceDemand Resource left +
              occurrenceDemand Resource right + separation.frame := by
          simpa [analysis, occurrenceDemand] using separation.source_eq
        _ = occurrenceDemand Resource right +
              (occurrenceDemand Resource left + separation.frame) := by
          ac_rfl

end ResourceModel

/-! ## Positive and negative controls -/

namespace Canary

inductive Resource where
  | left
  | right
  deriving DecidableEq

def singleton (resource : Resource) :
    (ResourceModel.theory Resource).Term :=
  ({resource} : Multiset Resource)

def empty : (ResourceModel.theory Resource).Term :=
  (0 : Multiset Resource)

def occurrence (resource : Resource) :
    Occurrence (ResourceModel.presentation Resource) :=
  ⟨singleton resource,
    ⟨PUnit.unit, empty,
      { demand := ({resource} : Multiset Resource)
        nonzero := by simp
        source_eq := by simp [singleton, empty] }⟩⟩

def leftOccurrence : Occurrence (ResourceModel.presentation Resource) :=
  occurrence .left

def rightOccurrence : Occurrence (ResourceModel.presentation Resource) :=
  occurrence .right

def inventory : Multiset Resource :=
  {.left, .right}

def separation : PairSeparation inventory
    ((ResourceModel.analysis Resource).effect leftOccurrence)
    ((ResourceModel.analysis Resource).effect rightOccurrence) where
  frame := 0
  source_eq := by
    change ({.left, .right} : Multiset Resource) =
      {.left} + {.right} + 0
    decide

/-- Positive control: the reusable resource semantics constructs a genuine
common-target diamond with the one-wave readout. -/
theorem resource_model_realizes_parallel_pair :
    let diamond := (ResourceModel.realizer Resource).realize separation
    (ResourceModel.theory Resource).Step inventory diamond.leftMiddle ∧
      (ResourceModel.theory Resource).Step diamond.leftMiddle diamond.target ∧
      (ResourceModel.theory Resource).Step inventory diamond.rightMiddle ∧
      (ResourceModel.theory Resource).Step diamond.rightMiddle diamond.target ∧
      diamond.workSpan = ⟨2, 1⟩ := by
  let diamond := (ResourceModel.realizer Resource).realize separation
  exact ⟨diamond.stepSquare.1, diamond.stepSquare.2.1,
    diamond.stepSquare.2.2.1, diamond.stepSquare.2.2.2, rfl⟩

/-- An execution-less target has the same authenticated occurrences and exact
effect analysis, but cannot realize even one contextual step. -/
def blockedExecution : ContextualOccurrenceExecution
    (ResourceModel.presentation Resource) where
  StepIn := fun _ _ _ => PEmpty
  sound := by
    intro _ _ _ impossible
    exact nomatch impossible

theorem blocked_has_no_separation_realizer :
    IsEmpty
      (SeparationRealizer (ResourceModel.analysis Resource) blockedExecution
        id) := by
  constructor
  intro alleged
  have diamond := alleged.realize separation
  exact nomatch diamond.leftFirst

/-- Resource separation and reflexive analysis agreement do not manufacture
target execution.  The operational realizer is irreducible structure. -/
theorem separation_and_agreement_do_not_create_execution :
    Nonempty (PairSeparation inventory
      ((ResourceModel.analysis Resource).effect leftOccurrence)
      ((ResourceModel.analysis Resource).effect rightOccurrence)) ∧
      Nonempty (ConsumptionAgreement
        (ResourceModel.analysis Resource) (ResourceModel.analysis Resource)) ∧
      IsEmpty
        (SeparationRealizer (ResourceModel.analysis Resource) blockedExecution
          id) :=
  ⟨⟨separation⟩, ⟨ConsumptionAgreement.refl _⟩,
    blocked_has_no_separation_realizer⟩

end Canary

#print axioms NativePairDiamond.stepSquare
#print axioms TransportedNativeParallelCapability.realized_stepSquare
#print axioms TransportedNativeParallelCapability.realized_workSpan
#print axioms ResourceModel.realizer
#print axioms Canary.resource_model_realizes_parallel_pair
#print axioms Canary.blocked_has_no_separation_realizer
#print axioms Canary.separation_and_agreement_do_not_create_execution

end Mettapedia.Languages.MeTTa.Prime.GSLTILNativeParallelRealization
