import Mettapedia.Languages.MeTTa.PrimeCellCausalFrontier
import Mettapedia.Languages.MeTTa.PrimeNativeReceiptCorrespondence

/-!
# Native receipt projection into the Prime cell-causal machine

The native checker already validates occurrence uniqueness and conflict-free
causal closure.  This module projects its cell-observation events into the
global producer layer and proves that every accepted receipt selects at most
one outcome for each Need cell.

Native observation-event IDs remain in `PrimeNativeReceiptCorrespondence`.
They identify subscriber observations, not distinct producer outcomes, so this
projection deliberately quotients them to one canonical producer occurrence.

This is the checked projection boundary, not a claim that arbitrary native C
execution refines every transition of the abstract machine.  A full replay
certificate must additionally connect demand subscriptions and publication
steps.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCellCausalNativeRefinement

open PrimeCellCausalSemantics
open PrimeCellCausalFrontier
open PrimeNativeReceiptCorrespondence

abbrev NativeOutcomeOccurrence := Unit

abbrev NativeOutcome (Obs : Type*) :=
  OutcomeEvent NativeCell NativeOutcomeOccurrence Obs

def decodeOutcome {Obs Eff : Type*} :
    NativeEvent Obs Eff → Option (NativeOutcome Obs)
  | { eventId := _, payload := .observeCell cell _ observation } =>
      some
        { producer := cell
          occurrence := ()
          outcome := observation }
  | _ => none

def decodedOutcomes
    {Obs Eff : Type*} [DecidableEq Obs]
    (receipt : NativeReceipt Obs Eff) :
    Finset (NativeOutcome Obs) :=
  (receipt.events.filterMap decodeOutcome).toFinset

theorem mem_decodedOutcomes_iff
    {Obs Eff : Type*} [DecidableEq Obs]
    {receipt : NativeReceipt Obs Eff}
    {outcome : NativeOutcome Obs} :
    outcome ∈ decodedOutcomes receipt ↔
      ∃ event ∈ receipt.events, decodeOutcome event = some outcome := by
  simp [decodedOutcomes]

def nativeOutcomeModel (Obs : Type*) :
    Model NativeCell NativeOutcomeOccurrence Obs
      (NativeCell × Obs) where
  outcomeRoot outcome :=
    (outcome.producer, outcome.outcome)

abbrev NativeProducerState (Obs : Type*) :=
  State Nat (Option NativeSource) NativeCell Unit
    NativeOutcomeOccurrence Obs (NativeCell × Obs)
    Nat Unit

def decodedProducerState
    {Obs Eff : Type*} [DecidableEq Obs]
    (receipt : NativeReceipt Obs Eff) :
    NativeProducerState Obs :=
  { produced := decodedOutcomes receipt
    subscriptions := ∅
    observations := ∅
    roots := ∅
    publications := ∅ }

/-- Conflict-free native receipt validation implies the global machine's
one-outcome-per-cell invariant after quotienting subscriber observations. -/
theorem valid_decodedProducerState_functional
    {Obs Eff : Type*} [DecidableEq Obs] [DecidableEq Eff]
    {basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Obs Eff)}
    {effectConflict : Eff → Eff → Prop}
    {receipt : NativeReceipt Obs Eff}
    (valid : Valid basis effectConflict receipt) :
    ProducedFunctional (decodedProducerState receipt) := by
  intro left right leftMember rightMember sameProducer
  rcases mem_decodedOutcomes_iff.mp leftMember with
    ⟨leftEvent, leftNative, leftDecoded⟩
  rcases mem_decodedOutcomes_iff.mp rightMember with
    ⟨rightEvent, rightNative, rightDecoded⟩
  rcases leftEvent with ⟨leftId, leftPayload⟩
  rcases rightEvent with ⟨rightId, rightPayload⟩
  cases leftPayload <;> simp [decodeOutcome] at leftDecoded
  case observeCell leftCell leftSource leftObservation =>
    cases rightPayload <;> simp [decodeOutcome] at rightDecoded
    case observeCell rightCell rightSource rightObservation =>
      subst left
      subst right
      have sameCell : leftCell = rightCell := by
        simpa using sameProducer
      subst rightCell
      have leftRoot :
          ({ occurrence := leftId
             payload := .cellObserved leftSource leftCell leftObservation } :
            DecodedEvent Obs Eff) ∈ decodedRoots receipt := by
        have member :
            decodeEvent
              ({ eventId := leftId
                 payload := .observeCell leftCell leftSource leftObservation } :
                NativeEvent Obs Eff) ∈ decodedEvents receipt :=
          List.mem_map_of_mem leftNative
        simpa [decodedRoots, decodeEvent] using member
      have rightRoot :
          ({ occurrence := rightId
             payload := .cellObserved rightSource leftCell rightObservation } :
            DecodedEvent Obs Eff) ∈ decodedRoots receipt := by
        have member :
            decodeEvent
              ({ eventId := rightId
                 payload := .observeCell leftCell rightSource rightObservation } :
                NativeEvent Obs Eff) ∈ decodedEvents receipt :=
          List.mem_map_of_mem rightNative
        simpa [decodedRoots, decodeEvent] using member
      have sameObservation : leftObservation = rightObservation :=
        valid_observations_functional valid leftRoot rightRoot rfl rfl
      subst rightObservation
      rfl

theorem accepted_decodedProducerState_functional
    {Obs Eff : Type*} [DecidableEq Obs] [DecidableEq Eff]
    (basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Obs Eff))
    (executable : ExecutableCausalBasis basis)
    (effectConflict : Eff → Eff → Prop)
    [DecidableRel effectConflict]
    (receipt : NativeReceipt Obs Eff)
    (accepted : accepts basis executable effectConflict receipt = true) :
    ProducedFunctional (decodedProducerState receipt) :=
  valid_decodedProducerState_functional
    ((accepts_iff_valid basis executable effectConflict receipt).mp accepted)

/-! ## Replay-annotated subscriber projection -/

/-- Native observation events identify the cell, source site, and observed
value.  Demand role and expected type belong to candidate replay rather than
the answer receipt, so the bridge requires them as explicit annotations. -/
structure NativeDemandAnnotation (ExpectedType : Type*) where
  roleFor : Nat → DemandRole
  expectedTypeFor : Nat → ExpectedType

def lhsUnitAnnotation : NativeDemandAnnotation Unit :=
  { roleFor := fun _ => .lhs
    expectedTypeFor := fun _ => () }

def rhsUnitAnnotation : NativeDemandAnnotation Unit :=
  { roleFor := fun _ => .rhs
    expectedTypeFor := fun _ => () }

/-- The answer receipt alone cannot determine whether an observation was
demanded by matching or by the selected right-hand side. -/
theorem lhsUnitAnnotation_ne_rhsUnitAnnotation :
    lhsUnitAnnotation ≠ rhsUnitAnnotation := by
  intro equal
  have rolesEqual := congrArg (fun annotation => annotation.roleFor 0) equal
  cases rolesEqual

def decodeAnnotatedObservation
    {Obs Eff ExpectedType : Type*}
    (annotation : NativeDemandAnnotation ExpectedType)
    (rule : Nat) :
    NativeEvent Obs Eff → Option
      (Observation Nat (Option NativeSource) NativeCell ExpectedType
        NativeOutcomeOccurrence Obs)
  | { eventId := eventId
      payload := .observeCell cell source observation } =>
      some
        { subscription :=
            { rule := rule
              source := source
              producer := cell
              role := annotation.roleFor eventId
              expectedType := annotation.expectedTypeFor eventId }
          event :=
            { producer := cell
              occurrence := ()
              outcome := observation } }
  | _ => none

def decodedAnswerObservations
    {Obs Eff ExpectedType : Type*}
    [DecidableEq Obs] [DecidableEq ExpectedType]
    (annotation : NativeDemandAnnotation ExpectedType)
    (rule : Nat) (receipt : NativeReceipt Obs Eff) :
    Finset
      (Observation Nat (Option NativeSource) NativeCell ExpectedType
        NativeOutcomeOccurrence Obs) :=
  (receipt.events.filterMap
    (decodeAnnotatedObservation annotation rule)).toFinset

abbrev NativeAnswerState (ExpectedType Obs : Type*) :=
  State Nat (Option NativeSource) NativeCell ExpectedType
    NativeOutcomeOccurrence Obs (NativeCell × Obs) Nat Unit

def decodedAnswerState
    {Obs Eff ExpectedType : Type*}
    [DecidableEq Obs] [DecidableEq ExpectedType]
    (annotation : NativeDemandAnnotation ExpectedType)
    (rule : Nat) (receipt : NativeReceipt Obs Eff) :
    NativeAnswerState ExpectedType Obs :=
  let observations := decodedAnswerObservations annotation rule receipt
  { produced := observations.image Observation.event
    subscriptions := observations.image Observation.subscription
    observations := observations
    roots := observations.image fun observation =>
      { rule := rule
        event :=
          (observation.event.producer, observation.event.outcome) }
    publications := ∅ }

theorem decodedAnswerObservation_aligned
    {Obs Eff ExpectedType : Type*}
    [DecidableEq Obs] [DecidableEq ExpectedType]
    {annotation : NativeDemandAnnotation ExpectedType}
    {rule : Nat} {receipt : NativeReceipt Obs Eff}
    {observation :
      Observation Nat (Option NativeSource) NativeCell ExpectedType
        NativeOutcomeOccurrence Obs}
    (member : observation ∈
      decodedAnswerObservations annotation rule receipt) :
    observation.subscription.producer = observation.event.producer := by
  have listMember : observation ∈ receipt.events.filterMap
      (decodeAnnotatedObservation annotation rule) := by
    simpa [decodedAnswerObservations] using member
  rcases List.mem_filterMap.mp listMember with
    ⟨native, nativeMember, decoded⟩
  cases native with
  | mk eventId payload =>
    cases payload <;>
      simp [decodeAnnotatedObservation] at decoded
    case observeCell cell source value =>
      subst observation
      rfl

theorem decodedAnswerState_observationsSupported
    {Obs Eff ExpectedType : Type*}
    [DecidableEq Obs] [DecidableEq ExpectedType]
    (annotation : NativeDemandAnnotation ExpectedType)
    (rule : Nat) (receipt : NativeReceipt Obs Eff) :
    ObservationsSupported
      (decodedAnswerState annotation rule receipt) := by
  intro observation member
  refine ⟨?_, ?_, decodedAnswerObservation_aligned member⟩
  · exact Finset.mem_image.mpr ⟨observation, member, rfl⟩
  · exact Finset.mem_image.mpr ⟨observation, member, rfl⟩

theorem rootsFor_decodedAnswerState
    {Obs Eff ExpectedType : Type*}
    [DecidableEq Obs] [DecidableEq ExpectedType]
    (annotation : NativeDemandAnnotation ExpectedType)
    (rule : Nat) (receipt : NativeReceipt Obs Eff) :
    rootsFor (decodedAnswerState annotation rule receipt) rule =
      (decodedAnswerObservations annotation rule receipt).image
        (fun observation =>
          (observation.event.producer, observation.event.outcome)) := by
  ext event
  simp [rootsFor, decodedAnswerState, eq_comm]

end Mettapedia.Languages.MeTTa.PrimeCellCausalNativeRefinement
