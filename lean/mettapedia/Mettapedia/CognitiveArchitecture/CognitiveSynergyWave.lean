import Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
import Mettapedia.CognitiveArchitecture.CognitiveSynergy

/-!
# Proof-relevant cognitive synergy inside a licensed mind-agent wave

An attention-guided wave says which finite foreground/background batch may run
together.  Cognitive synergy says that a distinct provider produced an exact
occurrence which lets a stuck consumer advance.  Neither statement implies
the other.  This module joins them with an explicit positional link from the
provider's batch item to the fulfillment occurrence.

The bridge retains a separate foreground consumer position, occurrence
identity, execution/resource certificates, and optional value guidance.
Changing guidance cannot change either the synergy witness or the activation
plan.  An opaque delivery channel still blocks mediated synergy even when an
otherwise valid wave exists.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.CognitiveSynergyWave

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
open Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
open Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy
open Mettapedia.CognitiveArchitecture.CognitiveSynergy
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualControlSurface
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uId uActor uCurrency uDomain
universe uItem uGuard uCandidateView uState uStateView uValue uPriority

/-- A proof-relevant service occurrence connected to one licensed cognitive
wave.  `fulfillmentOf` is explicit because the wave item may be a task record,
not the fulfillment object itself. -/
structure ServiceWave
    {RequestId : Type uId} {Actor : Type uActor}
    {horizon : ImportanceHorizon} {Currency : Type uCurrency}
    [AddCommMonoid Currency]
    {Source Target : Type uDomain}
    (request : ServiceRequest RequestId Actor horizon Currency Source Target)
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    (fulfillmentOf : Item → Option request.Fulfillment)
    (provider consumer : Process Actor Bool request.Fulfillment)
    (providerState consumerState : Bool)
    (contract : Contract Item Guard CandidateView)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (shortDemand : Item → Fund .shortTerm Actor Currency)
    (longDemand : Item → Fund .longTerm Actor Currency)
    (shortSource : Fund .shortTerm Actor Currency)
    (longSource : Fund .longTerm Actor Currency)
    (batch : List Item)
    (Value : Type uValue) (Priority : Type uPriority) where
  attention : AttentionGuidedMindAgentWave.Wave contract semantics initial referenceTarget
    shortDemand longDemand shortSource longSource batch Value Priority
  synergy : FulfilledServiceSynergy request provider consumer
    providerState consumerState
  providerPosition : Fin batch.length
  consumerPosition : Fin batch.length
  distinctPositions : providerPosition ≠ consumerPosition
  providerCarriesFulfillment :
    fulfillmentOf (batch.get providerPosition) =
      some synergy.synergy.occurrence
  providerIsBackground :
    attention.role providerPosition = .background
  consumerIsForeground :
    attention.role consumerPosition = .foreground

namespace ServiceWave

variable {RequestId : Type uId} {Actor : Type uActor}
variable {horizon : ImportanceHorizon} {Currency : Type uCurrency}
variable [AddCommMonoid Currency]
variable {Source Target : Type uDomain}
variable {request : ServiceRequest RequestId Actor horizon Currency Source Target}
variable {Item : Type uItem} {Guard : Type uGuard}
variable {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {fulfillmentOf : Item → Option request.Fulfillment}
variable {provider consumer : Process Actor Bool request.Fulfillment}
variable {providerState consumerState : Bool}
variable {contract : Contract Item Guard CandidateView}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {shortDemand : Item → Fund .shortTerm Actor Currency}
variable {longDemand : Item → Fund .longTerm Actor Currency}
variable {shortSource : Fund .shortTerm Actor Currency}
variable {longSource : Fund .longTerm Actor Currency}
variable {batch : List Item}
variable {Value : Type uValue} {Priority : Type uPriority}

/-- The linked fulfillment is an actual assisted successor for the foreground
consumer, not merely a scheduled or valued proposal. -/
theorem assistedSuccessor
    (wave : ServiceWave request fulfillmentOf provider consumer providerState
      consumerState contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    Nonempty (Sigma fun occurrence : request.Fulfillment =>
      Sigma fun target : Bool =>
        consumer.Consumes consumerState occurrence target) :=
  wave.synergy.synergy.escapes_stuck_state

/-- The exact provider position remains in the guided occurrence ledger and
still carries the fulfillment used by the synergy proof. -/
theorem providerFulfillment_retained
    (wave : ServiceWave request fulfillmentOf provider consumer providerState
      consumerState contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    ∃ guided ∈ wave.attention.guidedPositions,
      guided.occurrence = wave.providerPosition ∧
        fulfillmentOf (batch.get guided.occurrence) =
          some wave.synergy.synergy.occurrence := by
  refine ⟨⟨wave.providerPosition,
      wave.attention.guidance.priority wave.providerPosition⟩, ?_, rfl, ?_⟩
  · simp [AttentionGuidedMindAgentWave.Wave.guidedPositions,
      AttentionGuidedMindAgentWave.Wave.positions, advise]
  · exact wave.providerCarriesFulfillment

/-- Replace advisory values without changing the service witness or any
execution/resource certificate. -/
def withGuidance
    (wave : ServiceWave request fulfillmentOf provider consumer providerState
      consumerState contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority)
    (replacement : Guidance (Fin batch.length) Value Priority) :
    ServiceWave request fulfillmentOf provider consumer providerState
      consumerState contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority where
  attention := wave.attention.withGuidance replacement
  synergy := wave.synergy
  providerPosition := wave.providerPosition
  consumerPosition := wave.consumerPosition
  distinctPositions := wave.distinctPositions
  providerCarriesFulfillment := wave.providerCarriesFulfillment
  providerIsBackground := wave.providerIsBackground
  consumerIsForeground := wave.consumerIsForeground

/-- Reprioritization changes neither the proof-relevant fulfillment nor the
observation-derived activation plan. -/
theorem withGuidance_preserves_service_and_plan
    (wave : ServiceWave request fulfillmentOf provider consumer providerState
      consumerState contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority)
    (replacement : Guidance (Fin batch.length) Value Priority)
    (branchAuthority : BranchAuthority) :
    (wave.withGuidance replacement).synergy.synergy.occurrence =
        wave.synergy.synergy.occurrence ∧
      (wave.withGuidance replacement).attention.certified.plan
          branchAuthority =
        wave.attention.certified.plan branchAuthority :=
  ⟨rfl, wave.attention.plan_withGuidance replacement branchAuthority⟩

end ServiceWave

/-! ## A concrete background-provider / foreground-consumer canary -/

namespace Canary

open Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy.Canary
open Mettapedia.CognitiveArchitecture.CognitiveSynergy.Canary

structure ServiceTask where
  occurrenceId : Nat
  actor : Actor

def providerTask : ServiceTask := ⟨0, .analyst⟩
def consumerTask : ServiceTask := ⟨1, .planner⟩
def batch : List ServiceTask := [providerTask, consumerTask]

def fulfillmentOf (task : ServiceTask) : Option firstRequest.Fulfillment :=
  if task.occurrenceId = 0 then some serviceCompletion else none

def contract : Contract ServiceTask Unit (Multiset ServiceTask) where
  observer := { observe := fun tasks => (tasks : Multiset ServiceTask) }
  demand := { completion := .completeBag }

def run (source : Multiset ServiceTask) (tasks : List ServiceTask)
    (target : Multiset ServiceTask) : Prop :=
  target = source + (tasks : Multiset ServiceTask)

def semantics :
    ExecutionSemantics ServiceTask (Multiset ServiceTask)
      (Multiset ServiceTask) where
  run := run
  observe := id

def unitFund (horizon : ImportanceHorizon) (actor : Actor) :
    Fund horizon Actor Currency where
  balances := Finsupp.single actor 1

def shortDemand (task : ServiceTask) : Fund .shortTerm Actor Currency :=
  unitFund .shortTerm task.actor

def longDemand (task : ServiceTask) : Fund .longTerm Actor Currency :=
  unitFund .longTerm task.actor

def shortSource : Fund .shortTerm Actor Currency :=
  batchDemand shortDemand batch

def longSource : Fund .longTerm Actor Currency :=
  batchDemand longDemand batch

def shortSeparation :
    BatchSeparation (Fund .shortTerm Actor Currency)
      shortDemand shortSource batch where
  frame := 0
  source_eq := by simp [shortSource]

def longSeparation :
    BatchSeparation (Fund .longTerm Actor Currency)
      longDemand longSource batch where
  frame := 0
  source_eq := by simp [longSource]

def certified : CertifiedBatch contract semantics 0
    (batch : Multiset ServiceTask)
    (ImportanceAccount Actor Currency)
    (fun task => (shortDemand task, longDemand task))
    (shortSource, longSource) batch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · rfl
    · intro ordering permutation
      refine ⟨(ordering : Multiset ServiceTask), rfl, ?_⟩
      exact Quot.sound permutation
  resources := pairFunding shortSeparation longSeparation

def role (occurrence : Fin batch.length) : AttentionGuidedMindAgentWave.WorkRole :=
  if occurrence.val = 0 then .background else .foreground

def guidance : Guidance (Fin batch.length) Nat Nat where
  value occurrence :=
    if occurrence.val = 0 then some 8 else some 5
  priorityOf := id
  fallback _ := 0

def attention : AttentionGuidedMindAgentWave.Wave contract semantics 0
    (batch : Multiset ServiceTask) shortDemand longDemand shortSource
    longSource batch Nat Nat where
  certified := certified
  role := role
  guidance := guidance
  foregroundPresent := ⟨⟨1, by decide⟩, rfl⟩
  backgroundPresent := ⟨⟨0, by decide⟩, rfl⟩

def serviceWave : ServiceWave firstRequest fulfillmentOf provider consumer
    false false contract semantics 0 (batch : Multiset ServiceTask)
    shortDemand longDemand shortSource longSource batch Nat Nat where
  attention := attention
  synergy := fulfilledSynergy
  providerPosition := ⟨0, by decide⟩
  consumerPosition := ⟨1, by decide⟩
  distinctPositions := by decide
  providerCarriesFulfillment := rfl
  providerIsBackground := rfl
  consumerIsForeground := rfl

/-- Positive control: a funded, serializable background service occurrence is
retained exactly and supplies an assisted successor to the stuck foreground
consumer. -/
theorem background_service_unsticks_foreground :
    consumer.Stuck false ∧
      Nonempty (Sigma fun occurrence : firstRequest.Fulfillment =>
        Sigma fun target : Bool => consumer.Consumes false occurrence target) ∧
      (attention.certified.plan .general).activation = .bulk ∧
      (∃ guided ∈ attention.guidedPositions,
        guided.occurrence = serviceWave.providerPosition ∧
          fulfillmentOf (batch.get guided.occurrence) =
            some serviceWave.synergy.synergy.occurrence) :=
  ⟨synergy.consumerStuck, serviceWave.assistedSuccessor,
    attention.completeBag_dispatches_bulk rfl,
    serviceWave.providerFulfillment_retained⟩

def reversedGuidance : Guidance (Fin batch.length) Nat Nat where
  value occurrence :=
    if occurrence.val = 0 then none else some 100
  priorityOf := id
  fallback _ := 0

/-- Negative authority control: making the consumer much more salient does
not alter the fulfillment witness or manufacture a new wave plan. -/
theorem reprioritization_preserves_service_and_plan :
    (serviceWave.withGuidance reversedGuidance).synergy.synergy.occurrence =
        serviceWave.synergy.synergy.occurrence ∧
      (serviceWave.withGuidance reversedGuidance).attention.certified.plan
          .general = attention.certified.plan .general :=
  serviceWave.withGuidance_preserves_service_and_plan
    reversedGuidance .general

/-- Negative channel control: a licensed attention wave does not bypass an
opaque occurrence channel. -/
theorem licensed_wave_does_not_cross_opaque_channel :
    Nonempty
        (AttentionGuidedMindAgentWave.Wave contract semantics 0
          (batch : Multiset ServiceTask) shortDemand longDemand shortSource
          longSource batch Nat Nat) ∧
      IsEmpty (ChannelWitness provider consumer sealedChannel false false) :=
  ⟨⟨attention⟩, opaque_channel_blocks_service_synergy⟩

end Canary

#print axioms ServiceWave.assistedSuccessor
#print axioms ServiceWave.providerFulfillment_retained
#print axioms ServiceWave.withGuidance_preserves_service_and_plan
#print axioms Canary.background_service_unsticks_foreground
#print axioms Canary.reprioritization_preserves_service_and_plan
#print axioms Canary.licensed_wave_does_not_cross_opaque_channel

end
end Mettapedia.CognitiveArchitecture.CognitiveSynergyWave
