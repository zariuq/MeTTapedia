import Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy
import Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing

/-!
# Cognitive synergy as proof-relevant stuck-state escape

Two processes are synergistic here when one produces an exact occurrence that
lets a distinct process leave a state in which it has no autonomous step.  The
definition retains the producing process, occurrence identity, and assisted
transition.  It does not equate attention, payment, similarity, or ancestry
with semantic success.

An explicit channel mediates cross-process use.  An opaque channel admits no
delivery evidence and therefore blocks synergy, even when a useful occurrence
exists on the producer side.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.CognitiveSynergy

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy

universe uAgent uState uOccurrence uDelivery uActor uCurrency uId

/-- One cognitive process with autonomous, production, and assisted
transition families. -/
structure Process (Agent : Type uAgent) (State : Type uState)
    (Occurrence : Type uOccurrence) where
  id : Agent
  Autonomous : State → State → Type uState
  Produces : State → Occurrence → Type uOccurrence
  Consumes : State → Occurrence → State → Type uState

namespace Process

variable {Agent : Type uAgent} {State : Type uState}
variable {Occurrence : Type uOccurrence}

/-- Genuine local stuckness: there is no autonomous successor occurrence. -/
def Stuck (process : Process Agent State Occurrence) (source : State) : Prop :=
  IsEmpty (Sigma fun target => process.Autonomous source target)

end Process

/-- A distinct provider produces one exact occurrence which enables the
consumer to leave a genuinely stuck state. -/
structure Witness
    {Agent : Type uAgent} {State : Type uState}
    {Occurrence : Type uOccurrence}
    (provider consumer : Process Agent State Occurrence)
    (providerState consumerState : State) where
  distinctProcesses : provider.id ≠ consumer.id
  occurrence : Occurrence
  produced : provider.Produces providerState occurrence
  target : State
  consumerStuck : consumer.Stuck consumerState
  assisted : consumer.Consumes consumerState occurrence target

namespace Witness

variable {Agent : Type uAgent} {State : Type uState}
variable {Occurrence : Type uOccurrence}
variable {provider consumer : Process Agent State Occurrence}
variable {providerState consumerState : State}

/-- The witness exposes an actual assisted successor, not merely a score or
claim that the processes are complementary. -/
theorem escapes_stuck_state
    (witness : Witness provider consumer providerState consumerState) :
    Nonempty (Sigma fun occurrence : Occurrence =>
      Sigma fun target : State =>
        consumer.Consumes consumerState occurrence target) :=
  ⟨⟨witness.occurrence, witness.target, witness.assisted⟩⟩

end Witness

/-! ## Channel obstruction -/

/-- A proof-relevant occurrence channel.  Delivery may translate the
occurrence representation while retaining an explicit witness. -/
structure Channel (Produced : Type uOccurrence) (Delivered : Type uDelivery) where
  Delivery : Produced → Delivered → Type (max uOccurrence uDelivery)

/-- No produced occurrence can cross an opaque channel. -/
def Channel.Opaque
    {Produced : Type uOccurrence} {Delivered : Type uDelivery}
    (channel : Channel Produced Delivered) : Prop :=
  ∀ produced delivered, IsEmpty (channel.Delivery produced delivered)

/-- Synergy mediated by a channel retains both the producer occurrence and
the exact delivered occurrence consumed on the other side. -/
structure ChannelWitness
    {Agent : Type uAgent} {State : Type uState}
    {Produced : Type uOccurrence} {Delivered : Type uDelivery}
    (provider : Process Agent State Produced)
    (consumer : Process Agent State Delivered)
    (channel : Channel Produced Delivered)
    (providerState consumerState : State) where
  distinctProcesses : provider.id ≠ consumer.id
  producedOccurrence : Produced
  produced : provider.Produces providerState producedOccurrence
  deliveredOccurrence : Delivered
  delivered : channel.Delivery producedOccurrence deliveredOccurrence
  target : State
  consumerStuck : consumer.Stuck consumerState
  assisted : consumer.Consumes consumerState deliveredOccurrence target

/-- Required negative control: an opaque channel prevents every mediated
synergy witness. -/
theorem no_channel_synergy_of_opaque
    {Agent : Type uAgent} {State : Type uState}
    {Produced : Type uOccurrence} {Delivered : Type uDelivery}
    {provider : Process Agent State Produced}
    {consumer : Process Agent State Delivered}
    {channel : Channel Produced Delivered}
    (hOpaque : channel.Opaque) (providerState consumerState : State) :
    IsEmpty (ChannelWitness provider consumer channel
      providerState consumerState) := by
  constructor
  intro witness
  exact (hOpaque witness.producedOccurrence witness.deliveredOccurrence).false
    witness.delivered

/-! ## Service and scheduling interfaces -/

/-- A fulfilled service can be the occurrence that enables another process.
The occurrence type itself is the request's proof-relevant fulfillment. -/
structure FulfilledServiceSynergy
    {RequestId : Type uId} {Actor : Type uActor}
    {horizon : ImportanceHorizon} {Currency : Type uCurrency}
    {Source Target : Type uState}
    (request : ServiceRequest RequestId Actor horizon Currency Source Target)
    (provider consumer : Process Actor Bool request.Fulfillment)
    (providerState consumerState : Bool) where
  synergy : Witness provider consumer providerState consumerState

/-- Settlement is an additional economic witness.  It must name the same
fulfillment occurrence used by the synergy proof. -/
structure SettledServiceSynergy
    {RequestId : Type uId} {Actor : Type uActor}
    {horizon : ImportanceHorizon} {Currency : Type uCurrency}
    {Source Target : Type uState}
    [AddCommGroup Currency] [LE Currency]
    (request : ServiceRequest RequestId Actor horizon Currency Source Target)
    (fund : Fund horizon Actor Currency)
    (provider consumer : Process Actor Bool request.Fulfillment)
    (providerState consumerState : Bool)
    extends FulfilledServiceSynergy request provider consumer
      providerState consumerState where
  settlement : request.Settlement fund
  sameFulfillment : settlement.fulfillment = toFulfilledServiceSynergy.synergy.occurrence

/-- Scheduling is only evidence that a provider was selected at a cycle. -/
structure ScheduledAttempt
    {RequestId : Type uId} {Actor : Type uActor}
    {horizon : ImportanceHorizon} {Currency : Type uCurrency}
    {Source Target : Type uState}
    (request : ServiceRequest RequestId Actor horizon Currency Source Target)
    (scheduled : Nat → Actor → Prop) where
  cycle : Nat
  selected : scheduled cycle request.payment.beneficiary

/-- A long-term protection contract yields a bounded scheduling occurrence,
not a service result. -/
theorem longTermProtection_schedules_provider
    {Actor : Type uActor} {Currency : Type uCurrency}
    [Zero Currency] [LE Currency]
    (economy : Economy Actor Currency) (floor : Currency) (window : Nat)
    (scheduled : Nat → Actor → Prop)
    (honors : HonorsLongTermProtection economy floor window scheduled)
    (provider : Actor) (isProtected : economy.LongTermProtected floor provider)
    (start : Nat) :
    ScheduledWithin scheduled start window provider :=
  honors provider isProtected start

/-! ## Positive and negative controls -/

namespace Canary

open CognitiveSchematicAttentionEconomy.Canary

def serviceCompletion : firstRequest.Fulfillment :=
  ServiceRequest.fulfillmentOfMay firstRequest firstMay
    (source := ()) PUnit.unit

def provider : Process Actor Bool firstRequest.Fulfillment where
  id := .analyst
  Autonomous := fun _ _ => Empty
  Produces := fun _ completion => PLift (completion = serviceCompletion)
  Consumes := fun _ _ _ => Empty

def consumer : Process Actor Bool firstRequest.Fulfillment where
  id := .planner
  Autonomous := fun _ _ => Empty
  Produces := fun _ _ => Empty
  Consumes := fun source completion target =>
    PLift (source = false ∧ completion = serviceCompletion ∧ target = true)

def synergy : Witness provider consumer false false where
  distinctProcesses := by decide
  occurrence := serviceCompletion
  produced := ⟨rfl⟩
  target := true
  consumerStuck := by
    constructor
    rintro ⟨target, autonomous⟩
    exact autonomous.elim
  assisted := ⟨rfl, rfl, rfl⟩

/-- Positive control: the exact fulfillment occurrence turns a locally stuck
consumer into an assisted successor while retaining process identity. -/
theorem service_occurrence_escapes_stuck :
    consumer.Stuck false ∧
      Nonempty (Sigma fun completion : firstRequest.Fulfillment =>
        Sigma fun target : Bool => consumer.Consumes false completion target) :=
  ⟨synergy.consumerStuck, synergy.escapes_stuck_state⟩

def fulfilledSynergy :
    FulfilledServiceSynergy firstRequest provider consumer false false where
  synergy := synergy

def firstSettlement : firstRequest.Settlement fund where
  fulfillment := serviceCompletion
  redemption := firstRedemption

def settledSynergy :
    SettledServiceSynergy firstRequest fund provider consumer false false where
  synergy := synergy
  settlement := firstSettlement
  sameFulfillment := rfl

def sealedChannel :
    Channel firstRequest.Fulfillment firstRequest.Fulfillment where
  Delivery := fun _ _ => Empty

theorem opaque_channel_blocks_service_synergy :
    IsEmpty (ChannelWitness provider consumer sealedChannel false false) :=
  no_channel_synergy_of_opaque (by
    intro produced delivered
    change IsEmpty Empty
    infer_instance) false false

def scheduled (_cycle : Nat) (actor : Actor) : Prop :=
  actor = .analyst

def unavailableAttempt : ScheduledAttempt paidButUnavailable scheduled where
  cycle := 0
  selected := rfl

/-- Required attention/payment negative control: a provider may be scheduled
and its funded promise redeemable while the service remains impossible. -/
theorem scheduling_and_payment_do_not_prove_service :
    Nonempty (ScheduledAttempt paidButUnavailable scheduled) ∧
      Nonempty (paidButUnavailable.payment.Redemption fund) ∧
      IsEmpty paidButUnavailable.Fulfillment :=
  ⟨⟨unavailableAttempt⟩,
    CognitiveSchematicAttentionEconomy.Canary.payment_does_not_prove_service⟩

/-- Conversely, the service occurrence used for synergy does not itself
authorize or fund an unrelated payment. -/
theorem service_does_not_supply_payment_authority :
    Nonempty achievableButUnfunded.Fulfillment ∧
      IsEmpty (achievableButUnfunded.payment.Redemption fund) :=
  CognitiveSchematicAttentionEconomy.Canary.service_does_not_authorize_payment

end Canary

#print axioms Witness.escapes_stuck_state
#print axioms no_channel_synergy_of_opaque
#print axioms longTermProtection_schedules_provider
#print axioms Canary.service_occurrence_escapes_stuck
#print axioms Canary.opaque_channel_blocks_service_synergy
#print axioms Canary.scheduling_and_payment_do_not_prove_service

end Mettapedia.CognitiveArchitecture.CognitiveSynergy
