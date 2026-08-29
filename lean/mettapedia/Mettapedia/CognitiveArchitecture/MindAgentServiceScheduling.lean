import Mettapedia.CognitiveArchitecture.CognitiveSynergyWave
import Mettapedia.GSLT.Core.AgePrioritySchedule
import Mettapedia.GSLT.Core.SearchControlProperties

/-!
# Occurrence-fair and recurrent scheduling for cognitive services

An attention-guided service wave licenses one finite foreground/background
batch.  An age-protected priority portfolio can ensure that every occurrence
in that batch is eventually selected.  Long-term ECAN protection is stronger:
it requires a provider to be scheduled again in every bounded window.  A
one-shot finite batch cannot supply that recurrence by itself.

This module connects the finite service-wave positions to the existing
age-priority theorem, then states the additional occurrence-supply condition
which is sufficient for bounded LTI scheduling.  Selection, payment, and
proof-relevant service fulfillment remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
open Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy
open Mettapedia.CognitiveArchitecture.CognitiveSynergy
open Mettapedia.CognitiveArchitecture.CognitiveSynergyWave
open Mettapedia.GSLT.Core.AgePrioritySchedule
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Dynamics.ContextualControlSurface
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uId uActor uCurrency uDomain
universe uItem uGuard uCandidateView uState uStateView uValue uPriority
universe uOccurrence

/-! ## Finite occurrence fairness for one service wave -/

/-- A finite batch viewed only as exact positional work occurrences.  Selecting
a position emits that position and creates no successors.  This isolates the
scheduling obligation from the service semantics connected to the position. -/
def positionSystem {Item : Type uItem} (batch : List Item) :
    BranchingSystem (Fin batch.length) (Fin batch.length) where
  emit occurrence := some occurrence
  successors _ := []

/-- Every positional occurrence is initially live exactly once. -/
def positionRoots {Item : Type uItem} (batch : List Item) :
    List (Fin batch.length) :=
  List.finRange batch.length

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

/-- A genuine priority portfolio with a separate FIFO age lane eventually
selects both exact service positions.  It does not claim that either selected
task has completed. -/
theorem positions_eventually_selected
    {laneCount : Nat} [NeZero laneCount]
    (wave : CognitiveSynergyWave.ServiceWave request fulfillmentOf provider
      consumer providerState consumerState contract semantics initial
      referenceTarget shortDemand longDemand shortSource longSource batch
      Value Priority)
    (portfolio : Mettapedia.GSLT.Core.AgePrioritySchedule.Spec
      (Fin batch.length) laneCount)
    (start : Fin laneCount) :
    (∃ fuel,
      wave.providerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          portfolio.schedule.disciplines fuel
          (portfolio.initial (Answer := Fin batch.length)
            (positionRoots batch) start)).selections) ∧
    (∃ fuel,
      wave.consumerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          portfolio.schedule.disciplines fuel
          (portfolio.initial (Answer := Fin batch.length)
            (positionRoots batch) start)).selections) := by
  constructor
  · exact portfolio.eventually_selects_root (positionSystem batch)
      (positionRoots batch) start (by simp [positionRoots])
  · exact portfolio.eventually_selects_root (positionSystem batch)
      (positionRoots batch) start (by simp [positionRoots])

/-- Any genuine occurrence-preserving priority field may be paired with an age
lane without endangering either service position. -/
theorem pairedPriority_positions_eventually_selected
    (wave : CognitiveSynergyWave.ServiceWave request fulfillmentOf provider
      consumer providerState consumerState contract semantics initial
      referenceTarget shortDemand longDemand shortSource longSource batch
      Value Priority)
    (priority : PriorityField (Fin batch.length)) :
    (∃ fuel,
      wave.providerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          (Mettapedia.GSLT.Core.AgePrioritySchedule.paired priority).schedule.disciplines fuel
          ((Mettapedia.GSLT.Core.AgePrioritySchedule.paired priority).initial
            (Answer := Fin batch.length) (positionRoots batch) 0)).selections) ∧
    (∃ fuel,
      wave.consumerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          (Mettapedia.GSLT.Core.AgePrioritySchedule.paired priority).schedule.disciplines fuel
          ((Mettapedia.GSLT.Core.AgePrioritySchedule.paired priority).initial
            (Answer := Fin batch.length) (positionRoots batch) 0)).selections) :=
  positions_eventually_selected wave
    (Mettapedia.GSLT.Core.AgePrioritySchedule.paired priority) 0

/-- Replacing every advisory value leaves the same two positional liveness
obligations provable.  The priority portfolio is a separate argument rather
than authority reconstructed from the values. -/
theorem guidance_change_preserves_position_fairness
    {laneCount : Nat} [NeZero laneCount]
    (wave : CognitiveSynergyWave.ServiceWave request fulfillmentOf provider
      consumer providerState consumerState contract semantics initial
      referenceTarget shortDemand longDemand shortSource longSource batch
      Value Priority)
    (replacement : Guidance (Fin batch.length) Value Priority)
    (portfolio : Mettapedia.GSLT.Core.AgePrioritySchedule.Spec
      (Fin batch.length) laneCount)
    (start : Fin laneCount) :
    (∃ fuel,
      (wave.withGuidance replacement).providerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          portfolio.schedule.disciplines fuel
          (portfolio.initial (Answer := Fin batch.length)
            (positionRoots batch) start)).selections) ∧
    (∃ fuel,
      (wave.withGuidance replacement).consumerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          portfolio.schedule.disciplines fuel
          (portfolio.initial (Answer := Fin batch.length)
            (positionRoots batch) start)).selections) :=
  positions_eventually_selected (wave.withGuidance replacement) portfolio start

end ServiceWave

/-! ## Recurrence required by long-term attention -/

/-- Turn exact selected occurrences into an actor-level scheduling relation.
The existential occurrence remains available as a scheduling receipt. -/
def scheduledFromOccurrences
    {Occurrence : Type uOccurrence} {Actor : Type uActor}
    (owner : Occurrence → Actor)
    (selected : Nat → Occurrence → Prop)
    (cycle : Nat) (actor : Actor) : Prop :=
  ∃ occurrence, selected cycle occurrence ∧ owner occurrence = actor

/-- A bounded supply of exact occurrences for every LTI-protected actor.
Unlike one finite wave, this condition quantifies over every future window. -/
structure RecurringOccurrenceCoverage
    {Occurrence : Type uOccurrence} {Actor : Type uActor}
    {Currency : Type uCurrency} [Zero Currency] [LE Currency]
    (economy : Economy Actor Currency) (floor : Currency) (window : Nat)
    (owner : Occurrence → Actor)
    (selected : Nat → Occurrence → Prop) : Prop where
  covers : ∀ actor, economy.LongTermProtected floor actor →
    ∀ start, ∃ occurrence offset,
      offset < window ∧
      owner occurrence = actor ∧
      selected (start + offset) occurrence

namespace RecurringOccurrenceCoverage

variable {Occurrence : Type uOccurrence} {Actor : Type uActor}
variable {Currency : Type uCurrency} [Zero Currency] [LE Currency]
variable {economy : Economy Actor Currency} {floor : Currency} {window : Nat}
variable {owner : Occurrence → Actor}
variable {selected : Nat → Occurrence → Prop}

/-- Bounded recurring occurrence coverage is sufficient for the exact ECAN
long-term protection contract. -/
theorem honorsLongTerm
    (coverage : RecurringOccurrenceCoverage economy floor window owner selected) :
    HonorsLongTermProtection economy floor window
      (scheduledFromOccurrences owner selected) := by
  intro actor isProtected start
  obtain ⟨occurrence, offset, beforeDeadline, owned, selectedAt⟩ :=
    coverage.covers actor isProtected start
  exact ⟨offset, beforeDeadline, occurrence, selectedAt, owned⟩

end RecurringOccurrenceCoverage

/-! ## Concrete service and recurrence canaries -/

namespace Canary

open Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy.Canary
open Mettapedia.CognitiveArchitecture.CognitiveSynergyWave.Canary

/-- A depth-biased priority view is deliberately distinct from FIFO.  The
paired age lane supplies its liveness proof. -/
def serviceDepthPriority : PriorityField (Fin batch.length) where
  discipline := QueueDiscipline.depthFirst
  distinguishesAge :=
    ⟨[serviceWave.providerPosition], [serviceWave.consumerPosition], by decide⟩

/-- Positive finite-wave control: even a depth-biased service priority cannot
starve either the background provider or foreground consumer. -/
theorem service_positions_are_occurrence_fair :
    (∃ fuel,
      serviceWave.providerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          (Mettapedia.GSLT.Core.AgePrioritySchedule.paired
            serviceDepthPriority).schedule.disciplines
          fuel
          ((Mettapedia.GSLT.Core.AgePrioritySchedule.paired
            serviceDepthPriority).initial
            (Answer := Fin batch.length) (positionRoots batch) 0)).selections) ∧
    (∃ fuel,
      serviceWave.consumerPosition ∈
        (PortfolioSnapshot.run (positionSystem batch)
          (Mettapedia.GSLT.Core.AgePrioritySchedule.paired
            serviceDepthPriority).schedule.disciplines
          fuel
          ((Mettapedia.GSLT.Core.AgePrioritySchedule.paired
            serviceDepthPriority).initial
            (Answer := Fin batch.length) (positionRoots batch) 0)).selections) :=
  ServiceWave.pairedPriority_positions_eventually_selected
    serviceWave serviceDepthPriority

/-- Dynamic service occurrences pair an epoch with an exact batch position. -/
abbrev ServiceOccurrence := Nat × Fin batch.length

def serviceOwner (occurrence : ServiceOccurrence) : Actor :=
  (batch.get occurrence.2).actor

/-- The background provider is supplied once at every cycle. -/
def recurrentProviderSelected
    (cycle : Nat) (occurrence : ServiceOccurrence) : Prop :=
  occurrence = (cycle, serviceWave.providerPosition)

def longTermServiceEconomy : Economy Actor Currency where
  shortTerm := 0
  longTerm := { balances := Finsupp.single .analyst 1 }

def recurrentProviderCoverage :
    RecurringOccurrenceCoverage longTermServiceEconomy 1 1
      serviceOwner recurrentProviderSelected where
  covers actor isProtected start := by
    have actorIsAnalyst : actor = .analyst := by
      cases actor <;>
        simp [Economy.LongTermProtected, longTermServiceEconomy]
          at isProtected ⊢
    subst actor
    exact ⟨(start, serviceWave.providerPosition), 0, by omega, rfl, rfl⟩

/-- Positive recurrent control: epoch-indexed provider occurrences discharge
the ECAN anti-starvation contract. -/
theorem recurrent_service_honors_longTerm :
    HonorsLongTermProtection longTermServiceEconomy 1 1
      (scheduledFromOccurrences serviceOwner recurrentProviderSelected) :=
  recurrentProviderCoverage.honorsLongTerm

/-- A one-shot batch selects the provider only at cycle zero. -/
def oneShotProviderSelected
    (cycle : Nat) (occurrence : ServiceOccurrence) : Prop :=
  cycle = 0 ∧ occurrence = (0, serviceWave.providerPosition)

theorem oneShot_provider_is_eventually_selected :
    ∃ cycle,
      scheduledFromOccurrences serviceOwner oneShotProviderSelected
        cycle .analyst := by
  exact ⟨0, (0, serviceWave.providerPosition), ⟨rfl, rfl⟩, rfl⟩

/-- Negative recurrence control: one eventual provider selection does not
satisfy an LTI promise over every future window. -/
theorem oneShot_does_not_honor_longTerm :
    ¬ HonorsLongTermProtection longTermServiceEconomy 1 1
      (scheduledFromOccurrences serviceOwner oneShotProviderSelected) := by
  intro honors
  have isProtected :
      longTermServiceEconomy.LongTermProtected 1 .analyst := by
    simp [Economy.LongTermProtected, longTermServiceEconomy]
  obtain ⟨offset, beforeDeadline, occurrence, selectedAt, _owned⟩ :=
    honors .analyst isProtected 1
  have offsetZero : offset = 0 := by omega
  subst offset
  simp [oneShotProviderSelected] at selectedAt

/-- Even bounded recurrent selection and funded authorization cannot turn an
unavailable schematic into a proof-relevant service occurrence. -/
theorem recurrence_and_payment_do_not_prove_service :
    HonorsLongTermProtection longTermServiceEconomy 1 1
        (scheduledFromOccurrences serviceOwner recurrentProviderSelected) ∧
      Nonempty (paidButUnavailable.payment.Redemption fund) ∧
      IsEmpty paidButUnavailable.Fulfillment :=
  ⟨recurrent_service_honors_longTerm,
    CognitiveSchematicAttentionEconomy.Canary.payment_does_not_prove_service⟩

end Canary

#print axioms ServiceWave.positions_eventually_selected
#print axioms ServiceWave.pairedPriority_positions_eventually_selected
#print axioms ServiceWave.guidance_change_preserves_position_fairness
#print axioms RecurringOccurrenceCoverage.honorsLongTerm
#print axioms Canary.service_positions_are_occurrence_fair
#print axioms Canary.recurrent_service_honors_longTerm
#print axioms Canary.oneShot_provider_is_eventually_selected
#print axioms Canary.oneShot_does_not_honor_longTerm
#print axioms Canary.recurrence_and_payment_do_not_prove_service

end
end Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling
