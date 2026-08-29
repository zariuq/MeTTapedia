import Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
import Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

/-!
# Triggered mind-agents as space-activation policies

This module embeds the triggered background-service semantics into the generic
space-activation capability order.  A trigger occurrence authorizes generation
of one exact epoch-indexed work receipt; residency alone does not.  Binary
communication remains a separate capability.

The clock is the visible store of this bridge.  Trigger firing does not advance
it: advancing an external trace, admitting generated work into a frontier, and
selecting that work are deliberately separate transitions.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.TriggeredSpaceActivationPolicy

noncomputable section

open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

universe uTrigger uResident uActor uCurrency

/-- A triggered service space contributes only the explicit-request fragment
of the generic activation algebra. -/
def ofTriggeredSpace
    {Trigger : Type uTrigger} {Resident : Type uResident}
    (space : Space Trigger Resident) (trace : Space.TriggerTrace Trigger) :
    Policy Nat Resident Trigger Nat
      (TriggeredOccurrence Trigger Resident) where
  resident _cycle resident := space.resident resident
  enabled cycle cause :=
    match cause with
    | .requested trigger resident =>
        trace cycle = some trigger ∧ space.enabled trigger resident
    | .communication _sender _receiver => False
  step cycle cause next receipt :=
    match cause with
    | .requested trigger resident =>
        trace cycle = some trigger ∧
          space.enabled trigger resident ∧
          next = cycle ∧
          receipt = Space.occurrenceAt cycle trigger resident
    | .communication _sender _receiver => False
  step_enabled := by
    intro cycle cause next receipt step
    cases cause with
    | requested trigger resident => exact ⟨step.1, step.2.1⟩
    | communication sender receiver => exact step.elim
  enabled_supported := by
    intro cycle cause enabled
    cases cause with
    | requested trigger resident =>
        exact space.enabled_resident trigger resident enabled.2
    | communication sender receiver => exact enabled.elim
  observe := id

theorem canFire_requested_iff
    {Trigger : Type uTrigger} {Resident : Type uResident}
    (space : Space Trigger Resident) (trace : Space.TriggerTrace Trigger)
    (cycle : Nat) (trigger : Trigger) (resident : Resident) :
    (ofTriggeredSpace space trace).CanFire cycle
        (.requested trigger resident) ↔
      trace cycle = some trigger ∧ space.enabled trigger resident := by
  constructor
  · rintro ⟨next, receipt, fired⟩
    exact ⟨fired.1, fired.2.1⟩
  · rintro ⟨triggerAt, enabled⟩
    exact ⟨cycle, Space.occurrenceAt cycle trigger resident,
      triggerAt, enabled, rfl, rfl⟩

/-- The transition receipt is exactly a generated triggered occurrence. -/
theorem fired_receipt_is_generated
    {Trigger : Type uTrigger} {Resident : Type uResident}
    {space : Space Trigger Resident} {trace : Space.TriggerTrace Trigger}
    {cycle next : Nat} {trigger : Trigger} {resident : Resident}
    {receipt : TriggeredOccurrence Trigger Resident}
    (fired :
      (ofTriggeredSpace space trace).step cycle
        (.requested trigger resident) next receipt) :
    space.Generated trace cycle receipt := by
  rcases fired with ⟨triggerAt, enabled, _nextIsCycle, receiptIsExact⟩
  subst receipt
  exact space.generated_occurrenceAt trace cycle trigger resident
    triggerAt enabled

/-- Conversely, every generated occurrence has an exact activation transition.
This is generation adequacy, not a scheduler or store-admission theorem. -/
theorem generated_has_activation
    {Trigger : Type uTrigger} {Resident : Type uResident}
    {space : Space Trigger Resident} {trace : Space.TriggerTrace Trigger}
    {cycle : Nat} {occurrence : TriggeredOccurrence Trigger Resident}
    (generated : space.Generated trace cycle occurrence) :
    (ofTriggeredSpace space trace).step cycle
      (.requested occurrence.trigger occurrence.resident) cycle occurrence := by
  rcases occurrence with ⟨generatedAt, trigger, resident⟩
  change generatedAt = cycle ∧
    trace cycle = some trigger ∧ space.enabled trigger resident at generated
  rcases generated with ⟨generatedAtIsCycle, triggerAt, enabled⟩
  subst generatedAt
  exact ⟨triggerAt, enabled, rfl, rfl⟩

/-- Triggered generation grants no binary communication capability. -/
theorem no_communication_fire
    {Trigger : Type uTrigger} {Resident : Type uResident}
    (space : Space Trigger Resident) (trace : Space.TriggerTrace Trigger)
    (cycle : Nat) (sender receiver : Resident) :
    ¬ (ofTriggeredSpace space trace).CanFire cycle
        (.communication sender receiver) := by
  rintro ⟨next, receipt, fired⟩
  exact fired

/-- Recurring trigger coverage becomes recurring availability of exact
activation transitions.  Selection still requires the independent scheduler
premise in `BoundedGeneratedSelection`. -/
theorem recurringCoverage_has_activation
    {Trigger : Type uTrigger} {Resident : Type uResident}
    {Actor : Type uActor} {Currency : Type uCurrency}
    [Zero Currency] [LE Currency]
    {economy : AttentionEconomy.Economy Actor Currency} {floor : Currency}
    {triggerWindow : Nat}
    {space : Space Trigger Resident} {trace : Space.TriggerTrace Trigger}
    {residentOwner : Resident → Actor}
    (coverage : RecurringTriggerCoverage economy floor triggerWindow
      space trace residentOwner) :
    ∀ actor, economy.LongTermProtected floor actor →
      ∀ (start : Nat), ∃ (offset : Nat) (trigger : Trigger) (resident : Resident),
        offset < triggerWindow ∧
          residentOwner resident = actor ∧
          (ofTriggeredSpace space trace).CanFire (start + offset)
            (.requested trigger resident) := by
  intro actor isProtected start
  obtain ⟨offset, trigger, resident, beforeDeadline, triggerAt, enabled, owned⟩ :=
    coverage.covers actor isProtected start
  exact ⟨offset, trigger, resident, beforeDeadline, owned,
    (canFire_requested_iff space trace (start + offset) trigger resident).2
      ⟨triggerAt, enabled⟩⟩

/-! ## Concrete recurring-service controls -/

namespace Canary

open TriggeredMindAgentSpace.ServiceCanary

def servicePolicy := ofTriggeredSpace serviceSpace heartbeatTrace

def dataView : Policy Nat Resident Trigger Nat Occurrence :=
  Policy.inert servicePolicy.resident servicePolicy.observe

theorem data_is_below_triggered : dataView.Extends servicePolicy :=
  Policy.inert_extends servicePolicy

theorem heartbeat_activates_provider (cycle : Nat) :
    servicePolicy.CanFire cycle (.requested () providerPosition) :=
  (canFire_requested_iff serviceSpace heartbeatTrace cycle ()
    providerPosition).2 ⟨rfl, rfl⟩

theorem heartbeat_receipt_is_exact (cycle : Nat) :
    servicePolicy.step cycle (.requested () providerPosition) cycle
      (Space.occurrenceAt cycle () providerPosition) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem silence_refuses_provider (cycle : Nat) :
    ¬ (ofTriggeredSpace serviceSpace silentTrace).CanFire cycle
      (.requested () providerPosition) := by
  rw [canFire_requested_iff serviceSpace silentTrace cycle () providerPosition]
  simp [silentTrace]

theorem heartbeat_does_not_authorize_communication (cycle : Nat) :
    ¬ servicePolicy.CanFire cycle
      (.communication providerPosition providerPosition) :=
  no_communication_fire serviceSpace heartbeatTrace cycle
    providerPosition providerPosition

end Canary

#print axioms canFire_requested_iff
#print axioms fired_receipt_is_generated
#print axioms generated_has_activation
#print axioms no_communication_fire
#print axioms recurringCoverage_has_activation
#print axioms Canary.data_is_below_triggered
#print axioms Canary.heartbeat_activates_provider
#print axioms Canary.heartbeat_receipt_is_exact
#print axioms Canary.silence_refuses_provider
#print axioms Canary.heartbeat_does_not_authorize_communication

end
end Mettapedia.CognitiveArchitecture.TriggeredSpaceActivationPolicy
