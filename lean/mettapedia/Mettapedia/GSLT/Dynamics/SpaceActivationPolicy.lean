import Mathlib.Tactic

/-!
# Composable activation capabilities over one space substrate

Space residency does not determine execution.  This module presents explicit
activation causes and a small capability order over policies sharing one store,
resident relation, and observation.

An explicit trigger/rewrite cause and a binary communication cause are distinct
constructors.  An inert data view contributes neither.  Compatible policies
join by disjunction of their enabling and transition relations, so evaluation
and rho-style communication may coexist without creating a second store or a
closed enumeration of space kinds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

universe uTrigger uOccurrence uStore uObservation uReceipt

/-- Authored reasons why resident work may become active. -/
inductive Cause (Trigger : Type uTrigger) (Occurrence : Type uOccurrence) where
  | requested (trigger : Trigger) (occurrence : Occurrence)
  | communication (sender receiver : Occurrence)
deriving DecidableEq, Repr

namespace Cause

/-- Every occurrence named by an enabled cause must be resident. -/
def Supported {Trigger : Type uTrigger} {Occurrence : Type uOccurrence}
    {Store : Type uStore}
    (resident : Store → Occurrence → Prop) (store : Store) :
    Cause Trigger Occurrence → Prop
  | .requested _ occurrence => resident store occurrence
  | .communication sender receiver =>
      resident store sender ∧ resident store receiver

end Cause

/-- One authored activation fragment over a visible occurrence substrate. -/
structure Policy
    (Store : Type uStore) (Occurrence : Type uOccurrence)
    (Trigger : Type uTrigger) (Observation : Type uObservation)
    (Receipt : Type uReceipt) where
  resident : Store → Occurrence → Prop
  enabled : Store → Cause Trigger Occurrence → Prop
  step : Store → Cause Trigger Occurrence → Store → Receipt → Prop
  step_enabled : ∀ {store cause next receipt},
    step store cause next receipt → enabled store cause
  enabled_supported : ∀ {store cause},
    enabled store cause → cause.Supported resident store
  observe : Store → Observation

namespace Policy

variable {Store : Type uStore} {Occurrence : Type uOccurrence}
variable {Trigger : Type uTrigger} {Observation : Type uObservation}
variable {Receipt : Type uReceipt}

/-- One exact enabled transition exists. -/
def CanFire
    (policy : Policy Store Occurrence Trigger Observation Receipt)
    (store : Store) (cause : Cause Trigger Occurrence) : Prop :=
  ∃ next receipt, policy.step store cause next receipt

/-- Policy comparison ignores activation but fixes the visible substrate. -/
def SameVisibleSubstrate
    (first second : Policy Store Occurrence Trigger Observation Receipt) : Prop :=
  (∀ store occurrence,
      first.resident store occurrence ↔ second.resident store occurrence) ∧
    (∀ store, first.observe store = second.observe store)

theorem SameVisibleSubstrate.refl
    (policy : Policy Store Occurrence Trigger Observation Receipt) :
    policy.SameVisibleSubstrate policy :=
  ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩

theorem SameVisibleSubstrate.symm
    {first second : Policy Store Occurrence Trigger Observation Receipt}
    (same : first.SameVisibleSubstrate second) :
    second.SameVisibleSubstrate first :=
  ⟨fun store occurrence => (same.1 store occurrence).symm,
    fun store => (same.2 store).symm⟩

/-- `extension` retains the visible substrate and every enabling/transition
capability of `base`. -/
structure Extends
    (base extension : Policy Store Occurrence Trigger Observation Receipt) : Prop where
  sameVisible : base.SameVisibleSubstrate extension
  enabled : ∀ {store cause}, base.enabled store cause → extension.enabled store cause
  step : ∀ {store cause next receipt},
    base.step store cause next receipt →
      extension.step store cause next receipt

theorem Extends.refl
    (policy : Policy Store Occurrence Trigger Observation Receipt) :
    policy.Extends policy where
  sameVisible := SameVisibleSubstrate.refl policy
  enabled := id
  step := id

theorem Extends.trans
    {first second third :
      Policy Store Occurrence Trigger Observation Receipt}
    (firstSecond : first.Extends second)
    (secondThird : second.Extends third) :
    first.Extends third where
  sameVisible := by
    constructor
    · intro store occurrence
      exact (firstSecond.sameVisible.1 store occurrence).trans
        (secondThird.sameVisible.1 store occurrence)
    · intro store
      exact (firstSecond.sameVisible.2 store).trans
        (secondThird.sameVisible.2 store)
  enabled enabled := secondThird.enabled (firstSecond.enabled enabled)
  step step := secondThird.step (firstSecond.step step)

/-- A data-only view retains and observes occurrences but authorizes no
activation. -/
def inert
    (resident : Store → Occurrence → Prop) (observe : Store → Observation) :
    Policy Store Occurrence Trigger Observation Receipt where
  resident := resident
  enabled := fun _store _cause => False
  step := fun _store _cause _next _receipt => False
  step_enabled step := step.elim
  enabled_supported enabled := enabled.elim
  observe := observe

theorem inert_extends
    (policy : Policy Store Occurrence Trigger Observation Receipt) :
    (inert policy.resident policy.observe).Extends policy where
  sameVisible := ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩
  enabled enabled := enabled.elim
  step step := step.elim

/-- Compatible policy fragments share residency and observation. -/
abbrev Compatible
    (first second : Policy Store Occurrence Trigger Observation Receipt) :=
  first.SameVisibleSubstrate second

/-- Join two compatible capability fragments over the first fragment's
physical substrate.  No occurrence or transition is synthesized. -/
def join
    (first second : Policy Store Occurrence Trigger Observation Receipt)
    (compatible : first.Compatible second) :
    Policy Store Occurrence Trigger Observation Receipt where
  resident := first.resident
  enabled store cause := first.enabled store cause ∨ second.enabled store cause
  step store cause next receipt :=
    first.step store cause next receipt ∨ second.step store cause next receipt
  step_enabled := by
    intro store cause next receipt step
    cases step with
    | inl firstStep => exact Or.inl (first.step_enabled firstStep)
    | inr secondStep => exact Or.inr (second.step_enabled secondStep)
  enabled_supported := by
    intro store cause enabled
    cases enabled with
    | inl firstEnabled => exact first.enabled_supported firstEnabled
    | inr secondEnabled =>
        have supported := second.enabled_supported secondEnabled
        cases cause with
        | requested trigger occurrence =>
            exact (compatible.1 store occurrence).mpr supported
        | communication sender receiver =>
            exact ⟨(compatible.1 store sender).mpr supported.1,
              (compatible.1 store receiver).mpr supported.2⟩
  observe := first.observe

theorem extends_join_left
    (first second : Policy Store Occurrence Trigger Observation Receipt)
    (compatible : first.Compatible second) :
    first.Extends (join first second compatible) where
  sameVisible := ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩
  enabled enabled := Or.inl enabled
  step step := Or.inl step

theorem extends_join_right
    (first second : Policy Store Occurrence Trigger Observation Receipt)
    (compatible : first.Compatible second) :
    second.Extends (join first second compatible) where
  sameVisible := by
    constructor
    · intro store occurrence
      exact (compatible.1 store occurrence).symm
    · intro store
      exact (compatible.2 store).symm
  enabled enabled := Or.inr enabled
  step step := Or.inr step

end Policy

/-! ## Data, evaluation, and communication canaries -/

namespace Canary

inductive Atom where
  | thunk
  | send
  | receive
  | result
deriving DecidableEq, Repr

inductive Receipt where
  | evaluated
  | communicated
deriving DecidableEq, Repr

abbrev Store := List Atom
abbrev Activation := Cause Unit Atom

def resident (store : Store) (atom : Atom) : Prop := atom ∈ store

def data : Policy Store Atom Unit Store Receipt :=
  Policy.inert resident id

def evaluation : Policy Store Atom Unit Store Receipt where
  resident := resident
  enabled store cause :=
    cause = .requested () .thunk ∧ .thunk ∈ store
  step store cause next receipt :=
    store = [.thunk] ∧
      cause = .requested () .thunk ∧
      next = [.result] ∧
      receipt = .evaluated
  step_enabled step := ⟨step.2.1, by simp [step.1]⟩
  enabled_supported enabled := by
    simpa [Cause.Supported, resident, enabled.1] using enabled.2
  observe := id

def communication : Policy Store Atom Unit Store Receipt where
  resident := resident
  enabled store cause :=
    cause = .communication .send .receive ∧
      .send ∈ store ∧ .receive ∈ store
  step store cause next receipt :=
    store = [.send, .receive] ∧
      cause = .communication .send .receive ∧
      next = [.result] ∧
      receipt = .communicated
  step_enabled step := by
    refine ⟨step.2.1, ?_, ?_⟩ <;> simp [step.1]
  enabled_supported enabled := by
    simpa [Cause.Supported, resident, enabled.1] using enabled.2
  observe := id

def evaluationCommunicationCompatible :
    evaluation.Compatible communication :=
  ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩

def combined : Policy Store Atom Unit Store Receipt :=
  Policy.join evaluation communication evaluationCommunicationCompatible

theorem data_is_below_evaluation : data.Extends evaluation :=
  Policy.inert_extends evaluation

theorem data_is_below_communication : data.Extends communication :=
  Policy.inert_extends communication

theorem evaluation_is_below_combined : evaluation.Extends combined :=
  Policy.extends_join_left evaluation communication
    evaluationCommunicationCompatible

theorem communication_is_below_combined : communication.Extends combined :=
  Policy.extends_join_right evaluation communication
    evaluationCommunicationCompatible

theorem evaluation_can_fire :
    evaluation.step [.thunk] (.requested () .thunk) [.result] .evaluated :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem communication_can_fire :
    communication.step [.send, .receive]
      (.communication .send .receive) [.result] .communicated :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Explicit evaluation cannot be reinterpreted as communication while
preserving the same exact transition. -/
theorem evaluation_not_below_communication :
    ¬ evaluation.Extends communication := by
  intro extension
  have impossible := extension.step evaluation_can_fire
  simp [communication] at impossible

/-- Communication likewise cannot be reinterpreted as a unary evaluation
request. -/
theorem communication_not_below_evaluation :
    ¬ communication.Extends evaluation := by
  intro extension
  have impossible := extension.step communication_can_fire
  simp [evaluation] at impossible

theorem combined_supports_both :
    combined.step [.thunk] (.requested () .thunk) [.result] .evaluated ∧
      combined.step [.send, .receive]
        (.communication .send .receive) [.result] .communicated :=
  ⟨Or.inl evaluation_can_fire, Or.inr communication_can_fire⟩

theorem data_cannot_fire (store : Store) (cause : Activation) :
    ¬ data.CanFire store cause := by
  rintro ⟨next, receipt, step⟩
  exact step

end Canary

#print axioms Policy.Extends.trans
#print axioms Policy.inert_extends
#print axioms Policy.extends_join_left
#print axioms Policy.extends_join_right
#print axioms Canary.evaluation_not_below_communication
#print axioms Canary.communication_not_below_evaluation
#print axioms Canary.combined_supports_both
#print axioms Canary.data_cannot_fire

end Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
