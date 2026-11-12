import Mettapedia.Machines.ProgressRestriction

set_option autoImplicit false

namespace Mettapedia.Machines.ProgressObservation.RestrictionControls

inductive State where
  | good
  | bad

inductive Event : State → State → Type
  | pulse : Event .good .good
  | escape : Event .good .bad
  | spin : Event .bad .bad

instance quiver : Quiver State := ⟨Event⟩

def read : Observation State ℕ
  | _, _, .pulse => some 0
  | _, _, .escape | _, _, .spin => none

def domain (state : State) : Prop := state = .good

theorem domain_is_not_closed : ¬ DomainClosed domain := by
  intro closed
  have impossible := closed (a := .good) rfl Event.escape
  cases impossible

local instance : Quiver {state : State // domain state} := restrictedQuiver domain

theorem every_restricted_event_is_observed {a b : {state : State // domain state}} (event : a ⟶ b) :
    ((restrictedObservation read domain) event).isSome = true := by
  obtain ⟨a, first⟩ := a
  obtain ⟨b, last⟩ := b
  change a = .good at first
  change b = .good at last
  subst a
  subst b
  cases event
  rfl

theorem restricted_progress : NonZeno (restrictedObservation read domain) :=
  fun execution start => ⟨start, Nat.le_refl _, every_restricted_event_is_observed (execution.event start)⟩

def escaping : Execution State where
  state n := if n = 0 then .good else .bad
  event n := by
    cases n with
    | zero => exact .escape
    | succ n => exact .spin

theorem starts_in_domain : domain (escaping.state 0) := rfl

theorem escaping_erased (n : ℕ) : read (escaping.event n) = none := by
  cases n <;> rfl

/-- Filtering away bad states is insufficient unless the original events stay in the domain. -/
theorem restriction_without_closure_conceals_divergence :
    NonZeno (restrictedObservation read domain) ∧ domain (escaping.state 0) ∧
      ¬ (∀ start : ℕ, ∃ n, start ≤ n ∧ (read (escaping.event n)).isSome = true) := by
  refine ⟨restricted_progress, starts_in_domain, ?_⟩
  intro progress
  obtain ⟨n, _, observed⟩ := progress 0
  simp [escaping_erased n] at observed

end Mettapedia.Machines.ProgressObservation.RestrictionControls
