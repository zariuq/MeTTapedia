import Mettapedia.Machines.ProgressObservation

/-!
# Boundaries of administrative progress

The source counter and the delayed target have the same finite observations in
both directions, but the target admits an infinite erased execution. A semantic
internal event with the same endpoints remains a distinct observed event.

An infinitely branching countdown has well-founded administrative work but no
natural-number potential. Empty event fibres and an unreachable erased loop
separate progress of existing executions from existence and loaded-state claims.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProgressObservation.Controls

namespace Counter

inductive Label where
  | tick (value : ℕ)
  | semanticTau (value : ℕ)
  deriving DecidableEq

inductive Source where
  | count (value : ℕ)

inductive SourceEvent : Source → Source → Type
  | tick (value : ℕ) : SourceEvent (.count value) (.count (value + 1))
  | semanticTau (value : ℕ) : SourceEvent (.count value) (.count value)

instance sourceQuiver : Quiver Source := ⟨SourceEvent⟩

def sourceRead : Observation Source Label
  | _, _, .tick n => some (.tick n)
  | _, _, .semanticTau n => some (.semanticTau n)

inductive Target where
  | state (value : ℕ)

inductive TargetEvent : Target → Target → Type
  | delay (value : ℕ) : TargetEvent (.state value) (.state value)
  | tick (value : ℕ) : TargetEvent (.state value) (.state (value + 1))
  | semanticTau (value : ℕ) : TargetEvent (.state value) (.state value)

instance targetQuiver : Quiver Target := ⟨TargetEvent⟩

def targetRead : Observation Target Label
  | _, _, .delay _ => none
  | _, _, .tick n => some (.tick n)
  | _, _, .semanticTau n => some (.semanticTau n)

def view : Target → Source | .state n => .count n
def encode : Source → Target | .count n => .state n

def projectEvent {a b : Target} : (a ⟶ b) → Quiver.Path (view a) (view b)
  | .delay _ => .nil
  | .tick n => Quiver.Path.nil.cons (.tick n)
  | .semanticTau n => Quiver.Path.nil.cons (.semanticTau n)

def projectPath {a : Target} : {b : Target} → Quiver.Path a b → Quiver.Path (view a) (view b)
  | _, .nil => .nil
  | _, .cons path event => (projectPath path).comp (projectEvent event)

theorem project_observation {a b : Target} (path : Quiver.Path a b) :
    observePath sourceRead (projectPath path) = observePath targetRead path := by
  induction path with
  | nil => rfl
  | cons path event ih =>
      rw [projectPath, observePath_comp, ih]
      cases event <;> simp [projectEvent, observePath, targetRead, sourceRead]

def liftEvent {a b : Source} : (a ⟶ b) → (encode a ⟶ encode b)
  | .tick n => .tick n
  | .semanticTau n => .semanticTau n

def liftPath {a : Source} : {b : Source} → Quiver.Path a b → Quiver.Path (encode a) (encode b)
  | _, .nil => .nil
  | _, .cons path event => (liftPath path).cons (liftEvent event)

theorem lift_observation {a b : Source} (path : Quiver.Path a b) :
    observePath targetRead (liftPath path) = observePath sourceRead path := by
  induction path with
  | nil => rfl
  | cons path event ih =>
      cases event <;> simp [liftPath, liftEvent, observePath, targetRead, sourceRead, ih]

theorem finite_observations_iff (word : List Label) :
    (∃ last : Target, ∃ path : Quiver.Path (.state 0) last, observePath targetRead path = word) ↔
      ∃ last : Source, ∃ path : Quiver.Path (.count 0) last, observePath sourceRead path = word := by
  constructor
  · rintro ⟨last, path, observed⟩
    exact ⟨view last, projectPath path, (project_observation path).trans observed⟩
  · rintro ⟨last, path, observed⟩
    exact ⟨encode last, liftPath path, (lift_observation path).trans observed⟩

def silentExecution : Execution Target where
  state _ := .state 0
  event _ := .delay 0

theorem silent_execution_erased (n : ℕ) : targetRead (silentExecution.event n) = none := rfl

theorem finite_correspondence_does_not_imply_progress :
    (∀ word, (∃ last : Target, ∃ path : Quiver.Path (.state 0) last,
        observePath targetRead path = word) ↔
      ∃ last : Source, ∃ path : Quiver.Path (.count 0) last,
        observePath sourceRead path = word) ∧ ¬ NonZeno targetRead := by
  refine ⟨finite_observations_iff, ?_⟩
  intro progress
  obtain ⟨_, _, observed⟩ := progress silentExecution 0
  simp [silentExecution, targetRead] at observed

theorem same_endpoints_different_observations :
    TargetEvent.delay 0 ≠ TargetEvent.semanticTau 0 ∧
      targetRead (TargetEvent.delay 0) = none ∧
      targetRead (TargetEvent.semanticTau 0) = some (.semanticTau 0) := by
  refine ⟨?_, rfl, rfl⟩
  intro same
  cases same

def sourceDivergence : Execution Source where
  state _ := .count 0
  event _ := .semanticTau 0

theorem semantic_divergence_is_retained (n : ℕ) :
    sourceRead (sourceDivergence.event n) = some (.semanticTau 0) := rfl

theorem source_event_observed {a b : Source} (event : SourceEvent a b) :
    (sourceRead event).isSome = true := by cases event <;> rfl

theorem source_nonZeno : NonZeno sourceRead :=
  fun execution start => ⟨start, Nat.le_refl _, source_event_observed (execution.event start)⟩

/-- Productivity does not force a continuously enabled alternative to be chosen. -/
theorem productive_execution_can_starve_an_alternative :
    NonZeno sourceRead ∧
      (∀ n : ℕ, Nonempty (sourceDivergence.state n ⟶ Source.count 1)) ∧
      (∀ n : ℕ, sourceRead (sourceDivergence.event n) ≠ some (.tick 0)) := by
  refine ⟨source_nonZeno, fun _ => ⟨SourceEvent.tick 0⟩, ?_⟩
  intro n same
  cases same

/-- A concrete policy is productive even though the unrestricted system is not. -/
def alternating : Execution Target where
  state _ := .state 0
  event n := if n % 2 = 0 then .semanticTau 0 else .delay 0

theorem alternating_productive (start : ℕ) :
    ∃ n, start ≤ n ∧ (targetRead (alternating.event n)).isSome = true := by
  refine ⟨2 * start, by omega, ?_⟩
  simp [alternating, targetRead]

end Counter

namespace Countdown

inductive State where
  | root
  | waiting (remaining : ℕ)
  | live

inductive Event : State → State → Type
  | choose (remaining : ℕ) : Event .root (.waiting remaining)
  | decrease (remaining : ℕ) : Event (.waiting (remaining + 1)) (.waiting remaining)
  | finish : Event (.waiting 0) .live
  | tick : Event .live .live

instance quiver : Quiver State := ⟨Event⟩

def read : Observation State ℕ
  | _, _, .tick => some 0
  | _, _, .choose _ | _, _, .decrease _ | _, _, .finish => none

theorem live_accessible : Acc (fun b a => Administrative read a b) .live := by
  refine .intro _ ?_
  rintro state ⟨event, erased⟩
  cases event
  simp [read] at erased

theorem waiting_accessible (n : ℕ) : Acc (fun b a => Administrative read a b) (.waiting n) := by
  induction n with
  | zero =>
      refine .intro _ ?_
      rintro state ⟨event, _⟩
      cases event
      exact live_accessible
  | succ n ih =>
      refine .intro _ ?_
      rintro state ⟨event, _⟩
      cases event
      exact ih

theorem administrative_wellFounded : WellFounded (fun b a => Administrative read a b) := by
  constructor
  intro state
  cases state with
  | live => exact live_accessible
  | waiting n => exact waiting_accessible n
  | root =>
      refine .intro _ ?_
      rintro state ⟨event, _⟩
      cases event with
      | choose n => exact waiting_accessible n

theorem nonZeno : NonZeno read := nonZeno_of_wellFounded read administrative_wellFounded

/-- Well-foundedness does not impose a finite bound at an infinitely branching root. -/
theorem no_natural_potential :
    ¬ ∃ rank : State → ℕ, ∀ {a b : State} (event : a ⟶ b),
      read event = none → rank b < rank a := by
  rintro ⟨rank, decreases⟩
  have lower (n : ℕ) : n ≤ rank (.waiting n) := by
    induction n with
    | zero => omega
    | succ n ih =>
        have drop := decreases (Event.decrease n) rfl
        omega
  have choose := decreases (Event.choose (rank .root)) rfl
  have enough := lower (rank .root)
  omega

end Countdown

namespace EmptyFibres

inductive State where | ready
instance quiver : Quiver State := ⟨fun _ _ => Empty⟩

def read : Observation State ℕ := fun event => event.elim

theorem no_execution : IsEmpty (Execution State) := ⟨fun execution => (execution.event 0).elim⟩

theorem nonZeno : NonZeno read := fun execution => (no_execution.false execution).elim

theorem no_successor (state : State) : ¬ ∃ next : State, Nonempty (state ⟶ next) := by
  rintro ⟨_, ⟨event⟩⟩
  exact event.elim

end EmptyFibres

end Mettapedia.Machines.ProgressObservation.Controls
