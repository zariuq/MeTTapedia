import Mettapedia.Machines.GenerationInvalidation

/-!
# Retained identities with bounded, non-reusable generations

Unlike a cache that can erase old cells before recycling a generation, a retained
identity may have external references that cannot be recalled. Replacement must
therefore issue a fresh bounded generation, or fail before changing the state.
Unrelated identities and payload-only writes preserve the reference discipline.

The state and bound invariant are shared with `GenerationInvalidation`. Here a
reference compares against its own retained cell, rather than the global cache
generation. These are different observation rules. This model does not interpret
C, machine faults, native callers or the finite table's allocation algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RetainedGeneration

open GenerationInvalidation (Cell State WellFormed)

variable {Key Value : Type} [DecidableEq Key]

def Current (state : State Key Value) (key : Key) (stamp : Nat) : Prop :=
  0 < stamp ∧ ∃ cell, state.slots key = some cell ∧ cell.generation = stamp

def Older (state : State Key Value) (key : Key) (stamp : Nat) : Prop :=
  ∃ cell, state.slots key = some cell ∧ stamp < cell.generation

def replace (limit : Nat) (state : State Key Value) (key : Key) (value : Value) :
    Option (State Key Value) :=
  if state.generation < limit then
    some ⟨state.generation + 1,
      Function.update state.slots key (some ⟨state.generation + 1, value⟩)⟩
  else none

def register (limit : Nat) (state : State Key Value) (key : Key) (value : Value) :
    Option (State Key Value) :=
  match state.slots key with
  | none => some { state with slots := Function.update state.slots key (some ⟨1, value⟩) }
  | some _ => replace limit state key value

def writePayload (state : State Key Value) (key : Key) (value : Value) : State Key Value :=
  match state.slots key with
  | none => state
  | some cell =>
      { state with slots := Function.update state.slots key (some { cell with payload := value }) }

private theorem update_wellFormed (limit : Nat) (state : State Key Value)
    (valid : WellFormed limit state) (counter : Nat) (positive : 0 < counter)
    (bounded : counter ≤ limit) (monotone : state.generation ≤ counter)
    (key : Key) (cell : Cell Value) (cellBound : cell.generation ≤ counter) :
    WellFormed limit ⟨counter, Function.update state.slots key (some cell)⟩ := by
  refine ⟨positive, bounded, ?_⟩
  intro observed entry found
  by_cases same : observed = key
  · subst observed
    simp only [Function.update_self, Option.some.injEq] at found
    subst entry
    exact cellBound
  · have original : state.slots observed = some entry := by simpa [same] using found
    exact Nat.le_trans (valid.2.2 observed entry original) monotone

theorem replace_wellFormed (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key : Key) (value : Value)
    (accepted : replace limit state key value = some next) : WellFormed limit next := by
  by_cases room : state.generation < limit
  · simp only [replace, room, ↓reduceIte, Option.some.injEq] at accepted
    subst next
    exact update_wellFormed limit state valid _ (by omega) (by omega)
      (by omega) key _ (by simp)
  · simp [replace, room] at accepted

theorem register_wellFormed (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key : Key) (value : Value)
    (accepted : register limit state key value = some next) : WellFormed limit next := by
  cases found : state.slots key with
  | none =>
      simp only [register, found, Option.some.injEq] at accepted
      subst next
      exact update_wellFormed limit state valid _ valid.1 valid.2.1 (by rfl)
        key _ (by exact valid.1)
  | some cell =>
      exact replace_wellFormed limit state next valid key value (by simpa [register, found] using accepted)

theorem payload_wellFormed (limit : Nat) (state : State Key Value)
    (valid : WellFormed limit state) (key : Key) (value : Value) :
    WellFormed limit (writePayload state key value) := by
  cases found : state.slots key with
  | none => simpa [writePayload, found] using valid
  | some cell =>
      simpa [writePayload, found] using
        update_wellFormed limit state valid _ valid.1 valid.2.1 (by rfl) key
          ({ cell with payload := value }) (valid.2.2 key cell found)

omit [DecidableEq Key] in
theorem older_not_current (state : State Key Value) (key : Key) (stamp : Nat)
    (old : Older state key stamp) : ¬ Current state key stamp := by
  rintro ⟨_, current, found, equal⟩
  rcases old with ⟨cell, stored, strict⟩
  rw [stored] at found
  cases Option.some.inj found
  omega

theorem replacement_invalidates (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key : Key) (value : Value) (stamp : Nat)
    (current : Current state key stamp)
    (accepted : replace limit state key value = some next) : Older next key stamp := by
  rcases current.2 with ⟨cell, found, equal⟩
  have bounded := valid.2.2 key cell found
  by_cases room : state.generation < limit
  · simp only [replace, room, ↓reduceIte, Option.some.injEq] at accepted
    subst next
    exact ⟨⟨state.generation + 1, value⟩, by simp, by dsimp; omega⟩
  · simp [replace, room] at accepted

theorem reregistration_invalidates (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key : Key) (value : Value) (stamp : Nat)
    (current : Current state key stamp)
    (accepted : register limit state key value = some next) : ¬ Current next key stamp := by
  obtain ⟨cell, found, _⟩ := current.2
  apply older_not_current next key stamp
  apply replacement_invalidates limit state next valid key value stamp current
  simpa [register, found] using accepted

theorem exhausted_replacement (limit : Nat) (state : State Key Value)
    (full : limit ≤ state.generation) (key : Key) (value : Value) :
    replace limit state key value = none := by
  simp [replace, Nat.not_lt_of_ge full]

private theorem update_other_older (state : State Key Value) (key observed : Key)
    (different : observed ≠ key) (stamp counter : Nat) (cell : Cell Value)
    (old : Older state observed stamp) :
    Older ⟨counter, Function.update state.slots key (some cell)⟩ observed stamp := by
  simpa [Older, different] using old

theorem replacement_preserves_older (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key observed : Key) (value : Value) (stamp : Nat)
    (old : Older state observed stamp)
    (accepted : replace limit state key value = some next) : Older next observed stamp := by
  by_cases room : state.generation < limit
  · simp only [replace, room, ↓reduceIte, Option.some.injEq] at accepted
    subst next
    by_cases same : observed = key
    · subst observed
      rcases old with ⟨cell, found, strict⟩
      have bounded := valid.2.2 key cell found
      exact ⟨⟨state.generation + 1, value⟩, by simp, by dsimp; omega⟩
    · exact update_other_older state key observed same stamp _ _ old
  · simp [replace, room] at accepted

theorem registration_preserves_older (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key observed : Key) (value : Value) (stamp : Nat)
    (old : Older state observed stamp)
    (accepted : register limit state key value = some next) : Older next observed stamp := by
  cases found : state.slots key with
  | none =>
      have different : observed ≠ key := by
        intro same
        rcases old with ⟨cell, stored, _⟩
        simp [same, found] at stored
      simp only [register, found, Option.some.injEq] at accepted
      subst next
      exact update_other_older state key observed different stamp _ _ old
  | some cell =>
      exact replacement_preserves_older limit state next valid key observed value stamp old
        (by simpa [register, found] using accepted)

theorem payload_preserves_older (state : State Key Value) (key observed : Key)
    (value : Value) (stamp : Nat) (old : Older state observed stamp) :
    Older (writePayload state key value) observed stamp := by
  cases found : state.slots key with
  | none => simpa [writePayload, found] using old
  | some cell =>
      by_cases same : observed = key
      · subst observed
        rcases old with ⟨entry, stored, strict⟩
        rw [found] at stored
        cases Option.some.inj stored
        exact ⟨{ cell with payload := value }, by simp [writePayload, found], strict⟩
      · simpa [writePayload, found] using
          update_other_older state key observed same stamp state.generation
            { cell with payload := value } old

inductive Event (Key Value : Type)
  | register (key : Key) (value : Value)
  | replace (key : Key) (value : Value)
  | writePayload (key : Key) (value : Value)

def step (limit : Nat) (state : State Key Value) : Event Key Value → State Key Value
  | .register key value => (register limit state key value).getD state
  | .replace key value => (replace limit state key value).getD state
  | .writePayload key value => writePayload state key value

theorem step_preserves (limit : Nat) (state : State Key Value)
    (valid : WellFormed limit state) (key : Key) (stamp : Nat) (old : Older state key stamp)
    (event : Event Key Value) :
    WellFormed limit (step limit state event) ∧ Older (step limit state event) key stamp := by
  cases event with
  | register changed value =>
      cases accepted : register limit state changed value with
      | none => simpa [step, accepted] using And.intro valid old
      | some next =>
          simpa [step, accepted] using And.intro
            (register_wellFormed limit state next valid changed value accepted)
            (registration_preserves_older limit state next valid changed key value stamp old accepted)
  | replace changed value =>
      cases accepted : replace limit state changed value with
      | none => simpa [step, accepted] using And.intro valid old
      | some next =>
          simpa [step, accepted] using And.intro
            (replace_wellFormed limit state next valid changed value accepted)
            (replacement_preserves_older limit state next valid changed key value stamp old accepted)
  | writePayload changed value =>
      exact ⟨payload_wellFormed limit state valid changed value,
        payload_preserves_older state changed key value stamp old⟩

theorem trace_never_resurrects (limit : Nat) (state : State Key Value)
    (valid : WellFormed limit state) (key : Key) (stamp : Nat) (old : Older state key stamp)
    (events : List (Event Key Value)) :
    ¬ Current (events.foldl (step limit) state) key stamp := by
  induction events generalizing state with
  | nil => exact older_not_current state key stamp old
  | cons event rest ih =>
      have next := step_preserves limit state valid key stamp old event
      exact ih _ next.1 next.2

theorem reregistration_trace_invalidates (limit : Nat) (state next : State Key Value)
    (valid : WellFormed limit state) (key : Key) (stamp : Nat) (value : Value)
    (current : Current state key stamp)
    (accepted : register limit state key value = some next) (events : List (Event Key Value)) :
    ¬ Current (events.foldl (step limit) next) key stamp := by
  obtain ⟨cell, found, _⟩ := current.2
  have fresh : replace limit state key value = some next := by
    simpa [register, found] using accepted
  exact trace_never_resurrects limit next (register_wellFormed limit state next valid key value accepted)
    key stamp (replacement_invalidates limit state next valid key value stamp current fresh) events

theorem exhausted_step_preserves_state (limit : Nat) (state : State Key Value)
    (full : limit ≤ state.generation) (key : Key) (value : Value) :
    step limit state (.replace key value) = state := by
  simp [step, exhausted_replacement limit state full key value]

def exampleState : State Bool Nat := ⟨2, fun key => if key then some ⟨2, 7⟩ else none⟩

theorem reset_to_one_resurrects :
    ¬ Current exampleState true 1 ∧
      Current (⟨2, fun key => if key then some ⟨1, 8⟩ else none⟩ : State Bool Nat) true 1 := by
  constructor
  · rintro ⟨_, cell, found, equal⟩
    have same : (⟨2, 7⟩ : Cell Nat) = cell := by
      simpa [exampleState] using found
    subst cell
    contradiction
  · exact ⟨by decide, ⟨1, 8⟩, rfl, rfl⟩

theorem exhausted_control : replace 2 exampleState true 8 = none := by
  simp [replace, exampleState]

theorem fresh_replacement_control :
    (replace 3 exampleState true 8).map (fun state => state.slots true) = some (some ⟨3, 8⟩) := by
  simp [replace, exampleState]

end Mettapedia.Machines.RetainedGeneration
