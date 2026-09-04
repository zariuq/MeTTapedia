import Mathlib.Tactic

/-!
# Staged binding observations for semantic decoding

A left-to-right decoder should not be forced into a global strict-scope mode
or a language-specific reflective-mode toggle.  The authored semantic
compiler instead emits one of three observations:

* `bind stage name` introduces an outer variable at a semantic stage;
* `use stage name` records an outer use, possibly as a deferred obligation;
* `opaqueCapture stage payload` inserts a value whose internal variables
  belong to the captured stage and are not recursively reinterpreted outside.

Deferred obligations support trailing binders.  Stage-indexed keys prevent a
binder in one stage from accidentally discharging an obligation in another.
Opaque capture is the generic form of lawful reflective MM2 behavior.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.StagedBinding

universe uName uPayload

/-- A variable address includes its semantic stage. -/
abbrev Key (Name : Type uName) := Nat × Name

/-- Binding-relevant observations emitted by an authored semantic compiler. -/
inductive Event (Name : Type uName) (Payload : Type uPayload) where
  | bind (stage : Nat) (name : Name)
  | use (stage : Nat) (name : Name)
  | opaqueCapture (stage : Nat) (payload : Payload)
  deriving DecidableEq, Repr

/-- The outer binding ledger.  `pending` records uses whose matching binder
has not yet appeared in the selected linearization. -/
structure State (Name : Type uName) where
  bound : List (Key Name)
  pending : List (Key Name)
  deriving DecidableEq, Repr

namespace State

variable {Name : Type uName} [DecidableEq Name]

def empty : State Name := ⟨[], []⟩

private def insertKey (key : Key Name) (keys : List (Key Name)) :
    List (Key Name) :=
  if key ∈ keys then keys else key :: keys

private def eraseKey (key : Key Name) (keys : List (Key Name)) :
    List (Key Name) :=
  keys.filter fun other => decide (other ≠ key)

/-- Deferred observation semantics.  Binding discharges the matching pending
obligation at the same stage; opaque payloads are values at this level. -/
def observe {Payload : Type uPayload} :
    State Name → Event Name Payload → State Name
  | state, .bind stage name =>
      { bound := insertKey (stage, name) state.bound
        pending := eraseKey (stage, name) state.pending }
  | state, .use stage name =>
      if (stage, name) ∈ state.bound then state
      else { state with pending := insertKey (stage, name) state.pending }
  | state, .opaqueCapture _stage _payload => state

def run {Payload : Type uPayload} :
    State Name → List (Event Name Payload) → State Name
  | state, [] => state
  | state, event :: events => run (observe state event) events

/-- All deferred outer-use obligations have been discharged. -/
def Admissible (state : State Name) : Prop := state.pending = []

/-- Strict online observation rejects a use whose binder has not appeared. -/
def observeStrict? {Payload : Type uPayload} :
    State Name → Event Name Payload → Option (State Name)
  | state, .bind stage name =>
      some (observe (Payload := Payload) state (.bind stage name))
  | state, .use stage name =>
      if (stage, name) ∈ state.bound then some state else none
  | state, .opaqueCapture _stage _payload => some state

def runStrict? {Payload : Type uPayload} :
    State Name → List (Event Name Payload) → Option (State Name)
  | state, [] => some state
  | state, event :: events => do
      let next ← observeStrict? state event
      runStrict? next events

@[simp] theorem observe_opaqueCapture {Payload : Type uPayload}
    (state : State Name) (stage : Nat) (payload : Payload) :
    observe state (.opaqueCapture stage payload) = state := rfl

@[simp] theorem observe_use_of_bound {Payload : Type uPayload}
    (state : State Name) (stage : Nat) (name : Name)
    (bound : (stage, name) ∈ state.bound) :
    observe (Payload := Payload) state (.use stage name) = state := by
  simp [observe, bound]

theorem observe_unbound_use_mem_pending {Payload : Type uPayload}
    (state : State Name) (stage : Nat) (name : Name)
    (unbound : (stage, name) ∉ state.bound) :
    (stage, name) ∈
  (observe (Payload := Payload) state (.use stage name)).pending := by
  simp only [observe, unbound, if_false]
  by_cases present : (stage, name) ∈ state.pending <;>
    simp [insertKey, present]

theorem observe_bind_removes_matching_pending {Payload : Type uPayload}
    (state : State Name) (stage : Nat) (name : Name) :
    (stage, name) ∉
      (observe (Payload := Payload) state (.bind stage name)).pending := by
  simp [observe, eraseKey]

/-- Successful strict observation is a special case of deferred observation
and produces exactly the same outer state. -/
theorem observeStrict?_eq_some_iff {Payload : Type uPayload}
    (state next : State Name) (event : Event Name Payload) :
    observeStrict? state event = some next ↔
      observe state event = next ∧
        match event with
        | .use stage name => (stage, name) ∈ state.bound
        | _ => True := by
  cases event with
  | bind stage name => simp [observeStrict?, observe]
  | use stage name =>
      by_cases bound : (stage, name) ∈ state.bound <;>
        simp [observeStrict?, observe, bound]
  | opaqueCapture stage payload => simp [observeStrict?, observe]

/-- A strict trace is preserved exactly by the deferred observer. -/
theorem runStrict?_eq_some_implies_run_eq
    {Payload : Type uPayload} :
    ∀ (events : List (Event Name Payload)) (state finalState : State Name),
      runStrict? state events = some finalState →
        run state events = finalState := by
  intro events
  induction events with
  | nil =>
      intro state finalState strictRun
      simpa [runStrict?, run] using strictRun
  | cons event events inductionHypothesis =>
      intro state finalState strictRun
      simp only [runStrict?] at strictRun
      cases strictStep : observeStrict? state event with
      | none => simp [strictStep] at strictRun
      | some next =>
          rw [strictStep] at strictRun
          have observed : observe state event = next :=
            (observeStrict?_eq_some_iff state next event).mp strictStep |>.1
          simp only [run, observed]
          exact inductionHypothesis next finalState strictRun

/-- A strict trace ending with no pending obligations is admitted by the
deferred semantics. -/
theorem strict_admissible_in_deferred
    {Payload : Type uPayload} {events : List (Event Name Payload)}
    {state finalState : State Name}
    (strictRun : runStrict? state events = some finalState)
    (admissible : finalState.Admissible) :
    (run state events).Admissible := by
  rw [runStrict?_eq_some_implies_run_eq events state finalState strictRun]
  exact admissible

end State

/-! ## Positive and negative controls -/

private abbrev StringEvent := Event String Unit

private def trailingBinderTrace : List StringEvent :=
  [.use 0 "x", .bind 0 "x"]

/-- Deferred obligations support a binding-respecting language whose concrete
linearization places a binder after its use. -/
theorem trailing_binder_is_deferred_admissible :
    (State.run State.empty trailingBinderTrace).Admissible := by
  simp [trailingBinderTrace, State.run, State.observe, State.Admissible,
    State.empty, State.insertKey, State.eraseKey]

/-- The same trace is rejected by strict introduced-before-use masking. -/
theorem trailing_binder_is_not_strictly_admissible :
    State.runStrict? State.empty trailingBinderTrace = none := by
  decide

private def wrongStageTrace : List StringEvent :=
  [.use 0 "x", .bind 1 "x"]

/-- A binder at another semantic stage cannot discharge an outer obligation. -/
theorem wrong_stage_binder_does_not_discharge :
    ¬ (State.run State.empty wrongStageTrace).Admissible := by
  simp [wrongStageTrace, State.run, State.observe, State.Admissible,
    State.empty, State.insertKey, State.eraseKey]

/-- A captured value is opaque to the outer stage even if its payload contains
bytes that an inner stage will later interpret as variable references. -/
theorem reflective_payload_is_outer_opaque :
    State.run (Name := String) State.empty
      [Event.opaqueCapture 1 ["$inner", "$later"]] = State.empty := by
  rfl

/-- Ordinary uses remain stage-sensitive outside an opaque capture. -/
theorem uncaptured_inner_spelling_creates_outer_obligation :
    ¬ (State.run (Name := String) State.empty
      [(Event.use 0 "$inner" : StringEvent)]).Admissible := by
  simp [State.run, State.observe, State.Admissible, State.empty,
    State.insertKey]

#print axioms State.observeStrict?_eq_some_iff
#print axioms State.runStrict?_eq_some_implies_run_eq
#print axioms State.strict_admissible_in_deferred
#print axioms trailing_binder_is_deferred_admissible
#print axioms trailing_binder_is_not_strictly_admissible
#print axioms wrong_stage_binder_does_not_discharge
#print axioms reflective_payload_is_outer_opaque
#print axioms uncaptured_inner_spelling_creates_outer_obligation

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.StagedBinding
