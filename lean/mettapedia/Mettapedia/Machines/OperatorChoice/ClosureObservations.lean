import Mettapedia.Languages.MeTTa.PeTTa.PartialApplicationExpansion
import Mettapedia.Machines.QueryState

/-!
# A partial application's presentation is not its dispatch authority

The existing private partial carrier retains its base and ordered bound
arguments. A public presentation is additional information. Equal payloads
preserve application under every handler, even when displays differ. Equal
displays do not imply equal application, and current alias agreement need not
survive later name updates.

The mutable controls use a small, argument-dependent family of functions,
adding a stored coefficient to the supplied numbers. They distinguish live
name lookup from capturing that coefficient. They do not prescribe which
closure policy HE or PeTTa should adopt or identify a printer with a codec.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.ClosureObservations

open Mettapedia.Languages.MeTTa.PeTTa.PartialApplicationExpansion
open ReadOnlyQuery (Program)

variable {Value Other State Reply : Type}

structure Presented (Value : Type) where
  payload : Partial Value
  label : String

def display (closure : Presented Value) : String × List Value :=
  (closure.label, closure.payload.bound)

def invoke (handler : State → Value → List Value → Reply × State)
    (state : State) (closure : Presented Value) (arguments : List Value) : Reply × State :=
  handler state closure.payload.base (closure.payload.bound ++ arguments)

theorem same_payload_preserves_application
    (handler : State → Value → List Value → Reply × State) (state : State)
    (first second : Presented Value) (same : first.payload = second.payload)
    (arguments : List Value) : invoke handler state first arguments =
      invoke handler state second arguments := by
  simp [invoke, same]

def map (convert : Value → Other) (closure : Presented Value) : Presented Other :=
  ⟨closure.payload.map convert, closure.label⟩

/-- Structural argument completion commutes with representation transport. -/
theorem completion_transport (convert : Value → Other) (closure : Presented Value)
    (arguments : List Value) :
    (expand closure.payload arguments).map convert =
      expand (map convert closure).payload (arguments.map convert) :=
  expand_map convert closure.payload arguments

namespace LiveNames

abbrev Table := Nat → Nat

def handler (table : Table) (name : Nat) (arguments : List Nat) : Nat × Table :=
  (table name + arguments.sum, table)

inductive Command where
  | put (name value : Nat)
  | apply (closure : Partial Nat) (arguments : List Nat)

def service (table : Table) : Command → Nat × Table
  | .put name value => (value, Function.update table name value)
  | .apply closure arguments => handler table closure.base (closure.bound ++ arguments)

def capture (table : Table) (closure : Presented Nat) : Presented Nat :=
  ⟨⟨table closure.payload.base, closure.payload.bound⟩, closure.label⟩

def retainedHandler (table : Table) (coefficient : Nat) (arguments : List Nat) : Nat × Table :=
  (coefficient + arguments.sum, table)

theorem capture_matches_the_creation_read (table : Table) (closure : Presented Nat)
    (arguments : List Nat) :
    invoke retainedHandler table (capture table closure) arguments =
      invoke handler table closure arguments := rfl

/-- Captured meaning survives a later name edit in this function family. The
world edit itself is retained; equality is of application answers only. -/
theorem captured_answer_survives_name_changes (before after : Table)
    (closure : Presented Nat) (arguments : List Nat) :
    (invoke retainedHandler after (capture before closure) arguments).1 =
      (invoke handler before closure arguments).1 := rfl

end LiveNames

namespace Controls

open LiveNames

def table : Table := fun _ => 7
def first : Presented Nat := ⟨⟨1, [3]⟩, "closure f"⟩
def second : Presented Nat := ⟨⟨2, [3]⟩, "closure f"⟩
def renamed : Presented Nat := ⟨first.payload, "closure base"⟩

theorem distinct_displays_can_share_the_same_application :
    display first ≠ display renamed ∧
      invoke handler table first [5] = invoke handler table renamed [5] := by
  constructor
  · decide
  · rfl

theorem equal_displays_and_current_answers_do_not_certify_future_aliases :
    display first = display second ∧
      (invoke handler table first [5]).1 = (invoke handler table second [5]).1 ∧
      (invoke handler (Function.update table 1 11) first [5]).1 = 19 ∧
      (invoke handler (Function.update table 1 11) second [5]).1 = 15 := by decide

def editThenApply (closure : Partial Nat) : Program Command Nat Nat :=
  .read (.put 1 11) fun _ => .read (.apply closure [5]) .pure

theorem a_public_update_context_distinguishes_the_aliases :
    (QueryState.run service (editThenApply first.payload) table).answer = 19 ∧
      (QueryState.run service (editThenApply second.payload) table).answer = 15 := by decide

theorem live_and_retained_meanings_are_different_policies :
    (invoke handler (Function.update table 1 11) first [5]).1 = 19 ∧
      (invoke retainedHandler (Function.update table 1 11) (capture table first) [5]).1 = 15 := by decide

/-- A rendering that loses authority can identify semantically distinct
partials even when their visible arguments are identical. -/
theorem a_display_key_is_not_a_uniform_application_cache_key :
    ¬ (∀ state : Table, (invoke handler state first [5]).1 =
        (invoke handler state second [5]).1) := by
  intro allStates
  have impossible := allStates (Function.update table 1 11)
  change 19 = 15 at impossible
  contradiction

end Controls

end Mettapedia.Machines.OperatorChoice.ClosureObservations
