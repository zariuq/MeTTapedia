import Mettapedia.Machines.OperatorChoice.HeadDispatchDesigns
import Mettapedia.Machines.QueryState

/-!
# Private interpreter state under arbitrary public adaptive clients

The source service and engine service are separately defined. The engine
retains implementation rows and an audit counter; public operations query,
count and extend only its source view. The commuting law lifts through the
existing state-threaded client interpreter, preserving complete reply histories
and source-world changes.

The API offers no operation naming the implementation store. This is a
capability boundary assumption of the model, not C memory protection or an
assertion that public numeric scope labels are unforgeable.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.PrivateMachineViews

open ReadOnlyQuery (Program)
open HeadDispatchDesigns

variable {Payload Answer : Type}

inductive Command (Payload : Type) where
  | query (request : Request)
  | count
  | add (head : Option String) (arity : Nat) (payload : Payload)
  deriving DecidableEq, Repr

inductive Reply (Payload : Type) where
  | answers (values : List Payload)
  | count (count : Nat)
  | added
  deriving DecidableEq, Repr

structure Engine (Payload : Type) where
  source : List (Rule Payload)
  internal : List (Rule Payload)
  auditSteps : Nat
  deriving DecidableEq, Repr

def sourceStep (design : Design) (rows : List (Rule Payload)) :
    Command Payload → Reply Payload × List (Rule Payload)
  | .query request => (.answers (select design 0 request rows), rows)
  | .count => (.count rows.length, rows)
  | .add head arity payload => (.added, rows ++ [⟨0, head, arity, payload⟩])

def engineStep (design : Design) (engine : Engine Payload) :
    Command Payload → Reply Payload × Engine Payload
  | .query request =>
      (.answers (select design 0 request engine.source),
        { engine with auditSteps := engine.auditSteps + 1 })
  | .count =>
      (.count engine.source.length, { engine with auditSteps := engine.auditSteps + 1 })
  | .add head arity payload =>
      (.added, { source := engine.source ++ [⟨0, head, arity, payload⟩]
                 internal := engine.internal
                 auditSteps := engine.auditSteps + 1 })

theorem local_square (design : Design) (engine : Engine Payload) (command : Command Payload) :
    sourceStep design engine.source command =
      ((engineStep design engine command).1, (engineStep design engine command).2.source) := by
  cases command <;> rfl

/-- Source observations retain replies, history and the resulting source store. -/
def sourceObservation (result : QueryState.Observation (Command Payload) (Reply Payload)
    Answer (Engine Payload)) :
    QueryState.Observation (Command Payload) (Reply Payload) Answer (List (Rule Payload)) :=
  ⟨result.answer, result.state.source, result.reads⟩

theorem all_public_clients (design : Design)
    (program : Program (Command Payload) (Reply Payload) Answer) (engine : Engine Payload) :
    QueryState.run (sourceStep design) program engine.source =
      sourceObservation (QueryState.run (engineStep design) program engine) := by
  induction program generalizing engine with
  | pure answer => rfl
  | read command next ih =>
    simp only [QueryState.run, local_square design engine command]
    rw [ih (engineStep design engine command).1 (engineStep design engine command).2]
    rfl

theorem internal_rows_preserved (design : Design)
    (program : Program (Command Payload) (Reply Payload) Answer) (engine : Engine Payload) :
    (QueryState.run (engineStep design) program engine).state.internal = engine.internal := by
  induction program generalizing engine with
  | pure answer => rfl
  | read command next ih =>
    simp only [QueryState.run]
    rw [ih (engineStep design engine command).1 (engineStep design engine command).2]
    cases command <;> rfl

/-- An adaptive client's later requests cannot reveal implementation rows. -/
theorem private_replacement_preserves_observation (design : Design)
    (program : Program (Command Payload) (Reply Payload) Answer)
    (first second : Engine Payload) (same : first.source = second.source) :
    sourceObservation (QueryState.run (engineStep design) program first) =
      sourceObservation (QueryState.run (engineStep design) program second) := by
  rw [← all_public_clients, ← all_public_clients, same]

namespace Controls

def engine : Engine Nat :=
  ⟨[⟨0, some "f", 1, 7⟩], [⟨1, none, 1, 99⟩, ⟨1, some "pm:step", 1, 100⟩], 10⟩

def client : Program (Command Nat) (Reply Nat) (Reply Nat × Reply Nat) :=
  .read .count fun before =>
    .read (.add none 1 8) fun _ => .read (.query ⟨"g", 1, false⟩) fun answers =>
      .pure (before, answers)

theorem source_count_and_general_rules_ignore_the_interpreter_rows :
    (QueryState.run (engineStep HeadDispatchDesigns.Controls.scopedGeneral) client engine).answer =
      (.count 1, .answers [8]) ∧
      (QueryState.run (engineStep HeadDispatchDesigns.Controls.scopedGeneral) client engine).state.auditSteps = 13 :=
  by decide

theorem counting_a_flat_store_is_an_observable_leak :
    engine.source.length = 1 ∧ (engine.source ++ engine.internal).length = 3 := by decide

theorem separation_can_erase_inner_scope_checks :
    select HeadDispatchDesigns.Controls.scopedGeneral 0 ⟨"f", 1, false⟩
        (engine.source ++ engine.internal) =
      select { HeadDispatchDesigns.Controls.scopedGeneral with respectScope := false }
        0 ⟨"f", 1, false⟩ engine.source := by
  apply separated_view_erases_scope_tests HeadDispatchDesigns.Controls.scopedGeneral
    0 ⟨"f", 1, false⟩ engine.source engine.internal
  · intro row member
    simp only [engine, List.mem_singleton] at member
    subst row
    rfl
  · intro row member
    simp only [engine, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

end Controls

end Mettapedia.Machines.OperatorChoice.PrivateMachineViews
