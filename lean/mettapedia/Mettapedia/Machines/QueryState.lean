import Mettapedia.Machines.ReadOnlyQuery

/-!
# State-threaded interpretation of adaptive read programs

The existing query syntax is retained. A service may allocate a private
fresh-name scope on each read, so equal keys need not return the same names.
The interpreter threads that service state through nested continuations and
records the actual ordered replies. It does not re-evaluate a query or erase
repeated read occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.QueryState

open ReadOnlyQuery

variable {Key Reply Answer Other State : Type}

structure Observation (Key Reply Answer State : Type) where
  answer : Answer
  state : State
  reads : List (Key × Reply)

def run (service : State → Key → Reply × State) :
    Program Key Reply Answer → State → Observation Key Reply Answer State
  | .pure answer, state => ⟨answer, state, []⟩
  | .read key next, state =>
      let response := service state key
      let rest := run service (next response.1) response.2
      ⟨rest.answer, rest.state, (key, response.1) :: rest.reads⟩

theorem run_bind (service : State → Key → Reply × State)
    (program : Program Key Reply Answer) (next : Answer → Program Key Reply Other) (state : State) :
    run service (ReadOnlyQuery.bind program next) state =
      let first := run service program state
      let second := run service (next first.answer) first.state
      ⟨second.answer, second.state, first.reads ++ second.reads⟩ := by
  induction program generalizing state with
  | pure answer => simp [ReadOnlyQuery.bind, run]
  | read key more ih => simp [ReadOnlyQuery.bind, run, ih]

theorem run_map (service : State → Key → Reply × State) (convert : Answer → Other)
    (program : Program Key Reply Answer) (state : State) :
    run service (ReadOnlyQuery.map convert program) state =
      let result := run service program state
      ⟨convert result.answer, result.state, result.reads⟩ := by
  rw [ReadOnlyQuery.map, run_bind]
  simp [run]

/-- The old read-only interpreter is recovered when the service really has
no private state change; this is a derived special case, not the definition. -/
theorem readOnly (store : Key → Reply) (program : Program Key Reply Answer) (state : State) :
    run (fun current key => (store key, current)) program state =
      ⟨(ReadOnlyQuery.run store program).answer, state, (ReadOnlyQuery.run store program).reads⟩ := by
  induction program generalizing state with
  | pure answer => rfl
  | read key more ih => simp [run, ReadOnlyQuery.run, ih]

theorem state_invariant (service : State → Key → Reply × State) (invariant : State → Prop)
    (step : ∀ state, invariant state → ∀ key, invariant (service state key).2)
    (program : Program Key Reply Answer) (state : State) (good : invariant state) :
    invariant (run service program state).state := by
  induction program generalizing state with
  | pure answer => exact good
  | read key more ih => exact ih (service state key).1 _ (step state good key)

theorem state_extends (service : State → Key → Reply × State) (rel : State → State → Prop)
    (refl : ∀ state, rel state state)
    (trans : ∀ a b c, rel a b → rel b c → rel a c)
    (step : ∀ state key, rel state (service state key).2)
    (program : Program Key Reply Answer) (state : State) : rel state (run service program state).state := by
  induction program generalizing state with
  | pure answer => exact refl state
  | read key more ih => exact trans state _ _ (step state key) (ih (service state key).1 _)

namespace Controls

def twice : Program Unit Nat (Nat × Nat) :=
  .read () fun first => .read () fun second => .pure (first, second)

theorem repeated_keys_have_separate_occurrences :
    run (fun next (_ : Unit) => (next, next + 1)) twice 4 =
      ⟨(4, 5), 6, [((), 4), ((), 5)]⟩ := rfl

theorem readOnly_key_reuse_changes_fresh_answers :
    (run (fun next (_ : Unit) => (next, next + 1)) twice 4).answer ≠
      (ReadOnlyQuery.run (fun _ => 4) twice).answer := by decide

end Controls

end Mettapedia.Machines.QueryState
