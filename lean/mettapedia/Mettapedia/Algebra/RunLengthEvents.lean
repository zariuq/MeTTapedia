import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Range

/-!
# Run-length encoding of identified events

A run retains a complete payload and a consecutive interval of event identities.
Expansion distinguishes every occurrence. Two adjacent runs may coalesce only
when their payloads agree and the second interval starts at the first interval's
end. Coalescence preserves the ordered event history, not merely its total.

Identities here are natural numbers. Bounded machine encodings need a separate
no-wrap check; the interval-bound theorem states its arithmetic obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RunLengthEvents

universe uPayload uGrade

structure Run (Payload : Type uPayload) where
  firstIdentity : Nat
  repetitions : Nat
  payload : Payload
  deriving DecidableEq, Repr

abbrev Event (Payload : Type uPayload) := Nat × Payload

namespace Run

variable {Payload : Type uPayload}

def expand (run : Run Payload) : List (Event Payload) :=
  (List.range' run.firstIdentity run.repetitions).map fun identity => (identity, run.payload)

@[simp] theorem expand_length (run : Run Payload) : run.expand.length = run.repetitions := by
  simp [expand]

@[simp] theorem expand_identities (run : Run Payload) :
    run.expand.map Prod.fst = List.range' run.firstIdentity run.repetitions := by
  simp [expand, List.map_map, Function.comp_def]

theorem identities_nodup (run : Run Payload) : (run.expand.map Prod.fst).Nodup := by
  rw [expand_identities]
  exact List.nodup_range'

/-- Every expanded identity and payload is precisely one member of the run. -/
theorem mem_expand (run : Run Payload) (event : Event Payload) :
    event ∈ run.expand ↔ event.2 = run.payload ∧
      ∃ offset < run.repetitions, event.1 = run.firstIdentity + offset := by
  rcases event with ⟨identity, payload⟩
  simp only [expand, List.mem_map, List.mem_range', Nat.one_mul, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨offset, bound, rfl⟩, rfl, rfl⟩
    exact ⟨rfl, offset, bound, rfl⟩
  · rintro ⟨rfl, offset, bound, rfl⟩
    exact ⟨_, ⟨offset, bound, rfl⟩, rfl, rfl⟩

/-- Joining consecutive equal-payload runs preserves their entire ordered expansion. -/
theorem coalesce_expansion (first second : Run Payload)
    (samePayload : second.payload = first.payload)
    (consecutive : second.firstIdentity = first.firstIdentity + first.repetitions) :
    (Run.mk first.firstIdentity (first.repetitions + second.repetitions)
      first.payload).expand = first.expand ++ second.expand := by
  cases first
  cases second
  simp only at samePayload consecutive
  subst samePayload
  subst consecutive
  simp only [expand, ← List.range'_append, Nat.one_mul, List.map_append]

/-- Increasing one run by one is exactly appending one fresh event. -/
theorem extend_expansion (run : Run Payload) :
    {run with repetitions := run.repetitions + 1}.expand =
      run.expand ++ [(run.firstIdentity + run.repetitions, run.payload)] := by
  simp [expand, List.range'_concat]

/-- Payload-only additive metrics can be read directly from the encoded length. -/
theorem sum_payload {Grade : Type uGrade} [AddMonoid Grade]
    (grade : Payload → Grade) (run : Run Payload) :
    (run.expand.map (fun event => grade event.2)).sum = run.repetitions • grade run.payload := by
  simp only [expand, List.map_map, Function.comp_def]
  change (List.map (Function.const Nat (grade run.payload))
    (List.range' run.firstIdentity run.repetitions)).sum = _
  rw [List.map_const, List.length_range', List.sum_replicate]

/-- A finite identity representation is valid only when all expanded identities fit. -/
theorem identities_bounded (run : Run Payload) (maximum : Nat)
    (endFits : run.firstIdentity + run.repetitions ≤ maximum + 1) :
    ∀ event ∈ run.expand, event.1 ≤ maximum := by
  intro event present
  obtain ⟨_, offset, below, identity⟩ := (mem_expand run event).mp present
  omega

end Run

/-- Append an actual event, compressing only a matching consecutive final run.
The bound limits the representation of its repetition count, not its meaning. -/
def appendEvent {Payload : Type uPayload} [DecidableEq Payload] (maximum : Nat) :
    List (Run Payload) → Event Payload → List (Run Payload)
  | [], event => [⟨event.1, 1, event.2⟩]
  | [run], event =>
      if run.payload = event.2 ∧ run.firstIdentity + run.repetitions = event.1 ∧
          run.repetitions < maximum then
        [{run with repetitions := run.repetitions + 1}]
      else [run, ⟨event.1, 1, event.2⟩]
  | run :: next :: rest, event => run :: appendEvent maximum (next :: rest) event

def expand {Payload : Type uPayload} (runs : List (Run Payload)) : List (Event Payload) :=
  runs.flatMap Run.expand

@[simp] theorem expand_append {Payload : Type uPayload}
    (first second : List (Run Payload)) :
    expand (first ++ second) = expand first ++ expand second := by
  simp [expand]

/-- The executable last-run append agrees with uncompressed chronological append. -/
theorem expand_appendEvent {Payload : Type uPayload} [DecidableEq Payload]
    (maximum : Nat) (runs : List (Run Payload)) (event : Event Payload) :
    expand (appendEvent maximum runs event) = expand runs ++ [event] := by
  induction runs with
  | nil => simp [appendEvent, expand, Run.expand, List.range'_succ]
  | cons run rest ih =>
      cases rest with
      | nil =>
          by_cases coalesces : run.payload = event.2 ∧
              run.firstIdentity + run.repetitions = event.1 ∧ run.repetitions < maximum
          · simp only [appendEvent, coalesces, expand, List.flatMap_cons,
              List.flatMap_nil, List.append_nil]
            simp only [and_self, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
            have extension := Run.extend_expansion run
            simpa [coalesces.1, coalesces.2.1] using extension
          · simp [appendEvent, coalesces, expand, Run.expand, List.range'_succ]
      | cons next later =>
          simpa [appendEvent, expand, List.append_assoc] using
            congrArg (run.expand ++ ·) ih

/-- Nonconsecutive identities cannot be silently replaced by a consecutive run. -/
theorem gap_is_observable :
    expand [Run.mk 1 1 "same", Run.mk 3 1 "same"] ≠
      (Run.mk 1 2 "same").expand := by decide

/-- Payload changes remain observable even when the identities are consecutive. -/
theorem changed_payload_is_observable :
    expand [Run.mk 1 1 "first", Run.mk 2 1 "second"] ≠
      (Run.mk 1 2 "first").expand := by decide

end Mettapedia.Algebra.RunLengthEvents
