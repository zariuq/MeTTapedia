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


namespace Mettapedia.Algebra.RunLengthEvents

universe u v
variable {Payload : Type u} {NextPayload : Type v}

/-- Encode an ordered suffix beside an already retained retained. Compression
changes representation only where the ordinary append permits it. -/
def encodeInto [DecidableEq Payload] (maximum : Nat) :
    List (Event Payload) → List (Run Payload) → List (Run Payload)
  | [], retained => retained
  | event :: rest, retained => encodeInto maximum rest (appendEvent maximum retained event)

theorem expand_encodeInto [DecidableEq Payload] (maximum : Nat)
    (events : List (Event Payload)) (retained : List (Run Payload)) :
    expand (encodeInto maximum events retained) = expand retained ++ events := by
  induction events generalizing retained with
  | nil => simp [encodeInto]
  | cons event rest ih =>
      rw [encodeInto, ih, expand_appendEvent]
      simp only [List.append_assoc, List.singleton_append]

/-- Re-encode actual events rather than renaming the start of an interval. -/
def encode [DecidableEq Payload] (maximum : Nat) (events : List (Event Payload)) :
    List (Run Payload) := encodeInto maximum events []

theorem expand_encode [DecidableEq Payload] (maximum : Nat)
    (events : List (Event Payload)) : expand (encode maximum events) = events := by
  simpa only [encode, expand, List.flatMap_nil, List.nil_append] using
    expand_encodeInto maximum events []

def mapEvent (identity : Nat → Nat) (payload : Payload → NextPayload)
    (event : Event Payload) : Event NextPayload := (identity event.1, payload event.2)

theorem mapEvent_injective (identity : Nat → Nat) (payload : Payload → NextPayload)
    (identities : Function.Injective identity) (payloads : Function.Injective payload) :
    Function.Injective (mapEvent identity payload) := by
  intro first second same
  exact Prod.ext (identities (congrArg Prod.fst same)) (payloads (congrArg Prod.snd same))

/-- The bound controls repetition representation. An arbitrary identity map
may split a consecutive interval, so whole-run equality is not promised. -/
def transport [DecidableEq NextPayload] (maximum : Nat)
    (identity : Nat → Nat) (payload : Payload → NextPayload)
    (runs : List (Run Payload)) : List (Run NextPayload) :=
  encode maximum ((expand runs).map (mapEvent identity payload))

theorem expand_transport [DecidableEq NextPayload] (maximum : Nat)
    (identity : Nat → Nat) (payload : Payload → NextPayload)
    (runs : List (Run Payload)) :
    expand (transport maximum identity payload runs) =
      (expand runs).map (mapEvent identity payload) :=
  expand_encode maximum _

theorem transport_append_event [DecidableEq Payload] [DecidableEq NextPayload]
    (sourceMaximum destinationMaximum : Nat) (identity : Nat → Nat)
    (payload : Payload → NextPayload) (runs : List (Run Payload)) (event : Event Payload) :
    expand (transport destinationMaximum identity payload
      (appendEvent sourceMaximum runs event)) =
      expand (transport destinationMaximum identity payload runs) ++
        [mapEvent identity payload event] := by
  rw [expand_transport, expand_appendEvent, List.map_append,
    List.map_singleton, expand_transport]

theorem transport_reflects_chronology [DecidableEq NextPayload]
    (maximum : Nat) (identity : Nat → Nat) (payload : Payload → NextPayload)
    (identities : Function.Injective identity) (payloads : Function.Injective payload)
    (first second : List (Run Payload)) :
    expand (transport maximum identity payload first) =
      expand (transport maximum identity payload second) ↔ expand first = expand second := by
  rw [expand_transport, expand_transport]
  exact (List.map_injective_iff.mpr
    (mapEvent_injective identity payload identities payloads)).eq_iff

namespace TransportControls

def source : List (Run String) := [⟨1, 2, "same"⟩]
def spacing : Nat → Nat := fun identity => 10 * identity

theorem nonconsecutive_map_retains_both_events :
    expand (transport 255 spacing id source) = [(10, "same"), (20, "same")] ∧
      (transport 255 spacing id source).length = 2 := by decide +kernel

theorem renaming_only_interval_start_is_wrong :
    expand [Run.mk (spacing 1) 2 "same"] = [(10, "same"), (11, "same")] ∧
      expand [Run.mk (spacing 1) 2 "same"] ≠
        expand (transport 255 spacing id source) := by decide +kernel

theorem merged_identities_lose_authentication :
    expand (transport 255 (fun _ => 7) id [Run.mk 1 1 "same"]) =
      expand (transport 255 (fun _ => 7) id [Run.mk 2 1 "same"]) ∧
      expand [Run.mk 1 1 "same"] ≠ expand [Run.mk 2 1 "same"] := by decide +kernel

end TransportControls
end Mettapedia.Algebra.RunLengthEvents
