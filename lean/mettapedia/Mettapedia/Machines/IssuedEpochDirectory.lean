import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Finite read sets summarized by globally issued epochs

Each publication writes an arbitrary value and an epoch newer than every live
entry. The maximum epoch of a fixed read set is not an injective encoding of an
arbitrary directory. Along a valid publication history, however, equality of
that maximum entails equality of every selected value. Unrelated publications
may advance the issuer without invalidating the selected read set.

Read-set topology and owner identity are separate dependencies. Machine-word
comparison also requires the issuer not to wrap; encoding alone does not supply
that condition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IssuedEpochDirectory

universe u v

structure Cell (Value : Type v) where
  epoch : Nat
  value : Value

structure State (Key : Type u) (Value : Type v) where
  clock : Nat
  cells : Key → Cell Value

variable {Key : Type u} {Value : Type v} [DecidableEq Key]

def Valid (state : State Key Value) : Prop :=
  ∀ key, (state.cells key).epoch ≤ state.clock

def initial (values : Key → Value) : State Key Value :=
  ⟨0, fun key => ⟨0, values key⟩⟩

omit [DecidableEq Key] in
theorem initial_valid (values : Key → Value) : Valid (initial values) := fun _ => Nat.le_refl _

def publish (state : State Key Value) (key : Key) (value : Value) : State Key Value :=
  ⟨state.clock + 1, Function.update state.cells key ⟨state.clock + 1, value⟩⟩

theorem publish_valid (state : State Key Value) (valid : Valid state) (key : Key) (value : Value) :
    Valid (publish state key value) := by
  intro other
  by_cases same : other = key
  · subst other
    simp [publish]
  · simp only [publish, Function.update_of_ne same]
    exact (valid other).trans (Nat.le_succ _)

theorem publish_value (state : State Key Value) (key : Key) (value : Value) :
    ((publish state key value).cells key).value = value := by simp [publish]

theorem publish_other (state : State Key Value) (key other : Key) (value : Value)
    (different : other ≠ key) : (publish state key value).cells other = state.cells other := by
  simp [publish, different]

def latest (state : State Key Value) : List Key → Nat
  | [] => 0
  | key :: rest => max (state.cells key).epoch (latest state rest)

def read (state : State Key Value) (keys : List Key) : List Value :=
  keys.map fun key => (state.cells key).value

omit [DecidableEq Key] in
theorem latest_le_clock (state : State Key Value) (valid : Valid state) (keys : List Key) :
    latest state keys ≤ state.clock := by
  induction keys with
  | nil => exact Nat.zero_le _
  | cons key keys ih => exact max_le (valid key) ih

omit [DecidableEq Key] in
theorem epoch_le_latest (state : State Key Value) (keys : List Key) (key : Key) (member : key ∈ keys) :
    (state.cells key).epoch ≤ latest state keys := by
  induction keys with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact le_max_left _ _
      · exact (ih member).trans (le_max_right _ _)

omit [DecidableEq Key] in
theorem latest_mono (before after : State Key Value)
    (monotone : ∀ key, (before.cells key).epoch ≤ (after.cells key).epoch) (keys : List Key) :
    latest before keys ≤ latest after keys := by
  induction keys with
  | nil => exact Nat.le_refl _
  | cons key keys ih => exact max_le_max (monotone key) ih

theorem publish_epoch_mono (state : State Key Value) (valid : Valid state)
    (key other : Key) (value : Value) :
    (state.cells other).epoch ≤ ((publish state key value).cells other).epoch := by
  by_cases same : other = key
  · subst other
    simpa [publish] using (valid key).trans (Nat.le_succ state.clock)
  · rw [publish_other state key other value same]

theorem publish_latest_mono (state : State Key Value) (valid : Valid state)
    (key : Key) (value : Value) (keys : List Key) :
    latest state keys ≤ latest (publish state key value) keys :=
  latest_mono state _ (fun other => publish_epoch_mono state valid key other value) keys

theorem published_member_advances (state : State Key Value) (valid : Valid state)
    (key : Key) (value : Value) (keys : List Key) (member : key ∈ keys) :
    latest state keys < latest (publish state key value) keys := by
  have old := latest_le_clock state valid keys
  have fresh : state.clock + 1 ≤ latest (publish state key value) keys := by
    simpa only [publish, Function.update_self] using epoch_le_latest (publish state key value) keys key member
  omega

theorem publish_same_latest_read (state : State Key Value) (valid : Valid state)
    (key : Key) (value : Value) (keys : List Key)
    (same : latest (publish state key value) keys = latest state keys) :
    read (publish state key value) keys = read state keys := by
  have absent : key ∉ keys := by
    intro member
    have changed := published_member_advances state valid key value keys member
    omega
  apply List.map_congr_left
  intro other member
  have different : other ≠ key := by rintro rfl; exact absent member
  rw [publish_other state key other value different]

def execute (state : State Key Value) : List (Key × Value) → State Key Value
  | [] => state
  | (key, value) :: rest => execute (publish state key value) rest

theorem execute_append (state : State Key Value) (first second : List (Key × Value)) :
    execute state (first ++ second) = execute (execute state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons event rest ih => exact ih _

theorem execute_valid (state : State Key Value) (valid : Valid state) (events : List (Key × Value)) :
    Valid (execute state events) := by
  induction events generalizing state with
  | nil => exact valid
  | cons event rest ih => exact ih _ (publish_valid state valid event.1 event.2)

theorem execute_latest_mono (state : State Key Value) (valid : Valid state)
    (events : List (Key × Value)) (keys : List Key) :
    latest state keys ≤ latest (execute state events) keys := by
  induction events generalizing state with
  | nil => exact Nat.le_refl _
  | cons event rest ih =>
      exact (publish_latest_mono state valid event.1 event.2 keys).trans
        (ih _ (publish_valid state valid event.1 event.2))

/-- Equality is established over a publication history, not assumed to make
the maximum an injective summary of unrelated directories. -/
theorem execute_same_latest_read (state : State Key Value) (valid : Valid state)
    (events : List (Key × Value)) (keys : List Key)
    (same : latest (execute state events) keys = latest state keys) :
    read (execute state events) keys = read state keys := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      have first := publish_latest_mono state valid event.1 event.2 keys
      have later := execute_latest_mono (publish state event.1 event.2)
        (publish_valid state valid event.1 event.2) rest keys
      have firstEq : latest (publish state event.1 event.2) keys = latest state keys := by
        change latest (execute (publish state event.1 event.2) rest) keys = latest state keys at same
        omega
      calc
        read (execute state (event :: rest)) keys = read (publish state event.1 event.2) keys :=
          ih _ (publish_valid state valid event.1 event.2) (by simpa [execute, firstEq] using same)
        _ = read state keys := publish_same_latest_read state valid event.1 event.2 keys firstEq

theorem execute_same_latest_value (state : State Key Value) (valid : Valid state)
    (events : List (Key × Value)) (keys : List Key)
    (same : latest (execute state events) keys = latest state keys) (key : Key) (member : key ∈ keys) :
    ((execute state events).cells key).value = (state.cells key).value :=
  List.map_inj_left.mp (execute_same_latest_read state valid events keys same) key member

/-- A finite word is faithful here only under the explicit non-wrapping
bound. Native overflow handling must establish this for successful histories. -/
theorem checked_word_same_read (state : State Key Value) (valid : Valid state)
    (events : List (Key × Value)) (keys : List Key)
    (oldBound : latest state keys < UInt64.size)
    (newBound : latest (execute state events) keys < UInt64.size)
    (same : UInt64.ofNat (latest (execute state events) keys) = UInt64.ofNat (latest state keys)) :
    read (execute state events) keys = read state keys := by
  have natural := congrArg UInt64.toNat same
  rw [UInt64.toNat_ofNat_of_lt' newBound, UInt64.toNat_ofNat_of_lt' oldBound] at natural
  exact execute_same_latest_read state valid events keys natural

end Mettapedia.Machines.IssuedEpochDirectory
