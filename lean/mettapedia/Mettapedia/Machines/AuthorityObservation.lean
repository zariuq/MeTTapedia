import Mathlib.Tactic

/-!
# Direct comparison of an authority observation

The reference reads every authority component into a temporary snapshot and
then compares the recorded words. The target compares each observation at
once and stops at the first mismatch. Observers may update internal cache
state, so rejected runs need not end in identical physical states. Acceptance
is exact, accepted final states agree, and an observer preserving a public
projection cannot introduce a visible difference on refusal.

Native field/getter correspondence and the absence of language-visible getter
effects remain implementation obligations. This is not an authority cache or
a replacement for source, library or ownership admission.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AuthorityObservation

inductive Field where
  | foreignInstance | foreignRevision | semanticEpoch | transaction
  | translators | admission | capabilities | activeLibraries
  deriving DecidableEq, Repr

def inventory : List Field :=
  [.foreignInstance, .foreignRevision, .semanticEpoch, .transaction,
    .translators, .admission, .capabilities, .activeLibraries]

theorem inventory_complete : ∀ field : Field, field ∈ inventory := by
  intro field
  cases field <;> simp [inventory]

theorem inventory_distinct : inventory.Nodup := by decide

variable {Key Word State Public : Type} [DecidableEq Word]

def snapshot (observe : Key → State → Word × State) : List Key → State → List Word × State
  | [], state => ([], state)
  | key :: later, state =>
      let first := observe key state
      let tail := snapshot observe later first.2
      (first.1 :: tail.1, tail.2)

structure Result (State : Type) where
  accepted : Bool
  state : State
  reads : Nat
  deriving DecidableEq, Repr

def compare (expected : Key → Word) (observe : Key → State → Word × State) :
    List Key → State → Result State
  | [], state => ⟨true, state, 0⟩
  | key :: later, state =>
      let first := observe key state
      if first.1 = expected key then
        let tail := compare expected observe later first.2
        ⟨tail.accepted, tail.state, tail.reads + 1⟩
      else ⟨false, first.2, 1⟩

def reference (expected : Key → Word) (observe : Key → State → Word × State)
    (keys : List Key) (state : State) : Bool × State :=
  let read := snapshot observe keys state
  (decide (read.1 = keys.map expected), read.2)

theorem acceptance_refines (expected : Key → Word)
    (observe : Key → State → Word × State) (keys : List Key) (state : State) :
    (compare expected observe keys state).accepted = (reference expected observe keys state).1 := by
  induction keys generalizing state with
  | nil => rfl
  | cons key later ih =>
      by_cases same : (observe key state).1 = expected key
      · simpa [compare, reference, snapshot, same] using ih (observe key state).2
      · simp [compare, reference, snapshot, same]

theorem accepted_state_refines (expected : Key → Word)
    (observe : Key → State → Word × State) (keys : List Key) (state : State)
    (accepted : (compare expected observe keys state).accepted = true) :
    (compare expected observe keys state).state = (reference expected observe keys state).2 := by
  induction keys generalizing state with
  | nil => rfl
  | cons key later ih =>
      by_cases same : (observe key state).1 = expected key
      · have tail : (compare expected observe later (observe key state).2).accepted = true := by
          simpa [compare, same] using accepted
        simpa [compare, reference, snapshot, same] using ih (observe key state).2 tail
      · simp [compare, same] at accepted

theorem reads_bounded (expected : Key → Word)
    (observe : Key → State → Word × State) (keys : List Key) (state : State) :
    (compare expected observe keys state).reads ≤ keys.length := by
  induction keys generalizing state with
  | nil => simp [compare]
  | cons key later ih =>
      by_cases same : (observe key state).1 = expected key
      · simpa [compare, same] using Nat.add_le_add_right (ih (observe key state).2) 1
      · simp [compare, same]

theorem accepted_reads_complete (expected : Key → Word)
    (observe : Key → State → Word × State) (keys : List Key) (state : State)
    (accepted : (compare expected observe keys state).accepted = true) :
    (compare expected observe keys state).reads = keys.length := by
  induction keys generalizing state with
  | nil => rfl
  | cons key later ih =>
      by_cases same : (observe key state).1 = expected key
      · have tail : (compare expected observe later (observe key state).2).accepted = true := by
          simpa [compare, same] using accepted
        simpa [compare, same] using ih (observe key state).2 tail
      · simp [compare, same] at accepted

theorem compare_preserves_public (expected : Key → Word)
    (observe : Key → State → Word × State) (view : State → Public)
    (preserves : ∀ key state, view (observe key state).2 = view state)
    (keys : List Key) (state : State) :
    view (compare expected observe keys state).state = view state := by
  induction keys generalizing state with
  | nil => rfl
  | cons key later ih =>
      by_cases same : (observe key state).1 = expected key
      · simpa [compare, same] using (ih (observe key state).2).trans (preserves key state)
      · simpa [compare, same] using preserves key state

omit [DecidableEq Word] in
theorem snapshot_preserves_public (observe : Key → State → Word × State)
    (view : State → Public)
    (preserves : ∀ key state, view (observe key state).2 = view state)
    (keys : List Key) (state : State) :
    view (snapshot observe keys state).2 = view state := by
  induction keys generalizing state with
  | nil => rfl
  | cons key later ih =>
      simpa [snapshot] using (ih (observe key state).2).trans (preserves key state)

theorem public_state_refines (expected : Key → Word)
    (observe : Key → State → Word × State) (view : State → Public)
    (preserves : ∀ key state, view (observe key state).2 = view state)
    (keys : List Key) (state : State) :
    view (compare expected observe keys state).state =
      view (reference expected observe keys state).2 :=
  (compare_preserves_public expected observe view preserves keys state).trans
    (snapshot_preserves_public observe view preserves keys state).symm

def current (expected : Field → Word) (observe : Field → State → Word × State)
    (length : Nat) (state : State) : Result State :=
  if length = inventory.length then compare expected observe inventory state
  else ⟨false, state, 0⟩

theorem wrong_length_reads_nothing (expected : Field → Word)
    (observe : Field → State → Word × State) (length : Nat) (state : State)
    (wrong : length ≠ inventory.length) :
    current expected observe length state = ⟨false, state, 0⟩ := by
  simp [current, wrong]

namespace Controls

def expected : Field → Nat := fun _ => 7
def observe (bad : Option Field) (key : Field) (state : Nat) : Nat × Nat :=
  (if bad = some key then 8 else 7, state + 1)

theorem every_component_is_required (field : Field) :
    (current expected (observe (some field)) 8 0).accepted = false := by
  cases field <;> decide +kernel

theorem matching_snapshot_reads_all_fields :
    current expected (observe none) 8 0 = ⟨true, 8, 8⟩ := by decide +kernel

theorem mismatch_can_stop_before_snapshot_completion :
    (current expected (observe (some .foreignInstance)) 8 0).state = 1 ∧
    (reference expected (observe (some .foreignInstance)) inventory 0).2 = 8 ∧
    (current expected (observe (some .foreignInstance)) 8 0).accepted =
      (reference expected (observe (some .foreignInstance)) inventory 0).1 := by
  decide +kernel

theorem late_fields_are_not_optional :
    (compare expected (observe (some .capabilities)) (inventory.take 5) 0).accepted = true ∧
    (current expected (observe (some .capabilities)) 8 0).accepted = false := by
  decide +kernel

end Controls
end Mettapedia.Machines.AuthorityObservation
