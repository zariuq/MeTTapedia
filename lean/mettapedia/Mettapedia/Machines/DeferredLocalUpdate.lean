import Mathlib.Tactic

/-!
# What must stay stable while an update is deferred

A split update reads a slot, computes, and later publishes an absolute
value. Its dependence on the intervening writes is local, not global.
Ignoring changes is correct at the write point exactly when they leave the
computed value unchanged. For injective updates, this means stability of
the slot's readout. Independent contributions need not be overwritten at
all: a commutative delta can be applied to the current value instead.

This is reasoning over a history of atomic observations and publications.
A count of active workers is not a reservation of a future interval, and
a publication history says nothing about native memory ordering, the
validity of addresses, or the lifetime of a reader's loan.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeferredLocalUpdate

variable {Slot Value : Type*} [DecidableEq Slot]

abbrev Write (Slot Value : Type*) := Slot × (Value → Value)

def perform (state : Slot → Value) (edit : Write Slot Value) : Slot → Value :=
  Function.update state edit.1 (edit.2 (state edit.1))

def replay (state : Slot → Value) : List (Write Slot Value) → Slot → Value
  | [] => state
  | edit :: rest => replay (perform state edit) rest

def actionsAt (slot : Slot) (edits : List (Write Slot Value)) : List (Value → Value) :=
  edits.filterMap fun edit => if edit.1 = slot then some edit.2 else none

/-- Projecting a write history to one key can be done before replay; all
other writes remain allowed, including if they straddle the deferred read. -/
theorem replay_at (state : Slot → Value) (edits : List (Write Slot Value)) (slot : Slot) :
    replay state edits slot = (actionsAt slot edits).foldl (fun value update => update value) (state slot) := by
  induction edits generalizing state with
  | nil => rfl
  | cons edit rest ih =>
      obtain ⟨key, update⟩ := edit
      simp only [replay, ih, actionsAt, List.filterMap_cons]
      by_cases same : key = slot
      · subst key
        simp [perform]
      · simp [perform, same, Ne.symm same]

def overwrite (before : Slot → Value) (slot : Slot) (change : Value → Value)
    (edits : List (Write Slot Value)) : Slot → Value :=
  Function.update (replay before edits) slot (change (before slot))

/-- Exact characterization at the publication cut. A non-injective
overwrite may forget some interfering updates deliberately. -/
theorem overwrite_eq_current_iff (before : Slot → Value) (slot : Slot) (change : Value → Value)
    (edits : List (Write Slot Value)) :
    overwrite before slot change edits = perform (replay before edits) (slot, change) ↔
      change (before slot) = change (replay before edits slot) := by
  constructor
  · intro same
    simpa [overwrite, perform] using congrFun same slot
  · intro same
    simp only [overwrite, perform, same]

theorem injective_overwrite_iff_stable (before : Slot → Value) (slot : Slot)
    (change : Value → Value) (edits : List (Write Slot Value)) (recover : Function.Injective change) :
    overwrite before slot change edits = perform (replay before edits) (slot, change) ↔
      before slot = replay before edits slot := by
  rw [overwrite_eq_current_iff]
  exact recover.eq_iff

/-- Exclusion of conflicting edits is sufficient; exclusion of unrelated
threads or keys does not contribute to the equality. -/
theorem disjoint_edits_need_no_exclusion (before : Slot → Value) (slot : Slot)
    (change : Value → Value) (edits : List (Write Slot Value))
    (untouched : actionsAt slot edits = []) :
    overwrite before slot change edits = perform (replay before edits) (slot, change) := by
  rw [overwrite_eq_current_iff, replay_at, untouched]
  rfl

section Contributions

variable [AddCommMonoid Value]

def contribution (slot : Slot) (part : Value) : Write Slot Value := (slot, (· + part))

/-- If the proposed update is an independent contribution, it merges at
publication instead of overwriting a value computed from an old sample.
This includes idempotent union as well as additive accumulation. -/
theorem contributions_commute (state : Slot → Value) (a b : Slot) (left right : Value) :
    perform (perform state (contribution a left)) (contribution b right) =
      perform (perform state (contribution b right)) (contribution a left) := by
  funext slot
  by_cases ab : a = b
  · subst b
    by_cases atA : slot = a
    · subst slot; simp [perform, contribution, add_right_comm]
    · simp [perform, contribution, atA]
  · by_cases atA : slot = a
    · subst slot; simp [perform, contribution, ab]
    · by_cases atB : slot = b
      · subst slot; simp [perform, contribution, Ne.symm ab]
      · simp [perform, contribution, atA, atB]

end Contributions

/-- Even two commuting increments are not serializable as an absolute
read/compute/overwrite combined with a concurrent atomic increment. -/
theorem lost_update_in_neither_serial_order (before : Slot → Nat) (slot : Slot)
    (own another : Nat) (nonzero : 0 < another) :
    let other := contribution slot another
    let usual := contribution slot own
    overwrite before slot (· + own) [other] ≠ perform (perform before other) usual ∧
      overwrite before slot (· + own) [other] ≠ perform (perform before usual) other := by
  dsimp only
  rw [← contributions_commute before slot slot own another]
  constructor <;> intro same <;>
    have atSlot := congrFun same slot <;>
    simp [overwrite, replay, perform, contribution] at atSlot <;> omega

namespace Controls

/-- The worker is counted before its write and released afterwards. The
counter nevertheless has value zero at both ends of an outer split update.
The counts are read, not held as exclusive permission for that interval. -/
theorem zero_at_both_ends_can_hide_a_worker :
    let active := fun t : Nat => if 1 ≤ t ∧ t < 3 then (1 : Nat) else 0
    let initial := fun _ : Unit => 0
    let worker := contribution () 1
    active 0 = 0 ∧ active 2 = 1 ∧ active 4 = 0 ∧
      overwrite initial () (· + 1) [worker] () = 1 ∧
      perform (perform initial worker) (contribution () 1) () = 2 := by decide

theorem adding_elsewhere_preserves_pending_update :
    let initial := fun _ : Bool => 0
    overwrite initial false (· + 1) [contribution true 1] =
      perform (perform initial (contribution true 1)) (contribution false 1) := by
  exact disjoint_edits_need_no_exclusion _ _ _ _ (by decide)

end Controls
end Mettapedia.Machines.DeferredLocalUpdate
