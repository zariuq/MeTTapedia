import Mettapedia.Machines.MarkedUndoLog

/-!
# Rolling back a partial boolean-unification trial

A failed comparison can have bound several cells before finding a mismatch.
The trial logs the incoming payload of every write, including cells younger
than the enclosing search choice. Undo restores the complete incoming store.
On success the refined store is retained. The writes are arbitrary; whether
the native unifier chooses the correct writes is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.UnificationTrial

open MarkedUndoLog

variable {Slot Payload : Type} [DecidableEq Slot]

def execute : List (Slot × Payload) → (Slot → Payload) →
    (Slot → Payload) × List (Slot × Payload)
  | [], store => (store, [])
  | (slot, value) :: rest, store =>
      let later := execute rest (Function.update store slot value)
      (later.1, (slot, store slot) :: later.2)

theorem undo_complete (writes : List (Slot × Payload)) (store : Slot → Payload) :
    rollback (execute writes store).2 (execute writes store).1 = store := by
  induction writes generalizing store with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨slot, value⟩
      simp only [execute, rollback, List.foldr_cons]
      change restore (slot, store slot)
        (rollback (execute rest (Function.update store slot value)).2
          (execute rest (Function.update store slot value)).1) = store
      rw [ih]
      funext observed
      by_cases same : observed = slot
      · subst observed
        simp [restore]
      · simp [restore, same]

def finish (success : Bool) (writes : List (Slot × Payload)) (store : Slot → Payload) :
    Bool × (Slot → Payload) :=
  let trial := execute writes store
  (success, if success then trial.1 else rollback trial.2 trial.1)

theorem failed_trial (writes : List (Slot × Payload)) (store : Slot → Payload) :
    finish false writes store = (false, store) := by
  simp [finish, undo_complete]

theorem successful_trial (writes : List (Slot × Payload)) (store : Slot → Payload) :
    finish true writes store = (true, (execute writes store).1) := rfl

example : (finish false [(0, 9), (1, 8), (0, 7)] (fun i : Nat => i)).2 0 = 0 := by
  rw [failed_trial]

example : (finish true [(0, 9), (1, 8), (0, 7)] (fun i : Nat => i)).2 0 = 7 := by
  decide

example : (execute [(0, 9), (1, 8)] (fun i : Nat => i)).1 0 ≠ 0 := by decide

#print axioms undo_complete
#print axioms failed_trial
#print axioms successful_trial

end Mettapedia.Machines.UnificationTrial
