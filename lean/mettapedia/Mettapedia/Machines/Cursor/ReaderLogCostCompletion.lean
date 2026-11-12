import Mettapedia.Machines.Cursor.ReaderLogCost
import Mettapedia.Machines.RentOrBuyIndex

/-!
# Completing a retained reader after accumulated garbage work

The reader rents one inspection per encountered log entry until the rent
reaches its cached remaining-row count, then copies the remaining rows once.
Deliveries may shrink that count before the purchase. The actual copy walk
counts every copied cell, and the count is maintained by each delivery.

For every interleaving of deliveries and garbage encounters, rent plus copies
is at most twice the original remaining rows. This compares with copying the
original remainder, not with a clairvoyant copy of the final smaller remainder.
Each command also needs ordinary constant control work; that coordinate is
shown separately. Native allocation, physical slot width and log indexing are
not proved here. The initial row count must be already available metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderLogCostCompletion

variable {Value : Type}

def copyRows : List Value → List Value × Nat
  | [] => ([], 0)
  | value :: later =>
      let copied := copyRows later
      (value :: copied.1, 1 + copied.2)

theorem copyRows_exact (rows : List Value) :
    (copyRows rows).1 = rows ∧ (copyRows rows).2 = rows.length := by
  induction rows with
  | nil => exact ⟨rfl, rfl⟩
  | cons value later ih => simp [copyRows, ih, Nat.add_comm]

structure State (Value : Type) where
  remaining : List Value
  left : Nat
  owned : Bool
  rented : Nat
  copied : Nat
  delivered : Nat

def start (rows : List Value) (count : Nat) : State Value :=
  ⟨rows, count, false, 0, 0, 0⟩

def encounter (state : State Value) : State Value :=
  if state.owned then state
  else if state.left ≤ state.rented then
    let copied := copyRows state.remaining
    { state with remaining := copied.1, owned := true, copied := state.copied + copied.2 }
  else { state with rented := state.rented + 1 }

def deliver (state : State Value) : State Value :=
  match state.remaining with
  | [] => state
  | _ :: later =>
      { state with
        remaining := later
        left := state.left - 1
        delivered := state.delivered + 1 }

inductive Command where
  | garbage
  | answer
  deriving DecidableEq, Repr

def step (state : State Value) : Command → State Value
  | .garbage => encounter state
  | .answer => deliver state

def run : List Command → State Value → State Value
  | [], state => state
  | command :: later, state => run later (step state command)

def Valid (original : Nat) (state : State Value) : Prop :=
  state.left = state.remaining.length ∧
    state.left + state.delivered = original ∧
    state.rented ≤ original ∧ state.copied ≤ state.rented ∧
    (state.owned = false → state.copied = 0)

theorem start_valid (rows : List Value) (count : Nat) (known : count = rows.length) :
    Valid count (start rows count) := by simp [Valid, start, known]

theorem encounter_keeps_remaining (state : State Value) :
    (encounter state).remaining = state.remaining := by
  unfold encounter
  split
  · rfl
  · split
    · exact (copyRows_exact state.remaining).1
    · rfl

theorem encounter_valid (original : Nat) (state : State Value) (valid : Valid original state) :
    Valid original (encounter state) := by
  rcases valid with ⟨counted, conserved, rented, copies, unowned⟩
  unfold encounter
  split
  · exact ⟨counted, conserved, rented, copies, unowned⟩
  · rename_i notOwned
    have zeroCopies := unowned (by simpa using notOwned)
    split
    · rename_i affordable
      have copied := copyRows_exact state.remaining
      simp only [Valid, copied.1, copied.2]
      exact ⟨counted, conserved, rented, by omega, by simp⟩
    · rename_i tooEarly
      simp only [Valid]
      exact ⟨counted, conserved, by omega, by omega, fun _ => zeroCopies⟩

theorem deliver_valid (original : Nat) (state : State Value) (valid : Valid original state) :
    Valid original (deliver state) := by
  rcases valid with ⟨counted, conserved, rented, copies, unowned⟩
  unfold deliver
  cases rows : state.remaining with
  | nil => exact ⟨counted, conserved, rented, copies, unowned⟩
  | cons value later =>
      simp only [Valid]
      simp only [rows, List.length_cons] at counted
      exact ⟨by omega, by omega, rented, copies, unowned⟩

theorem run_valid (commands : List Command) (original : Nat) (state : State Value)
    (valid : Valid original state) : Valid original (run commands state) := by
  induction commands generalizing state with
  | nil => exact valid
  | cons command later ih =>
      apply ih
      cases command with
      | garbage => exact encounter_valid original state valid
      | answer => exact deliver_valid original state valid

/-- Even when deliveries reduce the purchase price, accumulated rent and
the actual one-time copy stay within twice the opening remainder. -/
theorem rent_and_copy_bound (rows : List Value) (count : Nat) (known : count = rows.length)
    (commands : List Command) :
    (run commands (start rows count)).rented +
      (run commands (start rows count)).copied ≤ 2 * count := by
  have valid := run_valid commands count (start rows count) (start_valid rows count known)
  rcases valid with ⟨_, _, rents, copies, _⟩
  omega

/-- Control inspections are not erased. Delivery plus garbage/copy work is
bounded, while the number of caller-issued commands remains explicit. -/
theorem total_work_bound (rows : List Value) (count : Nat) (known : count = rows.length)
    (commands : List Command) :
    commands.length + (run commands (start rows count)).rented +
        (run commands (start rows count)).copied +
        (run commands (start rows count)).delivered ≤
      commands.length + 3 * count := by
  have valid := run_valid commands count (start rows count) (start_valid rows count known)
  rcases valid with ⟨_, conservation, rents, copies, _⟩
  omega

/-- The no-delivery local policy has the same purchase decision as the
existing unit-rent, zero-after-purchase rent-or-buy machine. -/
def prices (count : Nat) : Mettapedia.Machines.RentOrBuyIndex.Prices :=
  ⟨1, count, 0, by decide, by decide⟩

def project (state : State Value) : Mettapedia.Machines.RentOrBuyIndex.St :=
  ⟨state.rented, state.owned⟩

theorem encounter_purchase_policy (state : State Value) :
    project (encounter state) =
      (Mettapedia.Machines.RentOrBuyIndex.step (prices state.left) (project state)).1 := by
  unfold encounter Mettapedia.Machines.RentOrBuyIndex.step project prices
  split <;> simp_all only
  split <;> rfl

example :
    let state := run [.garbage, .garbage] (start [1, 2, 3, 4] 4)
    state.rented = 2 ∧ state.copied = 0 ∧ state.owned = false := by decide

example :
    let state := run (List.replicate 20 .garbage) (start [1, 2, 3, 4] 4)
    state.rented = 4 ∧ state.copied = 4 ∧ state.owned = true := by decide

example :
    let state := run [.garbage, .garbage, .answer, .answer, .answer, .garbage]
      (start [1, 2, 3, 4] 4)
    state.rented = 2 ∧ state.copied = 1 ∧ state.remaining = [4] := by decide

/-- Comparing against twice the final remainder is false: useful deliveries
shrink it after rent has already been paid. -/
example :
    let state := run [.garbage, .garbage, .answer, .answer, .answer, .garbage]
      (start [1, 2, 3, 4] 4)
    2 * state.left < state.rented + state.copied := by decide

end Mettapedia.Machines.Cursor.ReaderLogCostCompletion
