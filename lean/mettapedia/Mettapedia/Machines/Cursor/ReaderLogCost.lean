import Mathlib.Tactic

/-!
# Shared death logs: publication, catch-up and retained garbage

A removal publishes one identified occurrence in a shared append-only log.
Readers retain absolute offsets and inspect that log only when they catch up.
The executable scanner below proves exact per-reader work, including repeated
catch-ups. A shared log removes notification work from a writer; it does not
erase the work of every reader inspecting the same published occurrence.

The meters count published log cells and inspected existing cells. Array
growth, record payload bytes, lookup instructions, synchronization and native
retention require separate accounts. A high-level removal of many occurrences
publishes many death cells, not one constant-price write.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderLogCost

variable {Value : Type}

structure Reader where
  offset : Nat
  inspected : Nat
  deriving DecidableEq, Repr

def openReader (log : Array Value) : Reader := ⟨log.size, 0⟩

/-- Publishing changes neither the positions nor the work of existing readers.
Readers retain offsets into the current log, not pointers into an old array. -/
structure Shared (Value : Type) (readers : Nat) where
  log : Array Value
  views : Fin readers → Reader
  published : Nat

def append {readers : Nat} (state : Shared Value readers) (value : Value) :
    Shared Value readers :=
  { state with log := state.log.push value, published := state.published + 1 }

@[simp] theorem append_keeps_readers {readers : Nat} (state : Shared Value readers)
    (value : Value) : (append state value).views = state.views := rfl

theorem append_one_publication {readers : Nat} (state : Shared Value readers)
    (value : Value) : (append state value).published = state.published + 1 := rfl

theorem append_keeps_old_cell {readers : Nat} (state : Shared Value readers)
    (value : Value) (position : Nat) (old : position < state.log.size) :
    (append state value).log[position]? = state.log[position]? := by
  simp only [append, Array.getElem?_push, if_neg (ne_of_lt old)]

/-- The alternative writer really visits each reader and updates its inbox. -/
def notifyAll (value : Value) : List (Array Value) → Nat × List (Array Value)
  | [] => (0, [])
  | inbox :: later =>
      let notified := notifyAll value later
      (1 + notified.1, inbox.push value :: notified.2)

theorem notifications_exact (value : Value) (inboxes : List (Array Value)) :
    (notifyAll value inboxes).1 = inboxes.length := by
  induction inboxes with
  | nil => rfl
  | cons inbox later ih => simp [notifyAll, ih, Nat.add_comm]

theorem notifications_have_no_uniform_bound (value : Value) (bound : Nat) :
    ∃ inboxes : List (Array Value), bound < (notifyAll value inboxes).1 := by
  refine ⟨List.replicate (bound + 1) #[], ?_⟩
  rw [notifications_exact]
  simp

def poll (log : Array Value) (reader : Reader) : Option Value × Reader :=
  match log[reader.offset]? with
  | none => (none, reader)
  | some value => (some value, ⟨reader.offset + 1, reader.inspected + 1⟩)

/-- Each successful poll advances one absolute position and accounts for its
inspection; an exhausted poll does not claim to inspect a nonexistent cell. -/
theorem poll_account (log : Array Value) (reader : Reader) :
    (poll log reader).2.inspected + reader.offset =
      reader.inspected + (poll log reader).2.offset := by
  cases found : log[reader.offset]? <;>
    simp [poll, found, Nat.add_comm, Nat.add_left_comm]

def drain (log : Array Value) : Nat → Reader → List Value × Reader
  | 0, reader => ([], reader)
  | amount + 1, reader =>
      match poll log reader with
      | (none, next) => ([], next)
      | (some value, next) =>
          let rest := drain log amount next
          (value :: rest.1, rest.2)

/-- This bound is derived from the actual cell-by-cell scanner, not from a
formula assigned to a completed scan. It preserves occurrence multiplicity. -/
theorem drain_exact (log : Array Value) (amount : Nat) (reader : Reader)
    (fits : reader.offset + amount ≤ log.size) :
    (drain log amount reader).2.offset = reader.offset + amount ∧
      (drain log amount reader).2.inspected = reader.inspected + amount ∧
      (drain log amount reader).1.length = amount := by
  induction amount generalizing reader with
  | zero => simp [drain]
  | succ amount ih =>
      cases found : log[reader.offset]? with
      | none =>
          have outside := Array.getElem?_eq_none_iff.mp found
          omega
      | some value =>
          have later := ih ⟨reader.offset + 1, reader.inspected + 1⟩ (by dsimp; omega)
          simp only [drain, poll, found]
          simp only [List.length_cons]
          exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later.1,
            by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later.2.1,
            by omega⟩

def catchUp (log : Array Value) (reader : Reader) : List Value × Reader :=
  drain log (log.size - reader.offset) reader

theorem catchUp_exact (log : Array Value) (reader : Reader) (valid : reader.offset ≤ log.size) :
    (catchUp log reader).2.offset = log.size ∧
      (catchUp log reader).2.inspected = reader.inspected + (log.size - reader.offset) ∧
      (catchUp log reader).1.length = log.size - reader.offset := by
  have executed := drain_exact log (log.size - reader.offset) reader (by omega)
  exact ⟨by simpa [catchUp, Nat.add_sub_of_le valid] using executed.1,
    executed.2.1, executed.2.2⟩

theorem catchUp_twice_no_replay (log : Array Value) (reader : Reader)
    (valid : reader.offset ≤ log.size) :
    catchUp log (catchUp log reader).2 = ([], (catchUp log reader).2) := by
  have reached := (catchUp_exact log reader valid).1
  change drain log (log.size - (catchUp log reader).2.offset)
    (catchUp log reader).2 = _
  rw [reached, Nat.sub_self]
  rfl

theorem new_reader_skips_old_log (log : Array Value) :
    catchUp log (openReader log) = ([], openReader log) := by
  simp [catchUp, openReader, drain]

/-- Every reader catches up independently. Publishing one log entry once
does not imply it is inspected once globally. -/
def catchAll (log : Array Value) : List Reader → Nat × List Reader
  | [] => (0, [])
  | reader :: later =>
      let read := catchUp log reader
      let rest := catchAll log later
      (read.1.length + rest.1, read.2 :: rest.2)

theorem cohort_catchUp_work (log : Array Value) (readers : Nat) :
    (catchAll log (List.replicate readers ⟨0, 0⟩)).1 = readers * log.size := by
  induction readers with
  | zero => simp [catchAll]
  | succ readers ih =>
      have length := (catchUp_exact log ⟨0, 0⟩ (by simp)).2.2
      rw [List.replicate_succ, catchAll, length, ih]
      simp [Nat.add_mul, Nat.add_comm]

/-- The single log shifts the R-by-W work to readers. There is no universal
constant bounding this catch-up work by readers plus publications alone. -/
theorem no_global_linear_catchUp_bound (coefficient : Nat) :
    ∃ (log : Array Unit) (readers : Nat),
      coefficient * (readers + log.size) <
        (catchAll log (List.replicate readers ⟨0, 0⟩)).1 := by
  let size := 2 * coefficient + 1
  refine ⟨(List.replicate size ()).toArray, size, ?_⟩
  rw [cohort_catchUp_work]
  simp only [List.size_toArray, List.length_replicate]
  dsimp [size]
  nlinarith

/-- Unique removed occurrences retained since a reader opened are bounded by
the number of death entries published during that lifetime. This counts
occurrences, not high-level removal calls or physical bytes/capacity. -/
def pinnedVictims [DecidableEq Value] (log : Array Value) (openedAt : Nat) : Finset Value :=
  (log.toList.drop openedAt).toFinset

theorem pinned_victims_le_deaths [DecidableEq Value] (log : Array Value) (openedAt : Nat) :
    (pinnedVictims log openedAt).card ≤ log.size - openedAt := by
  unfold pinnedVictims
  calc
    (log.toList.drop openedAt).toFinset.card ≤ (log.toList.drop openedAt).length :=
      List.toFinset_card_le _
    _ = log.size - openedAt := by simp

/-- A settlement that scans the complete physical table, copying live rows
and discarding tombstones. Closing the last reader does not make this scan
free; occupancy-triggered settlement needs its own amortization argument. -/
def compact : List (Option Value) → List Value × Nat
  | [] => ([], 0)
  | none :: later =>
      let rest := compact later
      (rest.1, 1 + rest.2)
  | some value :: later =>
      let rest := compact later
      (value :: rest.1, 1 + rest.2)

theorem compaction_inspects_every_slot (rows : List (Option Value)) :
    (compact rows).2 = rows.length := by
  induction rows with
  | nil => rfl
  | cons row later ih => cases row <;> simp [compact, ih, Nat.add_comm]

/-- One removed row can force unbounded work if closing the final reader
unconditionally compacts all pre-existing live rows. -/
theorem one_death_settlement_unbounded (value : Value) (bound : Nat) :
    bound < (compact (none :: List.replicate bound (some value))).2 := by
  rw [compaction_inspects_every_slot]
  simp

example : (notifyAll 7 [#[], #[], #[]]).1 = 3 := by decide
example : (catchAll #[1, 2, 3, 4] [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]).1 = 12 := by decide
example : (catchUp #[1, 2, 3, 4] ⟨4, 0⟩).1 = [] := by decide
example : (catchUp #[1, 2, 3, 4] ⟨0, 0⟩).2.inspected = 4 := by decide
example : (pinnedVictims #[7, 7, 9] 0).card = 2 := by decide
example : compact [none, some 7, some 8, some 9] = ([7, 8, 9], 4) := by decide

end Mettapedia.Machines.Cursor.ReaderLogCost
