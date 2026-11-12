import Mettapedia.Machines.Cursor.ReaderLogCost

/-!
# Nested short readers: a scan counterexample and a nonpersistent index

This concrete subcalculus appends fresh numbered rows and removes the current
first row. Its live rows form an interval. An old reader retains the interval
at entry, while two current interval bounds index the first live row. No old
store versions are needed for this workload.

By contrast, a fresh scalar visibility scan from physical row zero rereads
every old prefix tombstone. Each short reader pays the prefix length again.
Thus scalar tombstone scanning is slow here, but absence of persistence alone
does not imply that cost: the maintained current-live index avoids it.

The metrics count Boolean visibility-cell probes and scalar index-field loads.
They do not model arbitrary deletion, arbitrary patterns, payload mutation,
multicore synchronization, arithmetic bit complexity or CPU instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderLogCostNested

structure Interval where
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

def Valid (store : Interval) : Prop := store.lower ≤ store.upper

def append (store : Interval) : Interval := { store with upper := store.upper + 1 }

def pop (store : Interval) : Interval :=
  if store.lower < store.upper then { store with lower := store.lower + 1 } else store

theorem append_valid (store : Interval) (valid : Valid store) : Valid (append store) := by
  simp only [Valid, append] at *
  omega

theorem pop_valid (store : Interval) (valid : Valid store) : Valid (pop store) := by
  unfold pop
  split
  · change store.lower + 1 ≤ store.upper
    unfold Valid at valid
    omega
  · exact valid

/-- Physical rows before `lower` are tombstoned but keep their identities. -/
def visibility (store : Interval) : List Bool :=
  List.replicate store.lower false ++ List.replicate (store.upper - store.lower) true

def firstVisible : List Bool → Nat × Option Nat
  | [] => (0, none)
  | true :: _ => (1, some 0)
  | false :: later =>
      let reply := firstVisible later
      (1 + reply.1, reply.2.map Nat.succ)

theorem scan_dead_prefix (dead tail : Nat) :
    firstVisible (List.replicate dead false ++ true :: List.replicate tail true) =
      (dead + 1, some dead) := by
  induction dead with
  | zero => simp [firstVisible]
  | succ dead ih => simp [List.replicate_succ, firstVisible, ih, Nat.add_comm]

theorem scan_all_dead (dead : Nat) :
    firstVisible (List.replicate dead false) = (dead, none) := by
  induction dead with
  | zero => rfl
  | succ dead ih => simp [List.replicate_succ, firstVisible, ih, Nat.add_comm]

def loadLower (store : Interval) : Nat × Nat := (store.lower, 1)
def loadUpper (store : Interval) : Nat × Nat := (store.upper, 1)

/-- The index really reads two maintained scalar fields, rather than walking
the physical visibility cells. -/
def firstIndexed (store : Interval) : Nat × Option Nat :=
  let lower := loadLower store
  let upper := loadUpper store
  (lower.2 + upper.2, if lower.1 < upper.1 then some lower.1 else none)

theorem current_index_correct (store : Interval) (valid : Valid store) :
    (firstIndexed store).2 = (firstVisible (visibility store)).2 := by
  by_cases present : store.lower < store.upper
  · have split : store.upper - store.lower = (store.upper - store.lower - 1) + 1 := by omega
    change (if store.lower < store.upper then some store.lower else none) = _
    rw [if_pos present, visibility, split, List.replicate_succ, scan_dead_prefix]
  · have same : store.upper = store.lower := by unfold Valid at valid; omega
    simp [firstIndexed, loadLower, loadUpper, visibility, same, scan_all_dead]

theorem current_index_two_loads (store : Interval) : (firstIndexed store).1 = 2 := rfl

theorem fresh_scan_work (store : Interval) (present : store.lower < store.upper) :
    (firstVisible (visibility store)).1 = store.lower + 1 := by
  have split : store.upper - store.lower = (store.upper - store.lower - 1) + 1 := by omega
  rw [visibility, split, List.replicate_succ, scan_dead_prefix]

def shortReaders (store : Interval) : Nat → Nat × List (Option Nat)
  | 0 => (0, [])
  | amount + 1 =>
      let first := firstVisible (visibility store)
      let later := shortReaders store amount
      (first.1 + later.1, first.2 :: later.2)

theorem nested_short_scan_work (store : Interval) (present : store.lower < store.upper)
    (readers : Nat) : (shortReaders store readers).1 = readers * (store.lower + 1) := by
  induction readers with
  | zero => simp [shortReaders]
  | succ readers ih =>
      simp [shortReaders, fresh_scan_work store present, ih, Nat.add_mul, Nat.add_comm]

/-- Entry readers retain their lower and upper bounds. Existing row payloads
in this subcalculus are their immutable serials, so later prefix pops and fresh
appends cannot change the sequence bounded by those two captured numbers. -/
def readerNext (reader : Interval) : Option Nat × Interval :=
  if reader.lower < reader.upper then
    (some reader.lower, { reader with lower := reader.lower + 1 })
  else (none, reader)

example :
    let old := (⟨0, 4⟩ : Interval)
    let current := pop (pop (pop old))
    (readerNext old).1 = some 0 ∧ (firstIndexed current).2 = some 3 ∧
      (firstVisible (visibility current)).1 = 4 := by decide

example : (shortReaders ⟨100, 101⟩ 10).1 = 1010 ∧
    (firstIndexed ⟨100, 101⟩).1 = 2 := by decide

example :
    let old := (⟨0, 1⟩ : Interval)
    let current := append (pop old)
    (readerNext old).1 = some 0 ∧ (firstIndexed current).2 = some 1 := by decide

end Mettapedia.Machines.Cursor.ReaderLogCostNested
