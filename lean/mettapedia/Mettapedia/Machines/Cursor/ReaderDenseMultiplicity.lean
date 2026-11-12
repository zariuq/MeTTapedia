import Mathlib.Tactic

/-!
# Entry multiplicity for a packed tuple reader

A tuple is stored once with a versioned count, not once per logical copy.
A reader keeps its entry epoch and lazily caches only the count of its current
tuple. The first visit asks for that tuple's count at entry, never its live
count at visit time. Later writes preserve this historical lookup.

The histories are one executable logical mechanism, not a requirement that a
native implementation use lists or preserve one row per copy. Their lookup
cost, packed-word layout, native lifetime and reclamation need separate bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderDenseMultiplicity

structure Version where
  time : Nat
  copies : Nat
  deriving Repr, DecidableEq

def lookupCount (time : Nat) : List Version → Nat
  | [] => 0
  | version :: rest => if version.time ≤ time then version.copies else lookupCount time rest

structure Table where
  clock : Nat
  nextTuple : Nat
  histories : Nat → List Version

def countAt (table : Table) (time tuple : Nat) : Nat := lookupCount time (table.histories tuple)

def liveCount (table : Table) (tuple : Nat) : Nat := countAt table table.clock tuple

def publish (table : Table) (tuple copies : Nat) : Table :=
  ⟨table.clock + 1, table.nextTuple,
    Function.update table.histories tuple (⟨table.clock + 1, copies⟩ :: table.histories tuple)⟩

def addCopy (table : Table) (tuple : Nat) : Table := publish table tuple (liveCount table tuple + 1)
def removeOne (table : Table) (tuple : Nat) : Table := publish table tuple (liveCount table tuple - 1)
def removeAll (table : Table) (tuple : Nat) : Table := publish table tuple 0

def edits : Table → List (Nat × Nat) → Table
  | table, [] => table
  | table, (tuple, copies) :: rest => edits (publish table tuple copies) rest

theorem countAt_publish_past (table : Table) (changed copies time tuple : Nat)
    (past : time ≤ table.clock) :
    countAt (publish table changed copies) time tuple = countAt table time tuple := by
  by_cases same : tuple = changed
  · subst tuple
    simp [countAt, publish, lookupCount, show ¬table.clock + 1 ≤ time by omega]
  · simp [countAt, publish, Function.update_of_ne same]

theorem countAt_all_edits (table : Table) (changes : List (Nat × Nat)) (time tuple : Nat)
    (past : time ≤ table.clock) :
    countAt (edits table changes) time tuple = countAt table time tuple := by
  induction changes generalizing table with
  | nil => rfl
  | cons change changes ih =>
      rcases change with ⟨changed, copies⟩
      rw [edits, ih _ (by dsimp [publish]; omega), countAt_publish_past _ _ _ _ _ past]

/-- A completed semantic observation expands logical copies. The packed
implementation state above stores histories and scalar counts, not this list. -/
def entryCopies (table : Table) (time ceiling : Nat) : List Nat :=
  (List.range ceiling).flatMap (fun tuple => List.replicate (countAt table time tuple) tuple)

theorem entry_copies_all_edits (table : Table) (changes : List (Nat × Nat)) (time ceiling : Nat)
    (past : time ≤ table.clock) :
    entryCopies (edits table changes) time ceiling = entryCopies table time ceiling := by
  unfold entryCopies
  congr 1
  funext tuple
  rw [countAt_all_edits table changes time tuple past]

theorem publish_live (table : Table) (tuple copies : Nat) :
    liveCount (publish table tuple copies) tuple = copies := by
  simp [liveCount, countAt, publish, lookupCount]

def HistoryBound (table : Table) : Prop :=
  ∀ tuple version, version ∈ table.histories tuple → version.time ≤ table.clock

theorem history_bound_publish (table : Table) (valid : HistoryBound table) (changed copies : Nat) :
    HistoryBound (publish table changed copies) := by
  intro tuple version member
  by_cases same : tuple = changed
  · subst tuple
    simp [publish] at member
    rcases member with newest | older
    · cases newest
      exact le_rfl
    · exact (valid changed version older).trans (Nat.le_succ _)
  · simp only [publish, Function.update_of_ne same] at member
    exact (valid tuple version member).trans (Nat.le_succ _)

structure Reader where
  epoch : Nat
  ceiling : Nat
  tuple : Nat
  used : Nat
  cached : Option Nat
  deriving Repr, DecidableEq

def start (table : Table) : Reader := ⟨table.clock, table.nextTuple, 0, 0, none⟩

def quota (table : Table) (reader : Reader) : Nat :=
  match reader.cached with
  | some copies => copies
  | none => countAt table reader.epoch reader.tuple

inductive Reply where
  | exhausted
  | skip
  | copy (tuple : Nat) (ordinal : Nat)
  deriving Repr, DecidableEq

/-- One internal step either delivers one logical copy, advances to the next
tuple, or reports exhaustion. No expanded per-copy row list is stored. -/
def step (table : Table) (reader : Reader) : Reply × Reader :=
  if reader.tuple < reader.ceiling then
    let copies := quota table reader
    if reader.used < copies then
      (.copy reader.tuple reader.used,
        { reader with used := reader.used + 1, cached := some copies })
    else
      (.skip, { reader with tuple := reader.tuple + 1, used := 0, cached := none })
  else (.exhausted, reader)

def CacheSound (table : Table) (reader : Reader) : Prop :=
  ∀ copies, reader.cached = some copies → copies = countAt table reader.epoch reader.tuple

theorem quota_is_entry_count (table : Table) (reader : Reader) (sound : CacheSound table reader) :
    quota table reader = countAt table reader.epoch reader.tuple := by
  cases held : reader.cached with
  | none => simp [quota, held]
  | some copies => simpa [quota, held] using sound copies held

theorem cache_sound_start (table : Table) : CacheSound table (start table) := by
  intro copies held
  cases held

theorem cache_sound_publish (table : Table) (reader : Reader) (sound : CacheSound table reader)
    (past : reader.epoch ≤ table.clock) (changed copies : Nat) :
    CacheSound (publish table changed copies) reader := by
  intro cached held
  rw [countAt_publish_past table changed copies reader.epoch reader.tuple past]
  exact sound cached held

theorem step_cache_sound (table : Table) (reader : Reader) (sound : CacheSound table reader) :
    CacheSound table (step table reader).2 := by
  unfold step
  split
  · dsimp only
    split
    · intro copies held
      have same : quota table reader = copies := by simpa using held
      exact same.symm.trans (quota_is_entry_count table reader sound)
    · intro copies held
      cases held
  · exact sound

def remaining (table : Table) (reader : Reader) : Nat :=
  countAt table reader.epoch reader.tuple - reader.used

theorem remaining_publish (table : Table) (reader : Reader)
    (past : reader.epoch ≤ table.clock) (changed copies : Nat) :
    remaining (publish table changed copies) reader = remaining table reader := by
  simp only [remaining, countAt_publish_past table changed copies reader.epoch reader.tuple past]

theorem delivering_decrements_remaining (table : Table) (reader : Reader) (sound : CacheSound table reader)
    (within : reader.tuple < reader.ceiling) (available : reader.used < quota table reader) :
    remaining table (step table reader).2 + 1 = remaining table reader := by
  have quotaEq := quota_is_entry_count table reader sound
  simp only [step, if_pos within, if_pos available, remaining]
  omega

def run (table : Table) : Nat → Reader → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, reader =>
      let next := step table reader
      match next.1 with
      | .copy tuple ordinal => (tuple, ordinal) :: run table fuel next.2
      | .skip => run table fuel next.2
      | .exhausted => []

end Mettapedia.Machines.Cursor.ReaderDenseMultiplicity
