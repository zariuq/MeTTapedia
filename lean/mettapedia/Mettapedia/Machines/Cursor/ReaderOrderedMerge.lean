import Mettapedia.Machines.Cursor.StampedSnapshots
import Mettapedia.Machines.Cursor.Sequence
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Entry-view priority order from live and retired occurrences

Actual birth and death stamps partition a reader's entry occurrences into
still-live rows and rows retired after entry. A lazy two-head merge preserves
their priority order and occurrence identities. The mathematical merged list
is a readback, not a collection built when the implementation opens.

Priority keys are immutable for the lifetime of an occurrence; the occurrence
id breaks ties between equal payload keys. Comparator implementation, native
successor/heap maintenance and concurrent publication remain separate duties.
The list implementation below does not acquire a logarithmic heap tariff.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedMerge

open Mettapedia.TypeTheory
open StampedSnapshots

variable {Value Key : Type}

def entryIDs (store : Store Value) (reader : Reader) : Finset Nat :=
  (Finset.range reader.ceiling).filter (fun id => (atTime store reader.time id).isSome)

def survivingIDs (store : Store Value) (reader : Reader) : Finset Nat :=
  (Finset.range reader.ceiling).filter fun id =>
    (store.row id).any (fun row => decide (row.born ≤ reader.time) && row.death.isNone) = true

def retiredIDs (store : Store Value) (reader : Reader) : Finset Nat :=
  (Finset.range reader.ceiling).filter fun id =>
    (store.row id).any (fun row => decide (row.born ≤ reader.time) &&
      (row.death.map (fun death => decide (reader.time < death))).getD false) = true

/-- This partition is earned from the independently defined timestamp
visibility, including rows already dead when the reader opened. -/
theorem stamp_partition (store : Store Value) (reader : Reader) :
    survivingIDs store reader ∪ retiredIDs store reader = entryIDs store reader := by
  ext id
  simp only [Finset.mem_union, entryIDs, survivingIDs, retiredIDs,
    Finset.mem_filter, Finset.mem_range]
  cases found : store.row id with
  | none => simp [atTime, found]
  | some row =>
      cases dead : row.death <;>
        simp [atTime, visible, found, dead]

theorem stamp_partition_disjoint (store : Store Value) (reader : Reader) :
    Disjoint (survivingIDs store reader) (retiredIDs store reader) := by
  apply Finset.disjoint_left.mpr
  intro id live dead
  cases found : store.row id with
  | none => simp [survivingIDs, found] at live
  | some row =>
      cases death : row.death <;>
        simp [survivingIDs, retiredIDs, found, death] at live dead

theorem entry_add (store : Store Value) (reader : Reader) (value : Value)
    (valid : Admissible store reader) :
    entryIDs (add store value) reader = entryIDs store reader := by
  ext id
  by_cases within : id < reader.ceiling
  · have old : id < store.next := within.trans_le valid.2
    simp only [entryIDs, Finset.mem_filter, Finset.mem_range]
    unfold atTime
    rw [add_keeps_old_slot store value id old]
  · simp [entryIDs, within]

theorem entry_remove (store : Store Value) (reader : Reader) (id : Nat)
    (valid : Admissible store reader) :
    entryIDs (remove store id) reader = entryIDs store reader := by
  ext occurrence
  simp only [entryIDs, Finset.mem_filter]
  rw [remove_keeps_past store id reader.time occurrence valid.1]

abbrev Token (Key : Type) := Key ×ₗ Nat

def token (priority : Nat → Key) (id : Nat) : Token Key := toLex (priority id, id)

theorem token_injective (priority : Nat → Key) : Function.Injective (token priority) := by
  intro first second same
  exact congrArg (fun value : Token Key => (ofLex value).2) same

variable [LinearOrder Key]

def tokens (priority : Nat → Key) (ids : Finset Nat) : Finset (Token Key) :=
  ids.image (token priority)

theorem token_partition (priority : Nat → Key) (store : Store Value) (reader : Reader) :
    tokens priority (survivingIDs store reader) ∪ tokens priority (retiredIDs store reader) =
      tokens priority (entryIDs store reader) := by
  rw [tokens, tokens, ← Finset.image_union, stamp_partition]
  rfl

theorem token_partition_disjoint (priority : Nat → Key) (store : Store Value) (reader : Reader) :
    Disjoint (tokens priority (survivingIDs store reader))
      (tokens priority (retiredIDs store reader)) := by
  apply Finset.disjoint_left.mpr
  intro value live dead
  obtain ⟨first, firstLive, firstValue⟩ := Finset.mem_image.mp live
  obtain ⟨second, secondDead, secondValue⟩ := Finset.mem_image.mp dead
  have same := token_injective priority (firstValue.trans secondValue.symm)
  subst second
  exact Finset.disjoint_left.mp (stamp_partition_disjoint store reader) firstLive secondDead

structure State (Key : Type) where
  live : List (Token Key)
  gone : List (Token Key)

def meaning (state : State Key) : List (Token Key) :=
  List.merge state.live state.gone (fun a b => decide (a ≤ b))

/-- Two cached heads, one comparison, then consumption of the selected
occurrence. Selecting an equal payload never identifies distinct ids. -/
def pull (state : State Key) : Option (Token Key) × State Key :=
  match state.live, state.gone with
  | [], [] => (none, state)
  | first :: rest, [] => (some first, ⟨rest, []⟩)
  | [], first :: rest => (some first, ⟨[], rest⟩)
  | first :: rest, second :: tail =>
      if first ≤ second then (some first, ⟨rest, second :: tail⟩)
      else (some second, ⟨first :: rest, tail⟩)

def provider : Provider (Sequence.protocol (Token Key)) where
  State _ _ := State Key
  step state _ := ⟨(pull state).1, (pull state).2⟩

def refinement : Hom (provider (Key := Key)) (Sequence.tails (Token Key)) where
  map := meaning
  step state request := by
    rcases state with ⟨live, gone⟩
    cases live with
    | nil => cases gone <;> simp [provider, pull, meaning, Sequence.tails]
    | cons first rest =>
        cases gone with
        | nil => simp [provider, pull, meaning, Sequence.tails]
        | cons second tail =>
            by_cases before : first ≤ second <;>
              simp [provider, pull, meaning, Sequence.tails, before]

/-- The native interfaces must supply sorted, unique and disjoint occurrence
streams. Their contents are independently justified by the stamped store. -/
def Components (state : State Key) (live gone : Finset (Token Key)) : Prop :=
  state.live.Pairwise (· ≤ ·) ∧ state.gone.Pairwise (· ≤ ·) ∧
    state.live.Nodup ∧ state.gone.Nodup ∧
    state.live.toFinset = live ∧ state.gone.toFinset = gone ∧ Disjoint live gone

theorem merge_source (state : State Key) (live gone : Finset (Token Key))
    (valid : Components state live gone) :
    meaning state = (live ∪ gone).sort (· ≤ ·) := by
  rcases valid with ⟨liveOrdered, goneOrdered, liveUnique, goneUnique, liveSet, goneSet, separate⟩
  have ordered : (meaning state).Pairwise (· ≤ ·) := liveOrdered.merge goneOrdered
  have listsSeparate : List.Disjoint state.live state.gone := by
    intro value inLive inGone
    exact Finset.disjoint_left.mp separate
      (liveSet ▸ List.mem_toFinset.mpr inLive) (goneSet ▸ List.mem_toFinset.mpr inGone)
  have unique : (meaning state).Nodup :=
    (List.merge_perm_append (fun a b : Token Key => decide (a ≤ b))).nodup_iff.mpr
      (List.nodup_append.mpr ⟨liveUnique, goneUnique, by
        intro first firstLive second secondGone same
        subst second
        exact listsSeparate firstLive secondGone⟩)
  have all : (meaning state).toFinset = live ∪ gone := by
    ext value
    simp only [meaning, List.mem_toFinset, List.mem_merge, Finset.mem_union]
    rw [← List.mem_toFinset, liveSet, ← List.mem_toFinset, goneSet]
  have canonical := (List.toFinset_sort (r := (· ≤ ·)) unique).mpr ordered
  rw [all] at canonical
  exact canonical.symm

/-- Native live-successor and removed-heap contents earn the complete ordered
entry view through the actual birth/death partition. No final result equality
is supplied as a premise. -/
theorem stamped_entry_source (priority : Nat → Key) (store : Store Value) (reader : Reader)
    (state : State Key)
    (valid : Components state (tokens priority (survivingIDs store reader))
      (tokens priority (retiredIDs store reader))) :
    meaning state = (tokens priority (entryIDs store reader)).sort (· ≤ ·) := by
  rw [merge_source state _ _ valid, token_partition]

theorem entry_client_observation {Return : Unit → Unit → Type}
    (priority : Nat → Key) (store : Store Value) (reader : Reader) (state : State Key)
    (valid : Components state (tokens priority (survivingIDs store reader))
      (tokens priority (retiredIDs store reader)))
    (client : Client (P := Sequence.protocol (Token Key)) (Return := Return))
    (sourceCost : Charge (provider (Key := Key)))
    (targetCost : Charge (Sequence.tails (Token Key)))
    (fuel : Nat) (control : client.V () ()) :
    refinement.outcome client
        (advance provider client sourceCost fuel ⟨(), control, state⟩).2 =
      (advance (Sequence.tails (Token Key)) client targetCost fuel
        ⟨(), control, (tokens priority (entryIDs store reader)).sort (· ≤ ·)⟩).2 := by
  have comparison := Hom.advance client refinement sourceCost targetCost fuel
    ⟨(), control, state⟩
  simpa only [Hom.packet, refinement, stamped_entry_source priority store reader state valid] using
    comparison

def canonicalComponents (priority : Nat → Key) (store : Store Value) (reader : Reader) : State Key :=
  ⟨(tokens priority (survivingIDs store reader)).sort (· ≤ ·),
    (tokens priority (retiredIDs store reader)).sort (· ≤ ·)⟩

theorem canonical_components (priority : Nat → Key) (store : Store Value) (reader : Reader) :
    Components (canonicalComponents priority store reader)
      (tokens priority (survivingIDs store reader)) (tokens priority (retiredIDs store reader)) := by
  dsimp only [Components, canonicalComponents]
  exact ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _,
    Finset.sort_nodup _ _, Finset.sort_nodup _ _, Finset.sort_toFinset _ _,
    Finset.sort_toFinset _ _, token_partition_disjoint priority store reader⟩

end Mettapedia.Machines.Cursor.ReaderOrderedMerge
