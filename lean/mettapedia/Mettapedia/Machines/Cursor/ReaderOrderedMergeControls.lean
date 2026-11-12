import Mettapedia.Machines.Cursor.ReaderOrderedMergeUpdates
import Mettapedia.Machines.Cursor.ReaderOrderedMergeCursor

/-!
# Controls for stamped ordered readers and retirement transfer

The source stores are modified by the actual stamped add/remove operations.
Negative mechanisms lose a retired occurrence, duplicate it across streams,
forget priority ordering, adopt a later entry view, or replay a rejected prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedMergeControls

open ReaderOrderedMerge
open StampedSnapshots

def tok (priority id : Nat) : Token Nat := toLex (priority, id)

def drain : Nat → State Nat → List (Token Nat)
  | 0, _ => []
  | amount + 1, state =>
      match pull state with
      | (none, _) => []
      | (some value, next) => value :: drain amount next

def shown (values : List (Token Nat)) : List (Nat × Nat) := values.map ofLex

def original : Store Nat := add (add empty 20) 10
def reader : Reader := start original
def modified : Store Nat := add (remove original 1) 5

def priority (id : Nat) : Nat := if id = 0 then 20 else if id = 1 then 10 else 5

example : survivingIDs modified reader = {0} ∧ retiredIDs modified reader = {1} := by decide

example : entryIDs modified reader = {0, 1} := by decide

example : shown (drain 3 (canonicalComponents priority modified reader)) =
    [(10, 1), (20, 0)] := by
  have live : tokens priority (survivingIDs modified reader) = {tok 20 0} := by decide
  have gone : tokens priority (retiredIDs modified reader) = {tok 10 1} := by decide
  simp only [canonicalComponents, live, gone, Finset.sort_singleton]
  decide

/-- A newly opened reader has another entry view, including the fresh smaller
priority row and excluding the old removed row. An existing reader cannot adopt it. -/
example : shown (drain 3 (canonicalComponents priority modified (start modified))) =
    [(5, 2), (20, 0)] := by
  have live : tokens priority (survivingIDs modified (start modified)) =
      {tok 5 2, tok 20 0} := by decide
  have gone : tokens priority (retiredIDs modified (start modified)) = ∅ := by decide
  simp only [canonicalComponents, live, gone, Finset.sort_empty]
  have sorted : ({tok 5 2, tok 20 0} : Finset (Token Nat)).sort (· ≤ ·) =
      [tok 5 2, tok 20 0] := by
    apply (List.toFinset_sort (r := (· ≤ ·))
      (by decide : [tok 5 2, tok 20 0].Nodup)).mpr
    decide
  rw [sorted]
  decide

def tied : Store Nat := add (add empty 7) 7

example : shown (drain 3 (canonicalComponents (fun _ => 7) tied (start tied))) =
    [(7, 0), (7, 1)] := by
  have live : tokens (fun _ => 7) (survivingIDs tied (start tied)) =
      {tok 7 0, tok 7 1} := by decide
  have gone : tokens (fun _ => 7) (retiredIDs tied (start tied)) = ∅ := by decide
  simp only [canonicalComponents, live, gone, Finset.sort_empty]
  have sorted : ({tok 7 0, tok 7 1} : Finset (Token Nat)).sort (· ≤ ·) =
      [tok 7 0, tok 7 1] := by
    apply (List.toFinset_sort (r := (· ≤ ·))
      (by decide : [tok 7 0, tok 7 1].Nodup)).mpr
    decide
  rw [sorted]
  decide

def before : State Nat := ⟨[tok 10 1, tok 20 0], []⟩
def moved : State Nat := ReaderOrderedMergeUpdates.retire before (tok 10 1)

example : shown (drain 3 moved) = [(10, 1), (20, 0)] := by decide

example : shown (drain 3 (ReaderOrderedMergeUpdates.retire moved (tok 10 1))) =
    [(10, 1), (20, 0)] := by decide

/-- Retiring an already delivered occurrence must not put it back in the heap. -/
example : (ReaderOrderedMergeUpdates.retire (pull before).2 (tok 10 1)).live =
    (pull before).2.live := by decide

example : shown (drain 3 (⟨[tok 20 0], []⟩ : State Nat)) ≠ [(10, 1), (20, 0)] := by decide

example : shown (drain 3 (⟨[tok 10 1, tok 20 0], [tok 10 1]⟩ : State Nat)) =
    [(10, 1), (10, 1), (20, 0)] := by decide

example : shown (drain 3 (⟨[], [tok 20 0, tok 10 1]⟩ : State Nat)) =
    [(20, 0), (10, 1)] := by decide

def eligible (value : Token Nat) : Bool := decide ((ofLex value).2 < reader.ceiling)
def raw : State Nat := ⟨[tok 5 2, tok 20 0], [tok 10 1]⟩

def rawFirst : Sigma fun _ : Option (Token Nat) => State Nat :=
  (ReaderOrderedMergeCursor.provider eligible).step (base := ()) (index := ()) raw ()

example : rawFirst.1 = some (tok 10 1) ∧
    (ReaderOrderedMergeCursor.seek eligible raw.live).1 = 1 := by decide

example : (ReaderOrderedMergeCursor.seek eligible rawFirst.2.live).1 = 0 := by decide

/-- Restarting from the original live iterator charges the old rejected row
again, despite the same outward answer being available. -/
example : (ReaderOrderedMergeCursor.seek eligible raw.live).1 >
    (ReaderOrderedMergeCursor.seek eligible rawFirst.2.live).1 := by decide

example : ReaderOrderedMergeUpdates.insertionComparisons (tok 99 9)
    [tok 1 0, tok 2 1, tok 3 2, tok 4 3] = 4 := by decide

end Mettapedia.Machines.Cursor.ReaderOrderedMergeControls
