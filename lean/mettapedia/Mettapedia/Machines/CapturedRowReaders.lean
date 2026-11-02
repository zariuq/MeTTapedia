import Mettapedia.Machines.RevisionedOccurrenceStore
import Mathlib.Tactic

/-!
# Captured row readers across representation mutations

A live-validated reader and an owned captured reader have different contracts.
Before publishing a revision-changing edit, capture the reader's complete row
view. Reads then use that view rather than the new store's revision. The
current position and occurrence coordinates are preserved. The model includes
an edit whose row payloads do not change but whose revision does: treating
that as a live-reader change causes a false invalidation.

Epoch adoption is also sound when the entire captured prefix is unchanged.
That is a value-level condition; index coordinates and pointer lifetimes must
be certified by a native implementation before it uses that alternative.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CapturedRowReaders

variable {Entry : Type}

structure Store (Entry : Type) where
  revision : Nat
  rows : List Entry
  deriving DecidableEq

structure Cursor (Entry : Type) where
  revision : Nat
  ceiling : Nat
  position : Nat
  owned : Option (List Entry)
  deriving DecidableEq

def start (store : Store Entry) : Cursor Entry :=
  ⟨store.revision, store.rows.length, 0, none⟩

def rows (store : Store Entry) (cursor : Cursor Entry) : Option (List Entry) :=
  match cursor.owned with
  | some saved => some saved
  | none => if cursor.revision = store.revision then some (store.rows.take cursor.ceiling) else none

def remaining (store : Store Entry) (cursor : Cursor Entry) : Option (List Entry) :=
  (rows store cursor).map (List.drop cursor.position)

def detach (store : Store Entry) (cursor : Cursor Entry) : Option (Cursor Entry) :=
  (rows store cursor).map fun saved => { cursor with owned := some saved }

def next (store : Store Entry) (cursor : Cursor Entry) : Option (Option Entry × Cursor Entry) :=
  (rows store cursor).map fun saved =>
    match saved[cursor.position]? with
    | none => (none, cursor)
    | some item => (some item, { cursor with position := cursor.position + 1 })

def edit (store : Store Entry) (newRows : List Entry) : Store Entry :=
  ⟨store.revision + 1, newRows⟩

theorem start_rows (store : Store Entry) : rows store (start store) = some store.rows := by
  simp [rows, start]

theorem detach_rows (before after : Store Entry) (cursor : Cursor Entry) (saved : List Entry)
    (current : rows before cursor = some saved) :
    detach before cursor = some { cursor with owned := some saved } ∧
    rows after { cursor with owned := some saved } = some saved := by
  constructor
  · simp only [detach, current, Option.map_some]
  · rfl

/-- Any later store mutation is invisible to the already captured suffix. -/
theorem detached_remaining (before after : Store Entry) (cursor : Cursor Entry) (saved : List Entry)
    (current : rows before cursor = some saved) :
    remaining after { cursor with owned := some saved } = remaining before cursor := by
  simp only [remaining, current]
  rfl

theorem detached_next (before after : Store Entry) (cursor : Cursor Entry) (saved : List Entry)
    (current : rows before cursor = some saved) :
    (next after { cursor with owned := some saved }).map (fun p => (p.1, p.2.position)) =
      (next before cursor).map (fun p => (p.1, p.2.position)) := by
  simp only [next, current]
  simp only [rows, Option.map_some]
  split <;> rfl

/-- An attached reader may follow a new revision only after certifying its
entire captured prefix. Bag equality alone is insufficient. -/
theorem adopt_revision (before after : Store Entry) (cursor : Cursor Entry)
    (attached : cursor.owned = none) (current : cursor.revision = before.revision)
    (unchanged : after.rows.take cursor.ceiling = before.rows.take cursor.ceiling) :
    remaining after { cursor with revision := after.revision } = remaining before cursor := by
  simp [remaining, rows, attached, current, unchanged]

def publish (store : Store Entry) (cursor : Cursor Entry) (newRows : List Entry) :
    Option (Store Entry × Cursor Entry) :=
  (detach store cursor).map fun retained => (edit store newRows, retained)

theorem publish_preserves (before : Store Entry) (cursor : Cursor Entry) (newRows : List Entry)
    (after : Store Entry) (retained : Cursor Entry)
    (accepted : publish before cursor newRows = some (after, retained)) :
    remaining after retained = remaining before cursor := by
  obtain ⟨owned, held, equal⟩ := Option.map_eq_some_iff.mp accepted
  obtain ⟨saved, current, same⟩ := Option.map_eq_some_iff.mp held
  subst owned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact detached_remaining before _ cursor saved current

namespace Controls

def original : Store Nat := ⟨4, [7, 7, 9]⟩

theorem revision_only_mutation_can_invalidate :
    remaining original (start original) = some [7, 7, 9] ∧
    remaining (edit original original.rows) (start original) = none := by decide

theorem capture_before_removal_preserves_occurrences :
    remaining (edit original [9]) { start original with owned := some original.rows } =
      some [7, 7, 9] := by decide

/-- Keeping only the bag would not retain positional occurrences. -/
theorem equal_bags_do_not_justify_epoch_adoption :
    ([7, 9] : List Nat).Perm [9, 7] ∧
    next (⟨2, [7, 9]⟩ : Store Nat) ⟨2, 2, 0, none⟩ ≠
      next (⟨2, [9, 7]⟩ : Store Nat) ⟨2, 2, 0, none⟩ := by
  exact ⟨List.Perm.swap _ _ [], by decide⟩

end Controls

#print axioms detached_next
#print axioms adopt_revision
#print axioms publish_preserves

end Mettapedia.Machines.CapturedRowReaders
