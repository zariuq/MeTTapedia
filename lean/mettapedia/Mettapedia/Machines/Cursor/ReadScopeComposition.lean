import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# Composing per-call read views is not one whole-query snapshot

The reference algorithm captures the outer rows when it starts and captures
each inner row list when that prefix reaches its inner read. It emits rows
incrementally and resumes from the world supplied by its caller. The target
instead composes two single-read searches using ordinary shared-world bind.
The theorem identifies their complete traces, not just a completed answer bag.

A separate whole-entry query captures all joined rows before yielding any.
Its unchanged-world drain agrees with both nested forms, but caller writes
distinguish it. Thus a read-step substrate can express both contracts without
requiring a legacy conjunction to become a single global snapshot.

This is a finite relational fragment with explicit Boolean matching. It is
not a source binder/unification theorem or a native cost correspondence. The
lists specify read views; they do not require eager native list construction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReadScopeComposition

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)

variable {A B : Type}

structure World (A B : Type) where
  left : List A
  right : List B
  deriving DecidableEq, Repr

def selected (relation : A → B → Bool) (first : A) (rows : List B) : List (A × B) :=
  (rows.filter (relation first)).map (first, ·)

def joined (relation : A → B → Bool) (left : List A) (right : List B) : List (A × B) :=
  left.flatMap fun first => selected relation first right

def innerLoop (relation : A → B → Bool) (first : A) :
    List B → Search (World A B) (A × B)
  | [], world => .done world
  | second :: later, world =>
      if relation first second then
        .answer (first, second) world (innerLoop relation first later)
      else innerLoop relation first later world

def nestedLoop (relation : A → B → Bool) : List A → Search (World A B) (A × B)
  | [], world => .done world
  | first :: later, world =>
      (innerLoop relation first world.right world).append (nestedLoop relation later)

def readLeft : Search (World A B) A := fun world => Search.superpose world.left world

def readRight (relation : A → B → Bool) (first : A) : Search (World A B) (A × B) :=
  fun world => Search.superpose (selected relation first world.right) world

def composed (relation : A → B → Bool) : Search (World A B) (A × B) :=
  readLeft.bind (readRight relation)

def wholeEntry (relation : A → B → Bool) : Search (World A B) (A × B) :=
  fun world => Search.superpose (joined relation world.left world.right) world

theorem innerLoop_selected (relation : A → B → Bool) (first : A) (rows : List B) :
    innerLoop relation first rows = Search.superpose (selected relation first rows) := by
  induction rows with
  | nil => rfl
  | cons second later ih =>
      funext world
      cases matched : relation first second <;>
        simp [innerLoop, selected, matched, Search.superpose, ih]

/-- The reference loop and the composed read operations agree even when
their consumer changes the world between any two answers. Each inner view
is captured at its own call, not when the outer loop first began. -/
theorem nestedLoop_composed (relation : A → B → Bool) (rows : List A) :
    nestedLoop relation rows = (Search.superpose rows).bind (readRight relation) := by
  induction rows with
  | nil => rfl
  | cons first later ih =>
      funext world
      change (innerLoop relation first world.right world).append (nestedLoop relation later) =
        (readRight relation first world).append ((Search.superpose later).bind (readRight relation))
      rw [innerLoop_selected, ih]
      rfl

theorem per_call_views_refine_nested (relation : A → B → Bool) (world : World A B) :
    composed relation world = nestedLoop relation world.left world := by
  simp only [composed, readLeft, Search.bind]
  exact (congrFun (nestedLoop_composed relation world.left) world).symm

theorem nestedLoop_drain (relation : A → B → Bool) (rows : List A) (world : World A B) :
    (nestedLoop relation rows world).drain = (joined relation rows world.right, world) := by
  induction rows generalizing world with
  | nil => rfl
  | cons first later ih =>
      simp only [nestedLoop, innerLoop_selected, Trace.drain_append, Search.drain_superpose, ih,
        joined, List.flatMap_cons]

/-- A stable drain cannot distinguish the two scope policies. It is
therefore insufficient evidence for adaptive contextual equivalence. -/
theorem stable_drain_agrees (relation : A → B → Bool) (world : World A B) :
    (composed relation world).drain = (wholeEntry relation world).drain := by
  rw [per_call_views_refine_nested, nestedLoop_drain]
  exact (Search.drain_superpose _ _).symm

namespace Controls

def sameKey (first second : Nat) : Bool := first == second
def adding : World Nat Nat := ⟨[0, 1], [0]⟩
def removing : World Nat Nat := ⟨[0, 1], [0, 1]⟩

def addRight (pair : Nat × Nat) : Search (World Nat Nat) Nat := fun world =>
  .answer pair.1 { world with right := world.right ++ [1] } .done

def removeRight (pair : Nat × Nat) : Search (World Nat Nat) Nat := fun world =>
  .answer pair.1 { world with right := world.right.filter (· != 1) } .done

theorem later_call_sees_insertion :
    (((composed sameKey).bind addRight) adding).drain = ([0, 1], ⟨[0, 1], [0, 1, 1]⟩) := by
  decide

theorem whole_entry_does_not_see_insertion :
    (((wholeEntry sameKey).bind addRight) adding).drain = ([0], ⟨[0, 1], [0, 1]⟩) := by
  decide

theorem later_call_sees_removal :
    (((composed sameKey).bind removeRight) removing).drain = ([0], ⟨[0, 1], [0]⟩) := by
  decide

theorem whole_entry_keeps_removed_match :
    (((wholeEntry sameKey).bind removeRight) removing).drain = ([0, 1], ⟨[0, 1], [0]⟩) := by
  decide

def singleRead : Search (World Nat Nat) (Nat × Nat) :=
  readRight (fun _ _ => true) 0

/-- The single reader has already entered its right view; removing a later
row does not change what that same open reader still owes its caller. -/
theorem single_call_still_keeps_its_own_snapshot :
    ((singleRead.bind (fun pair world => .answer pair.2
      { world with right := world.right.filter (· != 1) } .done)) removing).drain =
        ([0, 1], ⟨[0, 1], [0]⟩) := by decide

theorem removing_global_scope_changes_context :
    ((composed sameKey).bind removeRight removing).drain.1 ≠
      ((wholeEntry sameKey).bind removeRight removing).drain.1 := by decide

end Controls

end Mettapedia.Machines.Cursor.ReadScopeComposition
