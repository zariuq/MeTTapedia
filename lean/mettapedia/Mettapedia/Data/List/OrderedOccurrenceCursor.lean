import Mathlib.Data.List.Basic

/-!
# Ordered occurrence cursors

An ordered space is observed as occurrences rather than as a set of values.
Occurrence identity keeps equal payloads distinct.  A broad-query cursor owns
the matching occurrence sequence visible when it is captured.  Later space
mutation therefore cannot append a new alternative, remove a pending one, or
reorder duplicates in that cursor.

The contract is deliberately independent of a storage representation.  A
runtime may realize the captured sequence with a flat snapshot, persistent
chunks, or a revision-pinned occurrence log, provided `drain_exact` holds.
-/

namespace Mettapedia.Data.List.OrderedOccurrenceCursor

structure Occurrence (α : Type*) where
  identity : Nat
  value : α
deriving DecidableEq, Repr

abbrev OrderedSpace (α : Type*) := List (Occurrence α)

/-- The captured sequence is retained for auditing; `remaining` is its
unconsumed suffix. -/
structure Cursor (α : Type*) where
  captured : List (Occurrence α)
  remaining : List (Occurrence α)
deriving Repr

namespace Cursor

def capture (accept : Occurrence α → Bool)
    (space : OrderedSpace α) : Cursor α :=
  let visible := space.filter accept
  { captured := visible, remaining := visible }

def step : Cursor α → Option (Occurrence α × Cursor α)
  | ⟨_, []⟩ => none
  | ⟨captured, occurrence :: rest⟩ =>
      some (occurrence, ⟨captured, rest⟩)

def drain (cursor : Cursor α) : List (Occurrence α) :=
  cursor.remaining

@[simp] theorem drain_eq_remaining (cursor : Cursor α) :
    cursor.drain = cursor.remaining := rfl

@[simp] theorem drain_capture_exact
    (accept : Occurrence α → Bool) (space : OrderedSpace α) :
    (capture accept space).drain = space.filter accept := by
  simp [capture]

@[simp] theorem captured_capture_exact
    (accept : Occurrence α → Bool) (space : OrderedSpace α) :
    (capture accept space).captured = space.filter accept := rfl

theorem step_preserves_capture
    {cursor next : Cursor α} {occurrence : Occurrence α}
    (stepped : cursor.step = some (occurrence, next)) :
    next.captured = cursor.captured := by
  cases cursor with
  | mk captured remaining =>
      cases remaining with
      | nil => simp [step] at stepped
      | cons head tail =>
          simp only [step, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨rfl, rfl⟩
          rfl

theorem step_decomposes_observation
    {cursor next : Cursor α} {occurrence : Occurrence α}
    (stepped : cursor.step = some (occurrence, next)) :
    cursor.drain = occurrence :: next.drain := by
  cases cursor with
  | mk captured remaining =>
      cases remaining with
      | nil => simp [step] at stepped
      | cons head tail =>
          simp only [step, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨rfl, rfl⟩
          rfl

end Cursor

/-- A cursor remains tied to its capture-time sequence across an arbitrary
later space state. -/
def StableAcross (cursor : Cursor α)
    (accept : Occurrence α → Bool) (before _after : OrderedSpace α) : Prop :=
  cursor.drain = before.filter accept

/-- A realization of an ordered broad-query cursor.  Exact list equality is
stronger than set or bag equality: it retains order, multiplicity, and the
identity of every occurrence.  Stability quantifies over an arbitrary later
space state, expressing logical-update isolation rather than a particular
mutation algorithm. -/
structure Contract
    (captureImpl : (Occurrence α → Bool) → OrderedSpace α → Cursor α) : Prop where
  drain_exact : ∀ accept space,
    (captureImpl accept space).drain = space.filter accept
  stable_after_change : ∀ accept before after,
    StableAcross (captureImpl accept before) accept before after

theorem capture_contract : Contract (@Cursor.capture α) where
  drain_exact := Cursor.drain_capture_exact
  stable_after_change := by
    intro accept before _after
    exact Cursor.drain_capture_exact accept before

def appendOccurrence (space : OrderedSpace α)
    (occurrence : Occurrence α) : OrderedSpace α :=
  space ++ [occurrence]

def removeFirstIdentity (identity : Nat) : OrderedSpace α → OrderedSpace α
  | [] => []
  | occurrence :: rest =>
      if occurrence.identity = identity then rest
      else occurrence :: removeFirstIdentity identity rest

theorem append_after_capture_invisible
    (accept : Occurrence α → Bool) (before : OrderedSpace α)
    (added : Occurrence α) :
    StableAcross (Cursor.capture accept before) accept before
      (appendOccurrence before added) := by
  exact Contract.stable_after_change capture_contract
    accept before (appendOccurrence before added)

theorem removal_after_capture_invisible
    (accept : Occurrence α → Bool) (before : OrderedSpace α)
    (identity : Nat) :
    StableAcross (Cursor.capture accept before) accept before
      (removeFirstIdentity identity before) := by
  exact Contract.stable_after_change capture_contract
    accept before (removeFirstIdentity identity before)

theorem values_preserve_order_and_multiplicity
    (accept : Occurrence α → Bool) (space : OrderedSpace α) :
    ((Cursor.capture accept space).drain.map Occurrence.value) =
      (space.filter accept).map Occurrence.value := by
  rw [Cursor.drain_capture_exact]

namespace Canaries

def firstSeven : Occurrence Nat := ⟨0, 7⟩
def secondSeven : Occurrence Nat := ⟨1, 7⟩
def nine : Occurrence Nat := ⟨2, 9⟩
def acceptAll (_ : Occurrence Nat) : Bool := true

/-- Equal values remain two ordered occurrences. -/
theorem duplicate_values_remain_distinct_occurrences :
    (Cursor.capture acceptAll [firstSeven, secondSeven]).drain =
      [firstSeven, secondSeven] := by
  rfl

/-- A cursor captured before an append cannot see the appended occurrence. -/
theorem captured_cursor_does_not_see_append :
    (Cursor.capture acceptAll [firstSeven]).drain = [firstSeven] ∧
      (Cursor.capture acceptAll
        (appendOccurrence [firstSeven] nine)).drain = [firstSeven, nine] := by
  constructor <;> rfl

/-- Reading the live list again is not a logical-update cursor: an append
changes its observation. -/
theorem live_read_is_not_append_stable :
    (List.filter acceptAll [firstSeven]) ≠
      List.filter acceptAll (appendOccurrence [firstSeven] nine) := by
  decide

/-- A positional live read is also invalidated by removal before its current
position; the retained cursor still owns the pending occurrence. -/
theorem live_position_is_not_removal_stable :
    ([firstSeven, nine].drop 1) ≠
      (removeFirstIdentity firstSeven.identity [firstSeven, nine]).drop 1 := by
  decide

end Canaries

#print axioms Cursor.drain_capture_exact
#print axioms Cursor.step_preserves_capture
#print axioms Cursor.step_decomposes_observation
#print axioms capture_contract
#print axioms append_after_capture_invisible
#print axioms removal_after_capture_invisible
#print axioms values_preserve_order_and_multiplicity
#print axioms Canaries.duplicate_values_remain_distinct_occurrences
#print axioms Canaries.live_read_is_not_append_stable
#print axioms Canaries.live_position_is_not_removal_stable

end Mettapedia.Data.List.OrderedOccurrenceCursor
