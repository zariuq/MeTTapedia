import Mettapedia.Languages.MeTTa.HE.IncrementalTableSemantics

/-!
# Producer/Consumer Choice Points for Backtracking Search

Formalizes the search context from CeTTa's `search_machine.c`: a
`SearchState` combines a `BindingsBuilder` (variable binding accumulator)
with a generic scratch arena (`List α`). A `ChoicePoint` marks both
components for stack-disciplined save/rollback.

## Key results (0 sorry)

- `save_rollback_identity`: save then rollback with no changes = identity
- `rollback_discards_new_bindings`: bindings after mark are discarded
- `rollback_discards_new_scratch`: scratch allocations after mark are discarded
- `rollback_preserves_old`: bindings/scratch before mark survive
- `rollback_idempotent`: double rollback = single rollback
- `nested_save_rollback`: nested save/rollback restores intermediate state
- `producer_rollback_consumer_stable`: consumer view stable across producer rollback
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: Search state -/

/-- A **search state** combines a bindings builder with a generic scratch arena.
    CeTTa's `SearchContext` has a `BindingsBuilder` plus a scratch memory region
    for temporary allocations during pattern matching. -/
structure SearchState (α : Type) where
  bindings : List (String × Atom)
  scratch : List α

namespace SearchState

def empty : SearchState α := ⟨[], []⟩

def addBinding (ss : SearchState α) (v : String) (a : Atom) : SearchState α :=
  { ss with bindings := (v, a) :: ss.bindings }

def allocScratch (ss : SearchState α) (x : α) : SearchState α :=
  { ss with scratch := x :: ss.scratch }

end SearchState

/-! ## §2: Choice points -/

/-- A **choice point** marks the search state at save time.
    CeTTa's `ChoicePoint` captures the bindings length and scratch arena position. -/
structure ChoicePoint where
  bindingsMark : Nat
  scratchMark : Nat

namespace ChoicePoint

/-- Save the current search state as a choice point. -/
def save (ss : SearchState α) : ChoicePoint :=
  ⟨ss.bindings.length, ss.scratch.length⟩

/-- Rollback the search state to a saved choice point.
    Truncates both bindings and scratch back to the marked lengths. -/
def rollback (cp : ChoicePoint) (ss : SearchState α) : SearchState α :=
  { bindings := ss.bindings.drop (ss.bindings.length - cp.bindingsMark),
    scratch := ss.scratch.drop (ss.scratch.length - cp.scratchMark) }

end ChoicePoint

/-! ## §3: Core save/rollback theorems -/

/-- **Theorem 1**: Save then rollback with no intermediate changes = identity. -/
theorem save_rollback_identity (ss : SearchState α) :
    (ChoicePoint.save ss).rollback ss = ss := by
  simp [ChoicePoint.save, ChoicePoint.rollback, Nat.sub_self]

/-- **Theorem 2**: Bindings added after mark are discarded by rollback. -/
theorem rollback_discards_new_bindings (ss : SearchState α) (v : String) (a : Atom) :
    (ChoicePoint.save ss).rollback (ss.addBinding v a) = ss := by
  simp [ChoicePoint.save, ChoicePoint.rollback, SearchState.addBinding]

/-- **Theorem 3**: Scratch allocations after mark are discarded by rollback. -/
theorem rollback_discards_new_scratch (ss : SearchState α) (x : α) :
    (ChoicePoint.save ss).rollback (ss.allocScratch x) = ss := by
  simp [ChoicePoint.save, ChoicePoint.rollback, SearchState.allocScratch]

/-- **Theorem 4**: Bindings and scratch before the mark survive rollback.
    Adding before saving, then adding more and rolling back, preserves the first add. -/
theorem rollback_preserves_old (ss : SearchState α)
    (v₁ : String) (a₁ : Atom) (x₁ : α)
    (v₂ : String) (a₂ : Atom) (x₂ : α) :
    let ss₁ := (ss.addBinding v₁ a₁).allocScratch x₁
    let cp := ChoicePoint.save ss₁
    let ss₂ := (ss₁.addBinding v₂ a₂).allocScratch x₂
    cp.rollback ss₂ = ss₁ := by
  simp [ChoicePoint.save, ChoicePoint.rollback,
        SearchState.addBinding, SearchState.allocScratch]

/-- **Theorem 5**: Double rollback to the same choice point is idempotent. -/
theorem rollback_idempotent (cp : ChoicePoint) (ss : SearchState α) :
    cp.rollback (cp.rollback ss) = cp.rollback ss := by
  simp [ChoicePoint.rollback, List.length_drop]; omega

/-- **Theorem 6**: Nested save/rollback restores intermediate state.
    Save at ss₁, extend to ss₂, save at ss₂, extend to ss₃. Rolling back
    the inner mark gives ss₂; rolling back the outer mark from there gives ss₁. -/
theorem nested_save_rollback (ss₁ : SearchState α)
    (v₁ : String) (a₁ : Atom) (x₁ : α)
    (v₂ : String) (a₂ : Atom) (x₂ : α) :
    let cp₁ := ChoicePoint.save ss₁
    let ss₂ := (ss₁.addBinding v₁ a₁).allocScratch x₁
    let cp₂ := ChoicePoint.save ss₂
    let ss₃ := (ss₂.addBinding v₂ a₂).allocScratch x₂
    cp₁.rollback (cp₂.rollback ss₃) = ss₁ := by
  simp [ChoicePoint.save, ChoicePoint.rollback,
        SearchState.addBinding, SearchState.allocScratch]

/-! ## §4: Producer/consumer model -/

/-- A consumer's view: a sub-list of the bindings up to some depth.
    A **producer** explores branches by saving choice points, extending state,
    and rolling back. A **consumer** reads the current bindings prefix without
    modifying the choice point stack. -/
def consumerView (ss : SearchState α) (depth : Nat) : List (String × Atom) :=
  ss.bindings.drop (ss.bindings.length - depth)

/-- **Theorem 7 (Producer rollback, consumer stable)**: If a consumer's view is
    determined by bindings that existed before the producer's choice point, then
    the consumer's view is unchanged after the producer rolls back.

    Formally: if the consumer's depth ≤ the bindings mark in the choice point,
    then rolling back preserves the consumer's view. -/
theorem producer_rollback_consumer_stable (cp : ChoicePoint) (ss : SearchState α)
    (depth : Nat) (hle : depth ≤ cp.bindingsMark)
    (hmark : cp.bindingsMark ≤ ss.bindings.length) :
    consumerView (cp.rollback ss) depth = consumerView ss depth := by
  simp [consumerView, ChoicePoint.rollback, List.length_drop]; omega

/-! ## §5: Multi-step extension and rollback -/

/-- Add n bindings to a search state (models a producer exploring n variables). -/
def SearchState.addBindings (ss : SearchState α) (bs : List (String × Atom)) :
    SearchState α :=
  { ss with bindings := bs.reverse ++ ss.bindings }

/-- Add n scratch allocations. -/
def SearchState.allocScratchList (ss : SearchState α) (xs : List α) :
    SearchState α :=
  { ss with scratch := xs.reverse ++ ss.scratch }

/-- Rollback after multi-step extension discards all new entries. -/
theorem rollback_multi_bindings (ss : SearchState α) (bs : List (String × Atom)) :
    (ChoicePoint.save ss).rollback (ss.addBindings bs) = ss := by
  simp [ChoicePoint.save, ChoicePoint.rollback, SearchState.addBindings,
        List.length_append, List.length_reverse]

/-- Rollback after multi-step scratch allocation discards all new entries. -/
theorem rollback_multi_scratch (ss : SearchState α) (xs : List α) :
    (ChoicePoint.save ss).rollback (ss.allocScratchList xs) = ss := by
  simp [ChoicePoint.save, ChoicePoint.rollback, SearchState.allocScratchList,
        List.length_append, List.length_reverse]

/-! ## §6: Choice point ordering -/

/-- A choice point `cp₁` is "older than" `cp₂` if both marks are ≤. -/
def ChoicePoint.olderThan (cp₁ cp₂ : ChoicePoint) : Prop :=
  cp₁.bindingsMark ≤ cp₂.bindingsMark ∧ cp₁.scratchMark ≤ cp₂.scratchMark

/-- Rolling back to an older mark after rolling back to a newer mark
    is the same as rolling back directly to the older mark —
    provided the newer mark is reachable from the current state. -/
theorem rollback_older_subsumes (cp₁ cp₂ : ChoicePoint) (ss : SearchState α)
    (holder : cp₁.olderThan cp₂)
    (hreach₂ : cp₂.bindingsMark ≤ ss.bindings.length ∧
               cp₂.scratchMark ≤ ss.scratch.length) :
    cp₁.rollback (cp₂.rollback ss) = cp₁.rollback ss := by
  simp [ChoicePoint.rollback, ChoicePoint.olderThan, List.length_drop] at *
  omega

end Mettapedia.Languages.MeTTa.HE
