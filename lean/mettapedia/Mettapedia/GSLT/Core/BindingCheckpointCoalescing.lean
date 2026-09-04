import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra

/-!
# Observer-delimited binding checkpoint coalescing

A linear rollback store need not retain one checkpoint per physical write.
When a finite region has no intermediate rollback observer, the checkpoint at
the region entrance already restores the exact authoritative substitution
after every write in that region.  This module states that optimization and
its boundary independently of a particular trail representation.

The negative theorem is equally important: if a meaning-changing write is
separated by an observed `save`, the marks before and after that write must be
distinct.  Coalescing across such an observation would therefore erase a
genuine rollback capability.  Replay remains a different advertised
capability and is not silently substituted for direct rollback here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.BindingCheckpointCoalescing

open BindingStoreCapabilityAlgebra

universe uLogical uPhysical uMark uUpdate

variable {Logical : Type uLogical} {Physical : Type uPhysical}
  {Mark : Type uMark} {Update : Type uUpdate}

/-- One entrance checkpoint is sufficient for exact rollback after an
arbitrary finite observer-free update region. -/
theorem entrance_checkpoint_suffices
    (store : LinearRollbackStore Logical Physical Mark Update)
    (physical : Physical) (updates : List Update) :
    store.denote
        (store.rollback
          (store.toBindingStore.writeMany physical updates)
          (store.save physical)) =
      store.denote physical :=
  store.rollback_after_writeMany_exact physical updates

/-- A direct checkpoint observed after a meaning-changing write cannot be the
same mark as the checkpoint observed before it.  This is the exact boundary
that prevents checkpoint coalescing across intermediate `save` operations. -/
theorem saves_distinct_of_meaning_change
    (store : LinearRollbackStore Logical Physical Mark Update)
    (physical : Physical) (update : Update)
    (changes :
      store.logicalWrite (store.denote physical) update ≠
        store.denote physical) :
    store.save (store.write physical update) ≠ store.save physical := by
  intro sameMark
  have oldValid : store.valid physical (store.save physical) :=
    store.save_valid physical
  have oldMeaningStable :
      store.savedMeaning
          (store.write physical update) (store.save physical) =
        store.savedMeaning physical (store.save physical) :=
    store.savedMeaning_write physical (store.save physical) update oldValid
  have newSaveExact :
      store.savedMeaning
          (store.write physical update)
          (store.save (store.write physical update)) =
        store.denote (store.write physical update) :=
    store.save_exact (store.write physical update)
  have oldSaveExact :
      store.savedMeaning physical (store.save physical) =
        store.denote physical :=
    store.save_exact physical
  apply changes
  rw [← store.write_exact physical update]
  rw [← newSaveExact, sameMark, oldMeaningStable, oldSaveExact]

/-! ## Exact checkpoint-count model

This model counts only rollback metadata for one observer-free region.  It
does not claim that writes, values, or the final substitution are free. -/

/-- The eager policy records one checkpoint before every write. -/
def eagerCheckpointCount (updates : List Update) : Nat := updates.length

/-- The coalesced policy records one entrance checkpoint exactly when a
nonempty region performs work. -/
def coalescedCheckpointCount (updates : List Update) : Nat :=
  if updates.isEmpty then 0 else 1

theorem coalescedCheckpointCount_le_eager (updates : List Update) :
    coalescedCheckpointCount updates ≤ eagerCheckpointCount updates := by
  cases updates with
  | nil => simp [coalescedCheckpointCount, eagerCheckpointCount]
  | cons update updates =>
      simp [coalescedCheckpointCount, eagerCheckpointCount]

/-- A region with at least two writes strictly reduces checkpoint metadata. -/
theorem coalescedCheckpointCount_lt_eager
    (updates : List Update) (atLeastTwo : 2 ≤ updates.length) :
    coalescedCheckpointCount updates < eagerCheckpointCount updates := by
  cases updates with
  | nil => simp at atLeastTwo
  | cons first rest =>
      simp only [List.length_cons] at atLeastTwo
      simp only [coalescedCheckpointCount, eagerCheckpointCount,
        List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      omega

/-! ## Independent controls -/

namespace Canaries

open BindingStoreCapabilityAlgebra.History

def base : History Nat := ⟨[10]⟩

/-- Three observer-free writes require one rollback checkpoint and restore the
exact entrance meaning. -/
example :
    History.store.denote
        (History.store.rollback
          (History.store.toBindingStore.writeMany base [20, 30, 40])
          (History.store.save base)) = [10] := by
  exact entrance_checkpoint_suffices History.store base [20, 30, 40]

example : coalescedCheckpointCount [20, 30, 40] = 1 := by decide

example : eagerCheckpointCount [20, 30, 40] = 3 := by decide

/-- Observing a checkpoint after a real update creates a distinct direct
rollback capability; the two writes cannot share one observed mark. -/
example :
    History.store.save
        (History.store.write base 20) ≠ History.store.save base := by
  apply saves_distinct_of_meaning_change History.store base 20
  simp [History.store]

/-- A no-op logical write does not justify the distinct-mark conclusion. -/
example :
    ¬ ((fun history : List Nat => history) [10] ≠ [10]) := by simp

end Canaries

#print axioms entrance_checkpoint_suffices
#print axioms saves_distinct_of_meaning_change
#print axioms coalescedCheckpointCount_le_eager
#print axioms coalescedCheckpointCount_lt_eager

end Mettapedia.GSLT.Core.BindingCheckpointCoalescing
