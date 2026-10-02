import Mettapedia.GSLT.LanguageDef.NativeOpsExternal

/-!
Defined storage effects of the system allocator's free operation. Null is a
no-op. A nonnull pointer must denote the base of a live owned allocation;
interior and missing allocations have no defined transition. These conditions
describe the C definedness domain, not additional runtime checks. System free
does not change the compact operational allocator's statistics or callbacks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFreeStorage

open NativeOps (Address SourceMemory TargetMemory MemoryRelated)

def sourceFree (memory : SourceMemory) (pointer : Option Address) : Option SourceMemory :=
  match pointer with
  | none => some memory
  | some address =>
    if address.element = 0 ∧ address.fields = [] then do
      let _ ← memory.owned address.storage
      some (NativeOps.sourceRelease memory address.storage)
    else none

def targetFree (memory : TargetMemory) (pointer : Option Address) : Option TargetMemory :=
  match pointer with
  | none => some memory
  | some address =>
    if address.element = 0 then
      if address.fields = [] then
        match memory.owned address.storage with
        | none => none
        | some _ => some (NativeOps.targetRelease memory address.storage)
      else none
    else none

theorem free_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (pointer : Option Address) (post : SourceMemory)
    (freed : sourceFree source pointer = some post) :
    ∃ native, targetFree target pointer = some native ∧ MemoryRelated post native := by
  cases pointer with
  | none =>
    have same : source = post := Option.some.inj freed
    exact ⟨target, rfl, same ▸ related⟩
  | some address =>
    by_cases element : address.element = 0
    · by_cases fields : address.fields = []
      · cases owned : source.owned address.storage with
        | none => simp only [sourceFree, element, fields, and_self, if_true, owned,
            bind, Option.bind_none] at freed; cases freed
        | some extent =>
          have same : NativeOps.sourceRelease source address.storage = post := by
            apply Option.some.inj
            simpa only [sourceFree, element, fields, and_self, if_true, owned,
              bind, Option.bind_some] using freed
          refine ⟨NativeOps.targetRelease target address.storage, ?_, ?_⟩
          · simp only [targetFree, element, fields, if_true, related.2, owned, Option.map_some]
          · rw [← same]
            exact NativeOps.release_correspondence source target related address.storage
      · simp only [sourceFree, fields, and_false, if_false] at freed; cases freed
    · simp only [sourceFree, element, false_and, if_false] at freed; cases freed

theorem free_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (pointer : Option Address) (native : TargetMemory)
    (freed : targetFree target pointer = some native) :
    ∃ post, sourceFree source pointer = some post ∧ MemoryRelated post native := by
  cases pointer with
  | none =>
    have same : target = native := Option.some.inj freed
    exact ⟨source, rfl, same ▸ related⟩
  | some address =>
    by_cases element : address.element = 0
    · by_cases fields : address.fields = []
      · cases owned : source.owned address.storage with
        | none => simp only [targetFree, element, fields, if_true, related.2, owned,
            Option.map_none] at freed; cases freed
        | some extent =>
          have same : NativeOps.targetRelease target address.storage = native := by
            apply Option.some.inj
            simpa only [targetFree, element, fields, if_true, related.2, owned,
              Option.map_some] using freed
          refine ⟨NativeOps.sourceRelease source address.storage, ?_, ?_⟩
          · simp only [sourceFree, element, fields, and_self, if_true, owned,
              bind, Option.bind_some]
          · rw [← same]
            exact NativeOps.release_correspondence source target related address.storage
      · simp only [targetFree, element, fields, if_true, if_false] at freed; cases freed
    · simp only [targetFree, element, if_false] at freed; cases freed

theorem source_free_other_storage (memory : SourceMemory) (pointer : Address)
    (post : SourceMemory) (freed : sourceFree memory (some pointer) = some post)
    (storage : Nat) (different : storage ≠ pointer.storage) :
    (∀ element, post.cells storage element = memory.cells storage element) ∧
      post.owned storage = memory.owned storage := by
  change (if pointer.element = 0 ∧ pointer.fields = [] then
    (memory.owned pointer.storage).bind (fun _ =>
      some (NativeOps.sourceRelease memory pointer.storage)) else none) = some post at freed
  split at freed
  · cases owned : memory.owned pointer.storage with
    | none => simp only [owned, Option.bind_none] at freed; cases freed
    | some extent =>
      have same : NativeOps.sourceRelease memory pointer.storage = post := by
        apply Option.some.inj
        simpa only [owned, bind, Option.bind_some] using freed
      rw [← same]
      exact ⟨fun _ => by simp only [NativeOps.sourceRelease, if_neg different],
        by simp only [NativeOps.sourceRelease, if_neg different]⟩
  · cases freed

theorem source_freed_allocation_is_dead (memory : SourceMemory) (pointer : Address)
    (post : SourceMemory) (freed : sourceFree memory (some pointer) = some post) :
    (∀ element, post.cells pointer.storage element = none) ∧
      post.owned pointer.storage = none := by
  change (if pointer.element = 0 ∧ pointer.fields = [] then
    (memory.owned pointer.storage).bind (fun _ =>
      some (NativeOps.sourceRelease memory pointer.storage)) else none) = some post at freed
  split at freed
  · cases owned : memory.owned pointer.storage with
    | none => simp only [owned, Option.bind_none] at freed; cases freed
    | some extent =>
      have same : NativeOps.sourceRelease memory pointer.storage = post := by
        apply Option.some.inj
        simpa only [owned, bind, Option.bind_some] using freed
      rw [← same]
      exact ⟨fun _ => by simp only [NativeOps.sourceRelease, if_true],
        by simp only [NativeOps.sourceRelease, if_true]⟩
  · cases freed

theorem null_free_needs_no_live_allocation (memory : SourceMemory) :
    sourceFree memory none = some memory := rfl

theorem interior_pointer_has_no_defined_free (memory : TargetMemory) :
    targetFree memory (some ⟨1, 1, []⟩) = none := rfl

theorem field_pointer_has_no_defined_free (memory : TargetMemory) :
    targetFree memory (some ⟨1, 0, [0]⟩) = none := rfl

theorem dead_allocation_has_no_defined_free (memory : TargetMemory) (storage : Nat)
    (dead : memory.owned storage = none) :
    targetFree memory (some ⟨storage, 0, []⟩) = none := by
  simp only [targetFree, if_true, dead]

end Mettapedia.GSLT.LanguageDef.NativeExecutionFreeStorage
