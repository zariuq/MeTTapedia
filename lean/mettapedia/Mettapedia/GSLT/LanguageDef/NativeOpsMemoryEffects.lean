import Mettapedia.GSLT.LanguageDef.NativeOpsMemory

/-!
Observable cell effects of successful native writes. Nested record paths read
back the assigned value; writes preserve ownership and all other storage cells.
Pointer aliases name the same logical address, so caller-visible writes remain
visible to a later read. This file concerns defined writes and does not turn a
dangling or incorrectly typed pointer into a runtime context fault.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

theorem source_path_after_write (path : List Nat) (replacement previous updated : SourceValue)
    (wrote : sourceWritePath path replacement previous = some updated) :
    sourceReadPath path updated = some replacement := by
  induction path generalizing previous updated with
  | nil =>
    have same : replacement = updated := Option.some.inj wrote
    rw [← same]
    rfl
  | cons index rest ih =>
    cases previous <;> try cases wrote
    case record name fields =>
      cases selected : fields[index]? with
      | none =>
          simp only [sourceWritePath, selected, bind, Option.bind_none] at wrote
          cases wrote
      | some child =>
        cases changed : sourceWritePath rest replacement child with
        | none =>
            simp only [sourceWritePath, selected, changed, bind,
              Option.bind_some, Option.bind_none] at wrote
            cases wrote
        | some value =>
          have same : SourceValue.record name (fields.set index value) = updated := by
            apply Option.some.inj
            simpa only [sourceWritePath, selected, changed, bind, Option.bind_some] using wrote
          rw [← same]
          have inRange : index < fields.length := (List.getElem?_eq_some_iff.mp selected).1
          simp only [sourceReadPath, List.getElem?_set_self inRange, Option.bind_some]
          exact ih child value changed

theorem source_read_after_write (memory : SourceMemory) (address : Address)
    (replacement : SourceValue) (post : SourceMemory)
    (wrote : sourceWrite memory address replacement = some post) :
    sourceRead post address = some replacement := by
  cases previous : memory.cells address.storage address.element with
  | none =>
      simp only [sourceWrite, previous, bind, Option.bind_none] at wrote
      cases wrote
  | some old =>
    cases changed : sourceWritePath address.fields replacement old with
    | none =>
        simp only [sourceWrite, previous, changed, bind,
          Option.bind_some, Option.bind_none] at wrote
        cases wrote
    | some value =>
      have same : sourceStoreCell memory address.storage address.element value = post := by
        apply Option.some.inj
        simpa only [sourceWrite, previous, changed, bind, Option.bind_some] using wrote
      rw [← same]
      simp only [sourceRead, sourceStoreCell, and_self, if_true, Option.bind_some]
      exact source_path_after_write address.fields replacement old value changed

theorem source_write_preserves_owned (memory : SourceMemory) (address : Address)
    (replacement : SourceValue) (post : SourceMemory)
    (wrote : sourceWrite memory address replacement = some post) : post.owned = memory.owned := by
  cases previous : memory.cells address.storage address.element with
  | none =>
      simp only [sourceWrite, previous, bind, Option.bind_none] at wrote
      cases wrote
  | some old =>
    cases changed : sourceWritePath address.fields replacement old with
    | none =>
        simp only [sourceWrite, previous, changed, bind,
          Option.bind_some, Option.bind_none] at wrote
        cases wrote
    | some value =>
      have same : sourceStoreCell memory address.storage address.element value = post := by
        apply Option.some.inj
        simpa only [sourceWrite, previous, changed, bind, Option.bind_some] using wrote
      rw [← same]
      rfl

theorem source_write_preserves_other_cells (memory : SourceMemory) (address : Address)
    (replacement : SourceValue) (post : SourceMemory)
    (wrote : sourceWrite memory address replacement = some post)
    (storage element : Nat) (other : storage ≠ address.storage ∨ element ≠ address.element) :
    post.cells storage element = memory.cells storage element := by
  cases previous : memory.cells address.storage address.element with
  | none =>
      simp only [sourceWrite, previous, bind, Option.bind_none] at wrote
      cases wrote
  | some old =>
    cases changed : sourceWritePath address.fields replacement old with
    | none =>
        simp only [sourceWrite, previous, changed, bind,
          Option.bind_some, Option.bind_none] at wrote
        cases wrote
    | some value =>
      have same : sourceStoreCell memory address.storage address.element value = post := by
        apply Option.some.inj
        simpa only [sourceWrite, previous, changed, bind, Option.bind_some] using wrote
      rw [← same]
      have distinct : ¬ (storage = address.storage ∧ element = address.element) := by
        rintro ⟨sameStorage, sameElement⟩
        exact other.elim (fun different => different sameStorage) (fun different => different sameElement)
      simp only [sourceStoreCell, distinct, if_false]

theorem source_write_preserves_other_reads (memory : SourceMemory) (address : Address)
    (replacement : SourceValue) (post : SourceMemory)
    (wrote : sourceWrite memory address replacement = some post)
    (otherAddress : Address)
    (other : otherAddress.storage ≠ address.storage ∨ otherAddress.element ≠ address.element) :
    sourceRead post otherAddress = sourceRead memory otherAddress := by
  simp only [sourceRead, source_write_preserves_other_cells memory address replacement post wrote
    otherAddress.storage otherAddress.element other]

theorem target_read_after_write (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (replacement : SourceValue)
    (post : TargetMemory) (wrote : targetWrite target address (encodeValue replacement) = some post) :
    targetRead post address = some (encodeValue replacement) := by
  obtain ⟨sourcePost, sourceWrote, postRelated⟩ :=
    memory_write_backward source target related address replacement post wrote
  rw [memory_read_correspondence sourcePost post postRelated,
    source_read_after_write source address replacement sourcePost sourceWrote]
  rfl

theorem target_write_preserves_other_reads (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (replacement : SourceValue)
    (post : TargetMemory) (wrote : targetWrite target address (encodeValue replacement) = some post)
    (otherAddress : Address)
    (other : otherAddress.storage ≠ address.storage ∨ otherAddress.element ≠ address.element) :
    targetRead post otherAddress = targetRead target otherAddress := by
  obtain ⟨sourcePost, sourceWrote, postRelated⟩ :=
    memory_write_backward source target related address replacement post wrote
  rw [memory_read_correspondence sourcePost post postRelated,
    source_write_preserves_other_reads source address replacement sourcePost sourceWrote otherAddress other,
    memory_read_correspondence source target related]

private def callerSlot : Address := ⟨4, 0, []⟩
private def nestedSlot : Address := ⟨4, 0, [1, 0]⟩
private def untouchedSlot : Address := ⟨5, 0, []⟩
private def completedHandle : Address := ⟨9, 0, []⟩
private def borrowedCallerMemory : SourceMemory :=
  ⟨fun storage index =>
    if storage = 4 ∧ index = 0 then some (.reference none)
    else if storage = 5 ∧ index = 0 then some (.word 42) else none,
    fun _ => none⟩
private def nestedMemory : SourceMemory :=
  ⟨fun storage index => if storage = 4 ∧ index = 0 then
      some (.record "outer" [.word 7, .record "inner" [.reference none, .bool true]]) else none,
    fun _ => none⟩

theorem publication_is_visible_through_caller_alias :
    (sourceWrite borrowedCallerMemory callerSlot (.reference (some completedHandle))).bind
      (fun post => sourceRead post callerSlot) = some (.reference (some completedHandle)) := rfl

theorem publication_preserves_other_storage :
    (sourceWrite borrowedCallerMemory callerSlot (.reference (some completedHandle))).bind
      (fun post => sourceRead post untouchedSlot) = some (.word 42) := rfl

theorem nested_publication_preserves_sibling_fields :
    (sourceWrite nestedMemory nestedSlot (.reference (some completedHandle))).bind
      (fun post => sourceRead post ⟨4, 0, [0]⟩) = some (.word 7) := rfl

theorem nested_publication_reaches_the_exact_field :
    (sourceWrite nestedMemory nestedSlot (.reference (some completedHandle))).bind
      (fun post => sourceRead post nestedSlot) = some (.reference (some completedHandle)) := rfl

theorem unowned_borrowed_caller_slot_accepts_a_defined_write :
    borrowedCallerMemory.owned callerSlot.storage = none ∧
      ∃ post, sourceWrite borrowedCallerMemory callerSlot (.reference (some completedHandle)) =
        some post := by
  exact ⟨rfl, _, rfl⟩

theorem missing_caller_slot_has_no_write :
    sourceWrite borrowedCallerMemory ⟨6, 0, []⟩ (.reference (some completedHandle)) = none := rfl

theorem missing_nested_field_has_no_write :
    sourceWrite nestedMemory ⟨4, 0, [1, 2]⟩ (.reference (some completedHandle)) = none := rfl

theorem scalar_dereference_has_no_nested_write :
    sourceWrite nestedMemory ⟨4, 0, [0, 0]⟩ (.reference (some completedHandle)) = none := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps
