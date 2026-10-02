import Mettapedia.GSLT.LanguageDef.NativeOpsTypedViews

/-!
# Memory extension by filling previously absent cells

Existing values and nested field reads survive an extension. Missing cells may
be filled; ownership is not inferred from their contents. Overwriting or
releasing an existing cell does not satisfy this relation in general.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.MemoryExtension

open NativeWord64 (Word)

def Extends (before after : SourceMemory) : Prop :=
  ∀ storage element value, before.cells storage element = some value →
    after.cells storage element = some value

theorem refl (memory : SourceMemory) : Extends memory memory := fun _ _ _ read => read

theorem trans {first second third : SourceMemory}
    (left : Extends first second) (right : Extends second third) : Extends first third :=
  fun storage element value read => right storage element value (left storage element value read)

theorem fresh_cell_store (memory : SourceMemory) (storage element : Nat) (value : SourceValue)
    (fresh : memory.cells storage element = none) :
    Extends memory (sourceStoreCell memory storage element value) := by
  intro other index old read
  by_cases same : other = storage ∧ index = element
  · rcases same with ⟨rfl, rfl⟩
    rw [fresh] at read
    contradiction
  · simp only [sourceStoreCell, same, if_false]
    exact read

theorem successful_read {before after : SourceMemory} (preserves : Extends before after)
    {address : Address} {value : SourceValue} (read : sourceRead before address = some value) :
    sourceRead after address = some value := by
  cases old : before.cells address.storage address.element with
  | none => simp [sourceRead, old] at read
  | some cell =>
      simpa only [sourceRead, preserves _ _ _ old, Option.bind_some] using
        (show sourceReadPath address.fields cell = some value from by
          simpa only [sourceRead, old, Option.bind_some] using read)

theorem typed_block {α : Type} (decode : SourceValue → Option α)
    {before after : SourceMemory} (preserves : Extends before after)
    (count : Nat) (address : Address) (values : List α)
    (read : TypedViews.sourceBlock decode before address count = some values) :
    TypedViews.sourceBlock decode after address count = some values := by
  induction count generalizing address values with
  | zero => exact read
  | succ count ih =>
      cases cellRead : sourceRead before address with
      | none => simp [TypedViews.sourceBlock, cellRead] at read
      | some cell =>
          cases decoded : decode cell with
          | none => simp [TypedViews.sourceBlock, cellRead, decoded] at read
          | some first =>
              cases tailRead : TypedViews.sourceBlock decode before (ByteViews.advance address) count with
              | none => simp [TypedViews.sourceBlock, cellRead, tailRead] at read
              | some tail =>
                  have targetHead := successful_read preserves cellRead
                  have targetTail := ih (ByteViews.advance address) tail tailRead
                  simpa only [TypedViews.sourceBlock, targetHead, decoded, targetTail,
                    bind, Option.bind] using (show some (first :: tail) = some values from by
                      simpa only [TypedViews.sourceBlock, cellRead, decoded, tailRead,
                        bind, Option.bind] using read)

theorem typed_view {α : Type} (element : NativeType) (decode : SourceValue → Option α)
    {before after : SourceMemory} (preserves : Extends before after)
    (value : SourceValue) (values : List α)
    (read : TypedViews.sourceView element decode before value = some values) :
    TypedViews.sourceView element decode after value = some values := by
  cases value with
  | unit => change (none : Option (List α)) = some values at read; contradiction
  | word _ => change (none : Option (List α)) = some values at read; contradiction
  | byte _ => change (none : Option (List α)) = some values at read; contradiction
  | bool _ => change (none : Option (List α)) = some values at read; contradiction
  | record _ _ => change (none : Option (List α)) = some values at read; contradiction
  | reference _ => change (none : Option (List α)) = some values at read; contradiction
  | array actual address count =>
      change (if actual ≠ element then none else
        if count.val = 0 then some [] else
          address.bind (fun base => TypedViews.sourceBlock decode before base count.val)) = some values at read
      change (if actual ≠ element then none else
        if count.val = 0 then some [] else
          address.bind (fun base => TypedViews.sourceBlock decode after base count.val)) = some values
      by_cases matching : actual ≠ element
      · rw [if_pos matching] at read
        contradiction
      · rw [if_neg matching] at read ⊢
        by_cases empty : count.val = 0
        · rw [if_pos empty] at read ⊢
          exact read
        · rw [if_neg empty] at read ⊢
          cases address with
          | none => contradiction
          | some base => exact typed_block decode preserves count.val base values read

theorem byte_block_as_typed (memory : SourceMemory) (count : Nat) (address : Address) :
    ByteViews.sourceBlock memory address count =
      TypedViews.sourceBlock ByteViews.sourceByte memory address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
      simp only [ByteViews.sourceBlock, ByteViews.sourceAt, TypedViews.sourceBlock, ih]
      cases sourceRead memory address <;> rfl

theorem byte_view {before after : SourceMemory} (preserves : Extends before after)
    (address : Option Address) (length : Word) (values : List UInt8)
    (read : ByteViews.sourceView before (.array .byte address length) = some values) :
    ByteViews.sourceView after (.array .byte address length) = some values := by
  by_cases empty : length.val = 0
  · simpa only [ByteViews.sourceView, empty, if_true] using read
  · cases address with
    | none => simp only [ByteViews.sourceView, empty, if_false, Option.bind_none] at read
              contradiction
    | some base =>
        simp only [ByteViews.sourceView, empty, if_false, Option.bind_some, byte_block_as_typed] at read ⊢
        exact typed_block ByteViews.sourceByte preserves length.val base values read

def occupied : SourceMemory :=
  ⟨fun storage element => if storage = 4 ∧ element = 0 then some (.word 7) else none,
    fun _ => none⟩

theorem fresh_insertion_keeps_old_cell :
    sourceRead (sourceStoreCell occupied 5 0 (.word 8)) ⟨4, 0, []⟩ = some (.word 7) :=
  successful_read (fresh_cell_store occupied 5 0 (.word 8) rfl) rfl

theorem replacing_old_value_is_not_an_extension :
    ¬ Extends occupied (sourceStoreCell occupied 4 0 (.word 8)) := by
  intro extension
  have same := extension 4 0 (.word 7) rfl
  change some (SourceValue.word 8) = some (.word 7) at same
  cases same

theorem release_is_not_an_extension : ¬ Extends occupied (sourceRelease occupied 4) := by
  intro extension
  have same := extension 4 0 (.word 7) rfl
  change none = some (SourceValue.word 7) at same
  contradiction

end Mettapedia.GSLT.LanguageDef.NativeOps.MemoryExtension
