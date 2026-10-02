import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryExtension

/-!
# Scalar array contents are separate from root record contents

Replacing a record cell preserves scalar views whose addresses have no field
path. Each scalar decoder must actually reject records. A borrowed view into a
record field does not meet the address premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.RecordScalarFrame

open NativeWord64 (Word)

theorem scalar_read {α : Type} (decode : SourceValue → Option α)
    (rejects : ∀ name fields, decode (.record name fields) = none)
    (memory : SourceMemory) (storage element : Nat) (name : String)
    (before after : List SourceValue) (stored : memory.cells storage element = some (.record name before))
    (address : Address) (rooted : address.fields = []) :
    (sourceRead (sourceStoreCell memory storage element (.record name after)) address).bind decode =
      (sourceRead memory address).bind decode := by
  cases address with
  | mk object index fields =>
      cases rooted
      by_cases same : object = storage ∧ index = element
      · rcases same with ⟨rfl, rfl⟩
        simp only [sourceRead, sourceStoreCell, and_self, if_true, stored, Option.bind_some,
          sourceReadPath, rejects]
      · simp only [sourceRead, sourceStoreCell, same, if_false]

theorem block {α : Type} (decode : SourceValue → Option α)
    (rejects : ∀ name fields, decode (.record name fields) = none)
    (memory : SourceMemory) (storage element : Nat) (name : String)
    (before after : List SourceValue) (stored : memory.cells storage element = some (.record name before))
    (count : Nat) (address : Address) (rooted : address.fields = []) :
    TypedViews.sourceBlock decode (sourceStoreCell memory storage element (.record name after)) address count =
      TypedViews.sourceBlock decode memory address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
      have head := scalar_read decode rejects memory storage element name before after stored address rooted
      have tail := ih (ByteViews.advance address) rooted
      simp only [TypedViews.sourceBlock, tail, bind]
      rw [← Option.bind_assoc, ← Option.bind_assoc, head]

theorem view {α : Type} (type : NativeType) (decode : SourceValue → Option α)
    (rejects : ∀ name fields, decode (.record name fields) = none)
    (memory : SourceMemory) (storage element : Nat) (name : String)
    (before after : List SourceValue) (stored : memory.cells storage element = some (.record name before))
    (address : Option Address) (length : Word)
    (rooted : ∀ base, address = some base → base.fields = []) :
    TypedViews.sourceView type decode (sourceStoreCell memory storage element (.record name after))
        (.array type address length) =
      TypedViews.sourceView type decode memory (.array type address length) := by
  change (if type ≠ type then none else if length.val = 0 then some [] else
    address.bind (fun base => TypedViews.sourceBlock decode
      (sourceStoreCell memory storage element (.record name after)) base length.val)) = _
  rw [if_neg (not_not_intro rfl)]
  change (if length.val = 0 then some [] else address.bind _) =
    (if type ≠ type then none else if length.val = 0 then some [] else address.bind _)
  rw [if_neg (not_not_intro rfl)]
  by_cases empty : length.val = 0
  · rw [if_pos empty, if_pos empty]
  · rw [if_neg empty, if_neg empty]
    cases address with
    | none => rfl
    | some base =>
        exact block decode rejects memory storage element name before after stored
          length.val base (rooted base rfl)

theorem word_view (memory : SourceMemory) (storage element : Nat) (name : String)
    (before after : List SourceValue) (stored : memory.cells storage element = some (.record name before))
    (address : Option Address) (length : Word)
    (rooted : ∀ base, address = some base → base.fields = []) :
    TypedViews.sourceView .word TypedViews.sourceWord
        (sourceStoreCell memory storage element (.record name after)) (.array .word address length) =
      TypedViews.sourceView .word TypedViews.sourceWord memory (.array .word address length) :=
  view .word _ (fun _ _ => rfl) memory storage element name before after stored address length rooted

theorem reference_view (type : NativeType) (memory : SourceMemory) (storage element : Nat) (name : String)
    (before after : List SourceValue) (stored : memory.cells storage element = some (.record name before))
    (address : Option Address) (length : Word)
    (rooted : ∀ base, address = some base → base.fields = []) :
    TypedViews.sourceView (.ref type) TypedViews.sourceReference
        (sourceStoreCell memory storage element (.record name after)) (.array (.ref type) address length) =
      TypedViews.sourceView (.ref type) TypedViews.sourceReference memory (.array (.ref type) address length) :=
  view (.ref type) _ (fun _ _ => rfl) memory storage element name before after stored address length rooted

theorem byte_view (memory : SourceMemory) (storage element : Nat) (name : String)
    (before after : List SourceValue) (stored : memory.cells storage element = some (.record name before))
    (address : Option Address) (length : Word)
    (rooted : ∀ base, address = some base → base.fields = []) :
    ByteViews.sourceView (sourceStoreCell memory storage element (.record name after)) (.array .byte address length) =
      ByteViews.sourceView memory (.array .byte address length) := by
  by_cases empty : length.val = 0
  · simp only [ByteViews.sourceView, empty, if_true]
  · simp only [ByteViews.sourceView, empty, if_false]
    cases address with
    | none => rfl
    | some base =>
        simp only [Option.bind_some, MemoryExtension.byte_block_as_typed]
        exact block ByteViews.sourceByte (fun _ _ => rfl) memory storage element name before after stored
          length.val base (rooted base rfl)

end Mettapedia.GSLT.LanguageDef.NativeOps.RecordScalarFrame
