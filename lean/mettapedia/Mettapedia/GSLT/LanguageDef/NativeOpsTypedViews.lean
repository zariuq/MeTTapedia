import Mettapedia.GSLT.LanguageDef.NativeOpsByteViews

/-!
# Typed contents of borrowed native arrays

The shared scan retains array order and multiplicity and checks every cell.
Word and nonnull-reference views instantiate the source/target correspondence
with independent scalar decoders. A view establishes readable contents, not
allocator ownership, object identity, or a guest judgment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.TypedViews

open NativeWord64 (Word encode)

def sourceBlock {α : Type} (decode : SourceValue → Option α)
    (memory : SourceMemory) (address : Address) : Nat → Option (List α)
  | 0 => some []
  | count + 1 => do
      let value ← sourceRead memory address
      let first ← decode value
      let rest ← sourceBlock decode memory (ByteViews.advance address) count
      some (first :: rest)

def targetBlock {α : Type} (decode : TargetValue → Option α)
    (memory : TargetMemory) (address : Address) : Nat → Option (List α)
  | 0 => some []
  | count + 1 =>
      match targetRead memory address with
      | none => none
      | some value =>
          match decode value with
          | none => none
          | some first =>
              match targetBlock decode memory (ByteViews.advance address) count with
              | none => none
              | some rest => some (first :: rest)

theorem block_correspondence {α : Type}
    (sourceDecode : SourceValue → Option α) (targetDecode : TargetValue → Option α)
    (scalars : ∀ value, targetDecode (encodeValue value) = sourceDecode value)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (count : Nat) (address : Address) :
    targetBlock targetDecode target address count = sourceBlock sourceDecode source address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
      simp only [targetBlock, sourceBlock, memory_read_correspondence source target related, ih]
      cases sourceRead source address with
      | none => rfl
      | some value =>
          simp only [Option.map_some, scalars, bind, Option.bind]
          cases sourceDecode value <;>
            cases sourceBlock sourceDecode source (ByteViews.advance address) count <;> rfl

theorem source_block_length {α : Type} (decode : SourceValue → Option α)
    (memory : SourceMemory) (count : Nat) (address : Address) (values : List α)
    (read : sourceBlock decode memory address count = some values) : values.length = count := by
  induction count generalizing address values with
  | zero => cases Option.some.inj read; rfl
  | succ count ih =>
      cases cell : sourceRead memory address with
      | none => simp [sourceBlock, cell, bind, Option.bind] at read
      | some value =>
          cases scalar : decode value with
          | none => simp [sourceBlock, cell, scalar, bind, Option.bind] at read
          | some first =>
              cases tail : sourceBlock decode memory (ByteViews.advance address) count with
              | none => simp [sourceBlock, cell, scalar, tail, bind, Option.bind] at read
              | some rest =>
                  have same : first :: rest = values := by
                    apply Option.some.inj
                    simpa only [sourceBlock, cell, scalar, tail, bind, Option.bind] using read
                  rw [← same, List.length_cons, ih (ByteViews.advance address) rest tail]

theorem source_block_all {α : Type} (decode : SourceValue → Option α)
    (property : α → Prop) (scalars : ∀ value result, decode value = some result → property result)
    (memory : SourceMemory) (count : Nat) (address : Address) (values : List α)
    (read : sourceBlock decode memory address count = some values) :
    ∀ value ∈ values, property value := by
  induction count generalizing address values with
  | zero => cases Option.some.inj read; simp
  | succ count ih =>
      cases cell : sourceRead memory address with
      | none => simp [sourceBlock, cell, bind, Option.bind] at read
      | some value =>
          cases scalar : decode value with
          | none => simp [sourceBlock, cell, scalar, bind, Option.bind] at read
          | some first =>
              cases tail : sourceBlock decode memory (ByteViews.advance address) count with
              | none => simp [sourceBlock, cell, scalar, tail, bind, Option.bind] at read
              | some rest =>
                  have same : first :: rest = values := by
                    apply Option.some.inj
                    simpa only [sourceBlock, cell, scalar, tail, bind, Option.bind] using read
                  rw [← same]
                  intro result member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact scalars value _ scalar
                  · exact ih (ByteViews.advance address) rest tail result member

/-- Only the cells traversed by the view have to be preserved. -/
theorem source_block_frame {α : Type} (decode : SourceValue → Option α)
    (before after : SourceMemory) (count : Nat) (address : Address)
    (same : ∀ offset < count,
      sourceRead before { address with element := address.element + offset } =
      sourceRead after { address with element := address.element + offset }) :
    sourceBlock decode before address count = sourceBlock decode after address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
      have head := same 0 (Nat.zero_lt_succ count)
      simp only [Nat.add_zero] at head
      have tail := ih (ByteViews.advance address) (by
        intro offset bound
        have selected := same (offset + 1) (Nat.succ_lt_succ bound)
        simpa only [ByteViews.advance, Nat.add_assoc, Nat.add_comm 1 offset] using selected)
      simp only [sourceBlock, head, tail]

def sourceView {α : Type} (element : NativeType) (decode : SourceValue → Option α)
    (memory : SourceMemory) : SourceValue → Option (List α)
  | .array actual address length =>
      if actual ≠ element then none else
      if length.val = 0 then some []
      else address.bind (fun base => sourceBlock decode memory base length.val)
  | _ => none

def targetView {α : Type} (element : NativeType) (decode : TargetValue → Option α)
    (memory : TargetMemory) : TargetValue → Option (List α)
  | .array actual address length =>
      if actual ≠ element then none else
      if length = 0 then some []
      else match address with
        | none => none
        | some base => targetBlock decode memory base length.toNat
  | _ => none

theorem view_correspondence {α : Type} (element : NativeType)
    (sourceDecode : SourceValue → Option α) (targetDecode : TargetValue → Option α)
    (scalars : ∀ value, targetDecode (encodeValue value) = sourceDecode value)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (view : SourceValue) :
    targetView element targetDecode target (encodeValue view) =
      sourceView element sourceDecode source view := by
  cases view <;> try rfl
  rename_i actual address length
  simp only [targetView, sourceView, encodeValue, NativeWord64.encode_eq_zero,
    NativeWord64.encode_toNat]
  by_cases wrong : actual ≠ element
  · rw [if_pos wrong, if_pos wrong]
  · rw [if_neg wrong, if_neg wrong]
    by_cases empty : length.val = 0
    · simp only [empty, if_true]
    · simp only [empty, if_false]
      cases address <;> simp [block_correspondence sourceDecode targetDecode scalars source target related,
        Option.bind]

theorem source_view_length {α : Type} (element : NativeType)
    (decode : SourceValue → Option α) (memory : SourceMemory) (address : Option Address)
    (length : Word) (values : List α)
    (read : sourceView element decode memory (.array element address length) = some values) :
    values.length = length.val := by
  simp only [sourceView, ne_eq, not_true_eq_false, if_false] at read
  by_cases empty : length.val = 0
  · rw [if_pos empty] at read
    cases Option.some.inj read
    exact empty.symm
  · rw [if_neg empty] at read
    cases address with
    | none => cases read
    | some base => exact source_block_length decode memory length.val base values read

theorem source_view_all {α : Type} (element : NativeType)
    (decode : SourceValue → Option α) (property : α → Prop)
    (scalars : ∀ value result, decode value = some result → property result)
    (memory : SourceMemory) (address : Option Address) (length : Word) (values : List α)
    (read : sourceView element decode memory (.array element address length) = some values) :
    ∀ value ∈ values, property value := by
  simp only [sourceView, ne_eq, not_true_eq_false, if_false] at read
  by_cases empty : length.val = 0
  · rw [if_pos empty] at read
    cases Option.some.inj read
    simp
  · rw [if_neg empty] at read
    cases address with
    | none => cases read
    | some base => exact source_block_all decode property scalars memory length.val base values read

def sourceWord : SourceValue → Option Nat
  | .word value => some value.val
  | _ => none

def targetWord : TargetValue → Option Nat
  | .word value => some value.toNat
  | _ => none

theorem word_scalar_correspondence (value : SourceValue) :
    targetWord (encodeValue value) = sourceWord value := by
  cases value <;> rfl

theorem source_word_bound (value : SourceValue) (word : Nat) (read : sourceWord value = some word) :
    word < 2 ^ 64 := by
  cases value <;> simp only [sourceWord, reduceCtorEq] at read
  rename_i wordValue
  cases Option.some.inj read
  exact wordValue.isLt

theorem word_view_bounded (memory : SourceMemory) (address : Option Address) (length : Word)
    (values : List Nat) (read : sourceView .word sourceWord memory (.array .word address length) =
      some values) : ∀ value ∈ values, value < 2 ^ 64 :=
  source_view_all .word sourceWord (fun value => value < 2 ^ 64) source_word_bound
    memory address length values read

def sourceReference : SourceValue → Option Address
  | .reference (some address) => some address
  | _ => none

def targetReference : TargetValue → Option Address
  | .reference (some address) => some address
  | _ => none

theorem reference_scalar_correspondence (value : SourceValue) :
    targetReference (encodeValue value) = sourceReference value := by
  cases value <;> try rfl
  rename_i address
  cases address <;> rfl

theorem word_view_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (view : SourceValue) :
    targetView .word targetWord target (encodeValue view) = sourceView .word sourceWord source view :=
  view_correspondence .word sourceWord targetWord word_scalar_correspondence source target related view

theorem reference_view_correspondence (element : NativeType)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (view : SourceValue) :
    targetView (.ref element) targetReference target (encodeValue view) =
      sourceView (.ref element) sourceReference source view :=
  view_correspondence (.ref element) sourceReference targetReference reference_scalar_correspondence
    source target related view

theorem null_nonempty_has_no_contents {α : Type} (element : NativeType)
    (decode : SourceValue → Option α) (memory : SourceMemory) (length : Word)
    (nonempty : length.val ≠ 0) :
    sourceView element decode memory (.array element none length) = none := by
  simp only [sourceView, ne_eq, not_true_eq_false, if_false, nonempty, Option.bind_none]

theorem null_empty_has_empty_contents {α : Type} (element : NativeType)
    (decode : SourceValue → Option α) (memory : SourceMemory) :
    sourceView element decode memory (.array element none 0) = some [] := by
  simp only [sourceView, ne_eq, not_true_eq_false, if_false, Fin.val_zero, if_true]

theorem wrong_element_has_no_contents {α : Type} (expected actual : NativeType)
    (decode : SourceValue → Option α) (memory : SourceMemory) (address : Option Address)
    (length : Word) (different : actual ≠ expected) :
    sourceView expected decode memory (.array actual address length) = none := by
  change (if actual ≠ expected then none else
    if length.val = 0 then some [] else
      address.bind (fun base => sourceBlock decode memory base length.val)) = none
  rw [if_pos different]

private def testBase : Address := ⟨7, 0, []⟩
private def testMemory : SourceMemory :=
  ⟨fun storage index =>
      if storage ≠ 7 then none else
      if index = 0 then some (.word 4) else
      if index = 1 then some (.word 4) else
      if index = 2 then some (.word 9) else none,
    fun _ => none⟩

theorem ordered_repeated_words_retained :
    sourceView .word sourceWord testMemory (.array .word (some testBase) 3) = some [4, 4, 9] := by
  decide +kernel

theorem missing_word_not_defaulted :
    sourceView .word sourceWord testMemory (.array .word (some testBase) 4) = none := by
  decide +kernel

theorem word_cell_is_not_a_reference :
    sourceView (.ref (.named "Term")) sourceReference testMemory
      (.array (.ref (.named "Term")) (some testBase) 1) = none := by
  decide +kernel

theorem null_reference_is_not_a_term_address : sourceReference (.reference none) = none := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.TypedViews
