import Mettapedia.GSLT.LanguageDef.NativeOpsMemory

/-!
Contents of typed borrowed byte views in the native memory profile. A byte
view identifies contiguous live cells; ownership of its storage may belong to
an external scope rather than the operational allocator. Empty views need no
pointer dereference. Missing or incorrectly typed cells have no defined
contents, rather than an invented runtime type fault. Concrete pointer and
stride realization are separate ABI obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

namespace ByteViews

open NativeWord64 (Byte encode)

def advance (address : Address) : Address := { address with element := address.element + 1 }

def sourceByte : SourceValue → Option UInt8
  | .byte value => some (UInt8.ofNat value.val)
  | _ => none

def targetByte : TargetValue → Option UInt8
  | .byte value => some (UInt8.ofBitVec value)
  | _ => none

theorem scalar_byte_correspondence (value : SourceValue) :
    targetByte (encodeValue value) = sourceByte value := by
  cases value <;> try rfl
  case byte value =>
    apply congrArg some
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofBitVec, NativeWord64.encode_toNat, UInt8.toNat_ofNat']
    exact (Nat.mod_eq_of_lt value.isLt).symm

def sourceAt (memory : SourceMemory) (address : Address) : Option UInt8 :=
  (sourceRead memory address).bind sourceByte

def targetAt (memory : TargetMemory) (address : Address) : Option UInt8 :=
  match targetRead memory address with
  | some (.byte value) => some (UInt8.ofBitVec value)
  | _ => none

theorem byte_cell_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetAt target address = sourceAt source address := by
  have asBind : targetAt target address = (targetRead target address).bind targetByte := by
    cases read : targetRead target address with
    | none => simp only [targetAt, read, Option.bind_none]
    | some value => cases value <;> simp only [targetAt, read, Option.bind_some, targetByte]
  rw [asBind, memory_read_correspondence source target related]
  cases read : sourceRead source address with
  | none => simp only [sourceAt, read, Option.map_none, Option.bind_none]
  | some value =>
    simp only [sourceAt, read, Option.map_some, Option.bind_some]
    exact scalar_byte_correspondence value

def sourceBlock (memory : SourceMemory) (address : Address) : Nat → Option (List UInt8)
  | 0 => some []
  | count + 1 => do
      let first ← sourceAt memory address
      let rest ← sourceBlock memory (advance address) count
      some (first :: rest)

def targetBlock (memory : TargetMemory) (address : Address) : Nat → Option (List UInt8)
  | 0 => some []
  | count + 1 =>
      match targetAt memory address with
      | none => none
      | some first =>
        match targetBlock memory (advance address) count with
        | none => none
        | some rest => some (first :: rest)

theorem block_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (count : Nat) (address : Address) :
    targetBlock target address count = sourceBlock source address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
    simp only [targetBlock, sourceBlock, byte_cell_correspondence source target related, ih]
    cases first : sourceAt source address with
    | none => rfl
    | some byte =>
      cases sourceBlock source (advance address) count <;> rfl

theorem source_block_length (memory : SourceMemory) (count : Nat) (address : Address)
    (bytes : List UInt8) (read : sourceBlock memory address count = some bytes) :
    bytes.length = count := by
  induction count generalizing address bytes with
  | zero =>
    have same : [] = bytes := Option.some.inj read
    rw [← same]
    rfl
  | succ count ih =>
    cases first : sourceAt memory address with
    | none => simp [sourceBlock, first, bind, Option.bind] at read
    | some byte =>
      cases tail : sourceBlock memory (advance address) count with
      | none => simp [sourceBlock, first, tail, bind, Option.bind] at read
      | some rest =>
        have same : byte :: rest = bytes := by
          apply Option.some.inj
          simpa only [sourceBlock, first, tail, bind, Option.bind] using read
        rw [← same, List.length_cons, ih (advance address) rest tail]

def sourceView (memory : SourceMemory) : SourceValue → Option (List UInt8)
  | .array .byte address length =>
      if length.val = 0 then some []
      else address.bind (fun base => sourceBlock memory base length.val)
  | _ => none

def targetView (memory : TargetMemory) : TargetValue → Option (List UInt8)
  | .array .byte address length =>
      if length = 0 then some []
      else match address with
        | none => none
        | some base => targetBlock memory base length.toNat
  | _ => none

theorem view_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (view : SourceValue) :
    targetView target (encodeValue view) = sourceView source view := by
  cases view <;> try rfl
  case array element address length =>
    cases element <;> try rfl
    simp only [targetView, sourceView, encodeValue, NativeWord64.encode_eq_zero,
      NativeWord64.encode_toNat]
    by_cases empty : length.val = 0
    · simp only [empty, if_true]
    · simp only [empty, if_false]
      cases address <;> simp [block_correspondence source target related, Option.bind]

theorem source_view_length (memory : SourceMemory) (address : Option Address)
    (length : NativeWord64.Word) (bytes : List UInt8)
    (read : sourceView memory (.array .byte address length) = some bytes) :
    bytes.length = length.val := by
  change (if length.val = 0 then some []
    else address.bind (fun base => sourceBlock memory base length.val)) = some bytes at read
  by_cases empty : length.val = 0
  · rw [if_pos empty] at read
    have same : [] = bytes := Option.some.inj read
    rw [← same, empty]
    rfl
  · rw [if_neg empty] at read
    cases address with
    | none => cases read
    | some base => exact source_block_length memory length.val base bytes read

theorem target_view_length (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Option Address)
    (length : NativeWord64.Word) (bytes : List UInt8)
    (read : targetView target (.array .byte address (encode length)) = some bytes) :
    bytes.length = length.val :=
  source_view_length source address length bytes
    ((view_correspondence source target related (.array .byte address length)).symm.trans read)

theorem released_nonempty_block_unreadable (memory : TargetMemory) (address : Address)
    (remaining : Nat) :
    targetBlock (targetRelease memory address.storage) address (remaining + 1) = none := by
  simp [targetBlock, targetAt, targetRead, targetRelease, Option.bind]

theorem released_nonempty_view_unreadable (memory : TargetMemory) (address : Address)
    (length : BitVec 64) (nonempty : length ≠ 0) :
    targetView (targetRelease memory address.storage) (.array .byte (some address) length) = none := by
  have positive : 0 < length.toNat := by
    have nonzero : length.toNat ≠ 0 := by
      intro zero
      have same : length = 0 := by apply BitVec.eq_of_toNat_eq; exact zero
      exact nonempty same
    exact Nat.pos_of_ne_zero nonzero
  simp only [targetView, nonempty, if_false]
  cases count : length.toNat with
  | zero => simp [count] at positive
  | succ remaining => exact released_nonempty_block_unreadable memory address remaining

private def emptySource : SourceMemory := ⟨fun _ _ => none, fun _ => none⟩
private def emptyTarget : TargetMemory := ⟨fun _ _ => none, fun _ => none⟩
private def base : Address := ⟨1, 0, []⟩
private def byteSource : SourceMemory :=
  ⟨fun storage index => if storage = 1 ∧ index = 0 then some (.byte 255) else none,
    fun _ => none⟩

theorem null_empty_view_has_empty_contents :
    targetView emptyTarget (.array .byte none 0) = some [] := rfl

theorem null_nonempty_view_has_no_contents :
    targetView emptyTarget (.array .byte none 1) = none := by decide +kernel

theorem borrowed_byte_needs_no_allocator_ownership :
    sourceView byteSource (.array .byte (some base) 1) = some [255] ∧
      byteSource.owned base.storage = none := by decide +kernel

theorem wrong_element_type_has_no_byte_view :
    sourceView emptySource (.array .word none 0) = none := rfl

theorem missing_byte_cell_has_no_contents :
    sourceView emptySource (.array .byte (some base) 1) = none := by decide +kernel

theorem empty_view_can_survive_release :
    targetView (targetRelease emptyTarget base.storage) (.array .byte (some base) 0) = some [] := rfl

end ByteViews

end Mettapedia.GSLT.LanguageDef.NativeOps
