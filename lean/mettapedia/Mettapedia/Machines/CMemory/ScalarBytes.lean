import Mettapedia.Machines.CMemory.Values
import Mettapedia.GSLT.LanguageDef.NativeOpsCScalarRead

/-!
# Typed byte requests at the cell-memory boundary

This fragment distinguishes UInt32 counts, unsigned 64-bit guards and size_t
allocation expressions. sizeof inspects a retained type, not a pointee. The
supported ABI parameters describe 32- or 64-bit size_t and equally sized
object pointers. Their relation to a native ABI is a separate obligation.

Unsigned multiplication wraps at its actual width. A successful wide guard
then proves that the allocation multiplication does not wrap and requests
exactly a whole number of cells. Unsupported types are not assigned a size.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ScalarBytes

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

inductive SizeWidth where
  | bits32
  | bits64
  deriving DecidableEq, Repr

def SizeWidth.modulus : SizeWidth → Nat
  | .bits32 => 2 ^ 32
  | .bits64 => 2 ^ 64

structure ABI where
  sizeWidth : SizeWidth
  pointerBytes : Nat
  pointerPositive : 0 < pointerBytes
  pointerBounded : pointerBytes < 2 ^ 32

def ABI.sizeMaximum (abi : ABI) : Nat := abi.sizeWidth.modulus - 1

abbrev Types := Name → Option CType

/-- Field typing belongs to the admitted record layout, independently of
its scalar values and native byte extent. -/
abbrev FieldTypes := CType → Name → Option CType

/-- Recover an operand's type without reading its value. Default field typing
retains the established pointer/cast fragment; record profiles supply their
field types explicitly. -/
def typeOf? (types : Types) (operand : CExpr)
    (fields : FieldTypes := fun _ _ => none) : Option CType := match operand with
  | .identifier name => types name
  | .unary .dereference operand => do
      let type ← typeOf? types operand fields
      match type.pointers with
      | 0 => none
      | depth + 1 => some ⟨type.name, depth⟩
  | .unary .address operand => do
      let type ← typeOf? types operand fields
      some ⟨type.name, type.pointers + 1⟩
  | .field owner name throughPointer => do
      let type ← typeOf? types owner fields
      if throughPointer then
        match type.pointers with
        | 0 => none
        | depth + 1 => fields ⟨type.name, depth⟩ name
      else fields type name
  | .cast type _ => some type
  | _ => none

theorem field_type_does_not_read_owner (types : Types) (fields : FieldTypes)
    (owner : CExpr) (name : Name) (type : CType) (fieldType : CType)
    (typed : typeOf? types owner fields = some ⟨type.name, type.pointers + 1⟩)
    (declared : fields type name = some fieldType) :
    typeOf? types (.field owner name true) fields = some fieldType := by
  simp only [typeOf?, typed, bind, Option.bind_some, declared, ↓reduceIte]

theorem pointer_field_requires_pointer_owner (types : Types) (fields : FieldTypes)
    (owner : CExpr) (name : Name) (typeName : Name)
    (typed : typeOf? types owner fields = some ⟨typeName, 0⟩) :
    typeOf? types (.field owner name true) fields = none := by
  simp only [typeOf?, typed, bind, Option.bind_some, ↓reduceIte]

def typeBytes? (abi : ABI) (type : CType) : Option Nat :=
  if 0 < type.pointers then some abi.pointerBytes else none

inductive Kind where
  | size
  | unsigned64
  deriving DecidableEq, Repr

structure Wide where
  kind : Kind
  value : Nat
  deriving DecidableEq, Repr

def Kind.modulus (abi : ABI) : Kind → Nat
  | .size => abi.sizeWidth.modulus
  | .unsigned64 => 2 ^ 64

def promote (left right : Kind) : Kind :=
  if left = .unsigned64 ∨ right = .unsigned64 then .unsigned64 else .size

def multiply (abi : ABI) (left right : Wide) : Wide :=
  let kind := promote left.kind right.kind
  ⟨kind, (left.value * right.value) % kind.modulus abi⟩

/-- Pure, typed wide operands. Casts in this fragment take pure UInt32 values;
an indirect or absent scalar binding therefore has no wide evaluation. -/
def wide? (abi : ABI) (types : Types) (values : ScalarRead.Environment Ptr) :
    CExpr → Option Wide
  | .identifier name =>
      if name = "SIZE_MAX".toList then some ⟨.size, abi.sizeMaximum⟩ else none
  | .cast type operand => do
      let .unsigned value ← ScalarRead.expression values (fun _ _ => none) operand | none
      if type = ⟨"uint64_t".toList, 0⟩ then some ⟨.unsigned64, value.toNat⟩
      else if type = ⟨"size_t".toList, 0⟩ then
        some ⟨.size, value.toNat % abi.sizeWidth.modulus⟩
      else none
  | .sizeOf type => (typeBytes? abi type).map (Wide.mk .size)
  | .sizeOfExpr operand => do
      let type ← typeOf? types operand
      (typeBytes? abi type).map (Wide.mk .size)
  | .binary .mul left right => do
      let first ← wide? abi types values left
      let second ← wide? abi types values right
      some (multiply abi first second)
  | _ => none

/-- Requests that do not cover whole cells have no cell-memory interpretation. -/
def cells? (abi : ABI) (bytes : Nat) : Option Nat :=
  if bytes % abi.pointerBytes = 0 then some (bytes / abi.pointerBytes) else none

theorem size_modulus_positive (width : SizeWidth) : 0 < width.modulus := by
  cases width <;> norm_num [SizeWidth.modulus]

theorem word_fits_size (width : SizeWidth) (word : UInt32) :
    word.toNat < width.modulus := by
  have bound := word.toNat_lt
  cases width <;> norm_num [SizeWidth.modulus] at * <;> omega

theorem size_cast_exact (width : SizeWidth) (word : UInt32) :
    word.toNat % width.modulus = word.toNat :=
  Nat.mod_eq_of_lt (word_fits_size width word)

theorem word_pointer_product_fits_unsigned64 (abi : ABI) (word : UInt32) :
    word.toNat * abi.pointerBytes < 2 ^ 64 := by
  have wordBound := word.toNat_lt
  have pointerBound := abi.pointerBounded
  have bounded : word.toNat * abi.pointerBytes ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  norm_num at bounded ⊢
  omega

theorem unsigned64_guard_product_exact (abi : ABI) (word : UInt32) :
    multiply abi ⟨.unsigned64, word.toNat⟩ ⟨.size, abi.pointerBytes⟩ =
      ⟨.unsigned64, word.toNat * abi.pointerBytes⟩ := by
  change Wide.mk .unsigned64 ((word.toNat * abi.pointerBytes) % (2 ^ 64)) = _
  rw [Nat.mod_eq_of_lt (word_pointer_product_fits_unsigned64 abi word)]

theorem guarded_size_product_exact (abi : ABI) (word : UInt32)
    (guard : word.toNat * abi.pointerBytes ≤ abi.sizeMaximum) :
    multiply abi ⟨.size, abi.pointerBytes⟩
      ⟨.size, word.toNat % abi.sizeWidth.modulus⟩ =
      ⟨.size, abi.pointerBytes * word.toNat⟩ := by
  have below : abi.pointerBytes * word.toNat < abi.sizeWidth.modulus := by
    have positive := size_modulus_positive abi.sizeWidth
    simp only [ABI.sizeMaximum] at guard
    rw [Nat.mul_comm] at guard
    omega
  simp [multiply, promote, Kind.modulus, size_cast_exact,
    Nat.mod_eq_of_lt below]

theorem whole_cell_request_exact (abi : ABI) (extent : Nat) :
    cells? abi (abi.pointerBytes * extent) = some extent := by
  simp [cells?, Nat.mul_div_cancel_left _ abi.pointerPositive]

theorem cell_request_reconstructs_bytes (abi : ABI) (bytes extent : Nat)
    (accepted : cells? abi bytes = some extent) :
    abi.pointerBytes * extent = bytes := by
  unfold cells? at accepted
  split at accepted
  · rename_i whole
    have same : bytes / abi.pointerBytes = extent := Option.some.inj accepted
    rw [← same]
    have decomposition := Nat.mod_add_div bytes abi.pointerBytes
    rw [whole, Nat.zero_add] at decomposition
    exact decomposition
  · cases accepted

namespace Controls

def abi32 : ABI := ⟨.bits32, 4, by decide, by decide⟩
def abi64 : ABI := ⟨.bits64, 8, by decide, by decide⟩

theorem size32_multiplication_wraps :
    multiply abi32 ⟨.size, 4⟩ ⟨.size, 1073741824⟩ = ⟨.size, 0⟩ := rfl

theorem unsigned64_guard_detects_that_wrap :
    abi32.sizeMaximum <
      (multiply abi32 ⟨.unsigned64, 1073741824⟩ ⟨.size, 4⟩).value := by
  decide

theorem size64_same_request_does_not_wrap :
    multiply abi64 ⟨.size, 8⟩ ⟨.size, 1073741824⟩ = ⟨.size, 8589934592⟩ := rfl

theorem partial_cell_not_truncated : cells? abi64 9 = none := rfl

theorem sizeof_does_not_load_values (values other : ScalarRead.Environment Ptr) :
    wide? abi64 (fun name => if name = "p".toList then some ⟨"Space".toList, 2⟩ else none)
      values (.sizeOfExpr (.unary .dereference (.identifier "p".toList))) =
    wide? abi64 (fun name => if name = "p".toList then some ⟨"Space".toList, 2⟩ else none)
      other (.sizeOfExpr (.unary .dereference (.identifier "p".toList))) := rfl

theorem absent_type_is_not_pointer_size :
    wide? abi64 (fun _ => none) (fun _ => none)
      (.sizeOfExpr (.unary .dereference (.identifier "p".toList))) = none := rfl

theorem dereferencing_scalar_has_no_size :
    typeOf? (fun _ => some ⟨"uint32_t".toList, 0⟩)
      (.unary .dereference (.identifier "p".toList)) = none := rfl

end Controls

end Mettapedia.Machines.CMemory.ScalarBytes
