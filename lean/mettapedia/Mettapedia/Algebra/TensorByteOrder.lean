import Std

/-!
# Scalar byte order at an immutable tensor boundary

The reference assigns base-256 positional weights. The implementation performs
a host-order accumulator load after conditionally reversing one complete cell.
Storage bytes and declared order remain physical metadata; semantic loads do
not rewrite either. Selected cell addresses are supplied by the independently
qualified stride/bounds layer, and repeated addresses remain repeated reads.
Words denote unsigned bit patterns, before signed or floating interpretation.

This does not verify native pointer arithmetic, hardware loads, floating-point
interpretation, allocation, scratch lifetime or external-owner callbacks.
-/

set_option autoImplicit false
namespace Mettapedia.Algebra.TensorByteOrder

abbrev Byte := Fin 256

inductive Endian where
  | little
  | big
  deriving DecidableEq, Repr

inductive Declared where
  | native
  | little
  | big
  deriving DecidableEq, Repr

def resolve (host : Endian) : Declared → Endian
  | .native => host
  | .little => .little
  | .big => .big

namespace Reference

/-- Each byte is weighted by its number of following bytes. -/
def positional : List Byte → Nat
  | [] => 0
  | byte :: rest => byte.val * 256 ^ rest.length + positional rest

def word (order : Endian) (bytes : List Byte) : Nat :=
  match order with
  | .big => positional bytes
  | .little => positional bytes.reverse

end Reference

namespace Native

def accumulate (word : Nat) (byte : Byte) : Nat := word * 256 + byte.val

def hostLoad (host : Endian) (bytes : List Byte) : Nat :=
  match host with
  | .big => bytes.foldl accumulate 0
  | .little => bytes.foldr (fun byte word => byte.val + 256 * word) 0

def needsSwap (host : Endian) (declared : Declared) (width : Nat) : Bool :=
  decide (1 < width ∧ resolve host declared ≠ host)

def prepare (host : Endian) (declared : Declared) (bytes : List Byte) : List Byte :=
  if needsSwap host declared bytes.length then bytes.reverse else bytes

def read (host : Endian) (declared : Declared) (bytes : List Byte) : Nat :=
  hostLoad host (prepare host declared bytes)

end Native

theorem accumulator_refines_positional (bytes : List Byte) (initial : Nat) :
    bytes.foldl Native.accumulate initial = initial * 256 ^ bytes.length + Reference.positional bytes := by
  induction bytes generalizing initial with
  | nil => simp [Reference.positional]
  | cons byte rest ih =>
      simp only [List.foldl_cons, List.length_cons, Reference.positional, ih, Native.accumulate]
      simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

theorem host_load_refines_positional (host : Endian) (bytes : List Byte) :
    Native.hostLoad host bytes = Reference.word host bytes := by
  cases host with
  | big => simpa [Native.hostLoad, Reference.word] using accumulator_refines_positional bytes 0
  | little =>
      have reversed := accumulator_refines_positional bytes.reverse 0
      simpa [Native.hostLoad, Reference.word, List.foldl_reverse,
        Native.accumulate, Nat.mul_comm, Nat.add_comm] using reversed

theorem reversal_changes_order (order : Endian) (bytes : List Byte) :
    Reference.word order bytes.reverse =
      Reference.word (match order with | .little => .big | .big => .little) bytes := by
  cases order <;> simp [Reference.word]

theorem short_cell_has_no_byte_order (order other : Endian) (bytes : List Byte)
    (short : bytes.length ≤ 1) : Reference.word order bytes = Reference.word other bytes := by
  cases bytes with
  | nil => cases order <;> cases other <;> rfl
  | cons byte rest =>
      have empty : rest = [] := by
        have : rest.length = 0 := by simp only [List.length_cons] at short; omega
        exact List.length_eq_zero_iff.mp this
      subst rest
      cases order <;> cases other <;> rfl

/-- This is a word-reading refinement, not an alias between two readers. -/
theorem semantic_read_refines (host : Endian) (declared : Declared) (bytes : List Byte) :
    Native.read host declared bytes = Reference.word (resolve host declared) bytes := by
  rw [Native.read, host_load_refines_positional]
  by_cases short : bytes.length ≤ 1
  · have noSwap : Native.needsSwap host declared bytes.length = false := by
      simp [Native.needsSwap]
      omega
    rw [Native.prepare, if_neg (by simp [noSwap])]
    exact short_cell_has_no_byte_order _ _ _ short
  · have long : 1 < bytes.length := by omega
    cases host <;> cases declared <;>
      simp [Native.prepare, Native.needsSwap, resolve, long, reversal_changes_order]

theorem positional_fits_byte_width (bytes : List Byte) :
    Reference.positional bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons byte rest ih =>
      have scaled := Nat.mul_le_mul_right (256 ^ rest.length)
        (show byte.val + 1 ≤ 256 by have := byte.isLt; omega)
      simp only [Nat.add_mul, Nat.one_mul] at scaled
      simp only [Reference.positional, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (256 ^ rest.length) 256]
      omega

theorem semantic_word_fits_byte_width (host : Endian) (declared : Declared) (bytes : List Byte) :
    Native.read host declared bytes < 256 ^ bytes.length := by
  rw [semantic_read_refines]
  cases resolve host declared with
  | big => exact positional_fits_byte_width bytes
  | little => simpa [Reference.word] using positional_fits_byte_width bytes.reverse

/-- A packed host reader is justified only after the no-swap admission.
The scalar path remains available for the other declared byte orders. -/
theorem unswapped_packed_read_refines (host : Endian) (declared : Declared) (bytes : List Byte)
    (admitted : Native.needsSwap host declared bytes.length = false) :
    Native.hostLoad host bytes = Reference.word (resolve host declared) bytes := by
  simpa [Native.read, Native.prepare, admitted] using semantic_read_refines host declared bytes

theorem prepared_width_preserved (host : Endian) (declared : Declared) (bytes : List Byte) :
    (Native.prepare host declared bytes).length = bytes.length := by
  unfold Native.prepare
  split <;> simp

theorem double_reversal_restores_physical_bytes (bytes : List Byte) :
    bytes.reverse.reverse = bytes := List.reverse_reverse bytes

def SupportedWidth (width : Nat) : Prop := width = 1 ∨ width = 4 ∨ width = 8

def CoordinateSafe (size start width : Nat) : Prop :=
  start ≤ size ∧ ∀ index : Fin width, start + index.val < size

instance (size start width : Nat) : Decidable (CoordinateSafe size start width) := by
  unfold CoordinateSafe
  infer_instance

theorem cell_bounds_refine (size start width : Nat) :
    CoordinateSafe size start width ↔ start + width ≤ size := by
  constructor
  · rintro ⟨anchor, coordinates⟩
    by_cases empty : width = 0
    · simp [empty, anchor]
    · have last := coordinates ⟨width - 1, by omega⟩
      change start + (width - 1) < size at last
      omega
  · intro bound
    constructor
    · omega
    · intro index
      have := index.isLt
      omega

namespace Reference

def cell (storage : List Byte) (start width : Nat) : Option (List Byte) :=
  if CoordinateSafe storage.length start width then
    some (List.ofFn fun index : Fin width => storage[start + index.val]?.getD 0)
  else none

end Reference

namespace Native

def cell (storage : List Byte) (start width : Nat) : Option (List Byte) :=
  if start + width ≤ storage.length then some ((storage.drop start).take width) else none

end Native

theorem selected_bytes_refine (storage : List Byte) (start width : Nat)
    (bound : start + width ≤ storage.length) :
    (List.ofFn fun index : Fin width => storage[start + index.val]?.getD 0) =
      (storage.drop start).take width := by
  apply List.ext_getElem
  · simp
    omega
  · intro index left right
    have inStorage : start + index < storage.length := by
      have inWidth : index < width := by simpa using left
      omega
    simp [List.getElem_ofFn, List.getElem_take, List.getElem_drop,
      List.getElem?_eq_getElem inStorage]

theorem complete_cell_refines (storage : List Byte) (start width : Nat) :
    Reference.cell storage start width = Native.cell storage start width := by
  by_cases bound : start + width ≤ storage.length
  · have safe := (cell_bounds_refine _ _ _).mpr bound
    simp [Reference.cell, Native.cell, safe, bound, selected_bytes_refine storage start width bound]
  · have outOfBounds : ¬CoordinateSafe storage.length start width := by
      intro safe
      exact bound ((cell_bounds_refine _ _ _).mp safe)
    simp [Reference.cell, Native.cell, outOfBounds, bound]

structure Storage where
  bytes : List Byte
  declared : Declared
  deriving DecidableEq, Repr

def referenceAt (host : Endian) (storage : Storage) (start width : Nat) : Option Nat :=
  (Reference.cell storage.bytes start width).map (Reference.word (resolve host storage.declared))

def nativeAt (host : Endian) (storage : Storage) (start width : Nat) : Option Nat :=
  (Native.cell storage.bytes start width).map (Native.read host storage.declared)

theorem semantic_cell_refines (host : Endian) (storage : Storage) (start width : Nat) :
    nativeAt host storage start width = referenceAt host storage start width := by
  unfold nativeAt referenceAt
  rw [complete_cell_refines]
  cases Native.cell storage.bytes start width with
  | none => rfl
  | some bytes => exact congrArg some (semantic_read_refines host storage.declared bytes)

/-- The stride layer supplies byte starts. Selection keeps their order and
multiplicity, including zero-stride aliases; it does not alter storage order. -/
theorem view_selection_refines (host : Endian) (storage : Storage) (width : Nat) (starts : List Nat) :
    starts.map (fun start => nativeAt host storage start width) =
      starts.map (fun start => referenceAt host storage start width) := by
  apply List.map_congr_left
  intro start _
  exact semantic_cell_refines host storage start width

namespace Controls

def foreign : Storage := ⟨[1, 2, 3, 4, 5, 6, 7, 8], .big⟩

theorem native_declaration_never_swaps (host : Endian) (bytes : List Byte) :
    Native.prepare host .native bytes = bytes := by
  simp [Native.prepare, Native.needsSwap, resolve]

theorem single_byte_orders_agree :
    Native.read .little .big [137] = 137 ∧ Native.read .big .little [137] = 137 := by
  decide

theorem eight_byte_order_is_observed :
    Native.read .little .big [1, 2, 3, 4, 5, 6, 7, 8] = 72623859790382856 ∧
      Native.read .big .little [1, 2, 3, 4, 5, 6, 7, 8] = 578437695752307201 := by
  decide

theorem supported_scalar_widths : SupportedWidth 1 ∧ SupportedWidth 4 ∧ SupportedWidth 8 := by
  simp [SupportedWidth]

theorem ignored_swap_is_observable :
    Native.read .little .big [1, 2, 3, 4] = 16909060 ∧
      Native.hostLoad .little [1, 2, 3, 4] = 67305985 := by
  decide

theorem double_swap_is_observable :
    Native.hostLoad .little (([1, 2, 3, 4] : List Byte).reverse.reverse) = 67305985 ∧
      Reference.word .big [1, 2, 3, 4] = 16909060 := by
  decide

theorem whole_cell_and_empty_anchor_bounds :
    Native.cell [1, 2, 3, 4] 0 4 = some [1, 2, 3, 4] ∧
      Native.cell [1, 2, 3, 4] 1 4 = none ∧
      Native.cell [1, 2, 3, 4] 4 0 = some [] ∧
      Native.cell [1, 2, 3, 4] 5 0 = none := by
  decide

theorem view_keeps_duplicate_and_reversed_addresses :
    [4, 0, 4].map (fun start => nativeAt .little foreign start 4) =
      [some 84281096, some 16909060, some 84281096] := by
  decide

theorem reversal_is_per_cell_not_per_allocation :
    nativeAt .little foreign 0 4 = some 16909060 ∧
      nativeAt .little ⟨foreign.bytes.reverse, .little⟩ 0 4 = some 84281096 := by
  decide

end Controls
end Mettapedia.Algebra.TensorByteOrder
