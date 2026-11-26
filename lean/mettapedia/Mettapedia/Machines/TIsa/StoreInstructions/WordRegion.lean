import Mettapedia.Machines.TIsa.X86PlacedMemory
import Mettapedia.Machines.TIsa.X86CanonicalSpan

/-! # Bounded qword cells in a canonical memory region -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.WordRegion

open X86PlacedMemory (Cell footprint)
open X86CanonicalSpan (Area narrow physicalKey)

structure Region (length : ℕ) where
  pointer : Word
  aligned : pointer.toNat % 8 = 0
  area : Area pointer (8 * length)
  shortOffset : 8 * length ≤ 2 ^ 31

private theorem displacement_extends {n : ℕ} (small : n < 2 ^ 31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have bound : n < 2 ^ 32 := by omega
  have low : (BitVec.ofNat 32 n).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false low, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

variable {length : ℕ}

def offset (slot : Fin length) : ℕ := 8 * slot.val

private theorem within (slot : Fin length) : offset slot + 8 ≤ 8 * length := by
  have inside := slot.isLt
  unfold offset
  omega

private theorem positive (slot : Fin length) : 0 < 8 * length := by have := slot.isLt; omega

def Region.cell (bank : Region length) (slot : Fin length) :
    Cell bank.pointer (BitVec.ofNat 32 (offset slot)) := by
  have extent := within slot
  have small : offset slot < 2 ^ 31 := by have := bank.shortOffset; omega
  have canonical := bank.area.2 (offset slot) (by omega : offset slot < 8 * length)
  refine ⟨narrow (bank.pointer + BitVec.ofNat 64 (offset slot)), ?_, ?_, ?_⟩
  · rw [displacement_extends small, X86CanonicalSpan.narrow_representation _ canonical]
  · rw [X86CanonicalSpan.narrow_toInt _ canonical,
      X86CanonicalSpan.offset_signed bank.pointer _ _ (positive slot) bank.area (by omega)]
    have upper := X86CanonicalSpan.area_signed_upper bank.pointer _ (positive slot) bank.area
    omega
  · apply X86CanonicalSpan.narrow_aligned _ canonical
    have fits : bank.pointer.toNat + offset slot < 2 ^ 64 := by have := bank.area.1; omega
    rw [X86CanonicalSpan.add_toNat _ _ fits, Nat.add_mod, bank.aligned]
    simp [offset]

private theorem physical_byte (bank : Region length) (slot : Fin length) (b : ℕ) (small : b < 8) :
    X86WriteWords.physicalAddress (bank.cell slot).address b =
      physicalKey (bank.pointer + BitVec.ofNat 64 (offset slot + b)) := by
  have whole := within slot
  change X86WriteWords.physicalAddress (narrow (bank.pointer + BitVec.ofNat 64 (offset slot))) b = _
  rw [X86CanonicalSpan.narrow_offset bank.pointer _ _ (positive slot) bank.area (by omega)]
  exact X86CanonicalSpan.physicalAddress_nested bank.pointer _ _ _ (positive slot) bank.area (by omega)

/-- Once the ordinal is in range, the scaled address is the exact cell address. -/
theorem Region.indexed_cell (bank : Region length) (ordinal : Word) (inside : ordinal.toNat < length) :
    bank.pointer + ordinal * 8 = (bank.cell ⟨ordinal.toNat, inside⟩).address.signExtend 64 := by
  have extent := within (⟨ordinal.toNat, inside⟩ : Fin length)
  have small : offset (⟨ordinal.toNat, inside⟩ : Fin length) < 2 ^ 31 := by have := bank.shortOffset; omega
  rw [← (bank.cell ⟨ordinal.toNat, inside⟩).effective, displacement_extends small]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (ordinal.toNat * 8) % 2 ^ 64 = (8 * ordinal.toNat) % 2 ^ 64
  rw [Nat.mul_comm ordinal.toNat]

private theorem footprint_index (bank : Region length) (slot : Fin length) {byte : ℕ}
    (inside : byte ∈ footprint (bank.cell slot).address) :
    ∃ b < 8, byte = physicalKey (bank.pointer + BitVec.ofNat 64 (offset slot + b)) := by
  obtain ⟨b, mem, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp inside)
  have small := List.mem_range.mp mem
  exact ⟨b, small, equal.symm.trans (physical_byte bank slot b small)⟩

theorem Region.separate_words (bank : Region length) {first second : Fin length} (distinct : first ≠ second) :
    Disjoint (footprint (bank.cell first).address) (footprint (bank.cell second).address) := by
  apply Finset.disjoint_left.mpr
  intro byte hitLeft hitRight
  obtain ⟨a, aSmall, sameA⟩ := footprint_index bank first hitLeft
  obtain ⟨b, bSmall, sameB⟩ := footprint_index bank second hitRight
  have left := within first
  have right := within second
  have same := X86CanonicalSpan.physicalKey_injective _ _ (bank.area.2 _ (by omega)) (bank.area.2 _ (by omega))
    (sameA.symm.trans sameB)
  have idx := congrArg BitVec.toNat same
  have noWrap := bank.area.1
  rw [X86CanonicalSpan.add_toNat _ _ (by omega), X86CanonicalSpan.add_toNat _ _ (by omega)] at idx
  unfold offset at idx
  exact distinct (Fin.ext (by omega))

theorem Region.separate_banks (old : Region length) {nextLength : ℕ} (next : Region nextLength)
    (before : old.pointer.toNat + 8 * length ≤ next.pointer.toNat) (left : Fin length) (right : Fin nextLength) :
    Disjoint (footprint (old.cell left).address) (footprint (next.cell right).address) := by
  apply Finset.disjoint_left.mpr
  intro byte leftByte rightByte
  obtain ⟨a, aSmall, sameA⟩ := footprint_index old left leftByte
  obtain ⟨b, bSmall, sameB⟩ := footprint_index next right rightByte
  have leftExtent := within left
  have rightExtent := within right
  have same := X86CanonicalSpan.physicalKey_injective _ _ (old.area.2 _ (by omega)) (next.area.2 _ (by omega))
    (sameA.symm.trans sameB)
  have physical := congrArg BitVec.toNat same
  have oldEnd := old.area.1
  have nextEnd := next.area.1
  rw [X86CanonicalSpan.add_toNat _ _ (by omega), X86CanonicalSpan.add_toNat _ _ (by omega)] at physical
  omega

end Mettapedia.Machines.TIsa.StoreInstructions.WordRegion
