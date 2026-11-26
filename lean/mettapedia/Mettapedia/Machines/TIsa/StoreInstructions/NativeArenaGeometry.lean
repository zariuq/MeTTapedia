import Mettapedia.Machines.TIsa.StoreInstructions.WordRegion

/-!
# Slices of contiguous native word arenas

Only a selected record needs to fit a signed displacement. The
whole arena uses a canonical unsigned span and need not fit disp32.
Slices do not allocate or introduce a directory of pointers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeArenaGeometry

open X86CanonicalSpan (Area narrow)
open X86PlacedMemory (footprint)

structure Region (length : ℕ) where
  pointer : Word
  aligned : pointer.toNat % 8 = 0
  area : Area pointer (8 * length)

variable {length : ℕ}

def Region.atWord (region : Region length) (start : ℕ) : Word :=
  region.pointer + BitVec.ofNat 64 (8 * start)

theorem Region.atWord_nat (region : Region length) (start : ℕ) (inside : start < length) :
    (region.atWord start).toNat = region.pointer.toNat + 8 * start :=
  X86CanonicalSpan.add_toNat _ _ (by have outer := region.area.1; omega)

theorem Region.atWord_next (region : Region length) (start offset : ℕ) :
    region.atWord start + BitVec.ofNat 64 (8 * offset) = region.atWord (start + offset) := by
  unfold Region.atWord
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

theorem word_scale8 (index : Word) : BitVec.ofNat 64 (8 * index.toNat) = index * 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  change (8 * index.toNat) % 2 ^ 64 = (index.toNat * 8) % 2 ^ 64
  rw [Nat.mul_comm 8]

theorem Region.positive_room (region : Region length) (positive : 0 < length) :
    8 * length ≤ 2 ^ 47 :=
  X86CanonicalSpan.area_size _ _ (by omega) region.area

def Region.slice (region : Region length) (start width : ℕ) (positive : 0 < width)
    (inside : start + width ≤ length) (short : 8 * width ≤ 2 ^ 31) : WordRegion.Region width where
  pointer := region.atWord start
  aligned := by
    rw [region.atWord_nat start (by omega), Nat.add_mod, region.aligned]
    simp
  area := by
    constructor
    · rw [region.atWord_nat start (by omega)]
      have outer := region.area.1
      omega
    · intro byte present
      have coordinate :
          region.atWord start + BitVec.ofNat 64 byte = region.pointer + BitVec.ofNat 64 (8 * start + byte) := by
        simp only [Region.atWord, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [coordinate]
      exact region.area.2 (8 * start + byte) (by omega)
  shortOffset := short

theorem Region.slice_address (region : Region length) (start width : ℕ)
    (positive : 0 < width) (inside : start + width ≤ length) (short : 8 * width ≤ 2 ^ 31)
    (field : Fin width) :
    ((region.slice start width positive inside short).cell field).address =
      narrow (region.atWord (start + field.val)) := by
  change narrow (region.atWord start + BitVec.ofNat 64 (8 * field.val)) = _
  rw [region.atWord_next start field.val]

theorem Region.slice_base_cell (region : Region length) (start width : ℕ)
    (positive : 0 < width) (inside : start + width ≤ length) (short : 8 * width ≤ 2 ^ 31) :
    ((region.slice start width positive inside short).cell ⟨0, positive⟩).address.signExtend 64 =
      region.atWord start := by
  have position : 8 * start < 8 * length := by omega
  have canonical := region.area.2 (8 * start) position
  rw [slice_address, show (⟨0, positive⟩ : Fin width).val = 0 from rfl, Nat.add_zero]
  exact X86CanonicalSpan.narrow_representation _ canonical

private theorem Region.byte_in_field (region : Region length) (start width : ℕ)
    (positive : 0 < width) (inside : start + width ≤ length) (short : 8 * width ≤ 2 ^ 31)
    (field : Fin width) {key : ℕ}
    (hit : key ∈ footprint ((region.slice start width positive inside short).cell field).address) :
    ∃ byte < 8, key = X86CanonicalSpan.physicalKey
      (region.pointer + BitVec.ofNat 64 (8 * (start + field.val) + byte)) := by
  obtain ⟨byte, entry, keyOf⟩ := List.mem_map.mp (List.mem_toFinset.mp hit)
  have byteBound := List.mem_range.mp entry
  have fieldBound := field.isLt
  have regionPositive : 0 < 8 * length := by omega
  have firstInside : 8 * (start + field.val) < 8 * length := by omega
  have location :=
    X86CanonicalSpan.narrow_offset _ _ _ regionPositive region.area firstInside
  refine ⟨byte, byteBound, keyOf.symm.trans ?_⟩
  rw [region.slice_address start width positive inside short, Region.atWord, location]
  exact X86CanonicalSpan.physicalAddress_nested _ _ _ _ regionPositive region.area (by omega)

theorem Region.slices_disjoint (region : Region length) (left nl right nr : ℕ)
    (leftPos : 0 < nl) (rightPos : 0 < nr) (leftInside : left + nl ≤ length) (rightInside : right + nr ≤ length)
    (leftShort : 8 * nl ≤ 2 ^ 31) (rightShort : 8 * nr ≤ 2 ^ 31) (before : left + nl ≤ right)
    (l : Fin nl) (r : Fin nr) :
    Disjoint (footprint ((region.slice left nl leftPos leftInside leftShort).cell l).address)
      (footprint ((region.slice right nr rightPos rightInside rightShort).cell r).address) := by
  apply Finset.disjoint_left.mpr
  intro key leftHit rightHit
  obtain ⟨a, smallA, hitA⟩ := region.byte_in_field left nl leftPos leftInside leftShort l leftHit
  obtain ⟨b, smallB, hitB⟩ := region.byte_in_field right nr rightPos rightInside rightShort r rightHit
  have leftBound := l.isLt
  have rightBound := r.isLt
  have same := X86CanonicalSpan.physicalKey_injective _ _ (region.area.2 _ (by omega))
    (region.area.2 _ (by omega)) (hitA.symm.trans hitB)
  have sameAddress := congrArg BitVec.toNat same
  have bounds := region.area.1
  rw [X86CanonicalSpan.add_toNat _ _ (by omega), X86CanonicalSpan.add_toNat _ _ (by omega)] at sameAddress
  omega

def Region.wordCell (region : Region length) (slot : Fin length) : WordRegion.Region 1 :=
  region.slice slot.val 1 (by decide) slot.isLt (by decide)

theorem Region.wordCells_disjoint (region : Region length) {i j : Fin length} (different : i ≠ j) :
    Disjoint (footprint (region.wordCell i |>.cell 0).address) (footprint (region.wordCell j |>.cell 0).address) := by
  have distinct : i.val ≠ j.val := fun eq => different (Fin.ext eq)
  rcases lt_or_gt_of_ne distinct with before | after
  · exact region.slices_disjoint i.val 1 j.val 1 (by decide) (by decide) i.isLt j.isLt
      (by decide) (by decide) before 0 0
  · exact (region.slices_disjoint j.val 1 i.val 1 (by decide) (by decide) j.isLt i.isLt
      (by decide) (by decide) after 0 0).symm

/-- Distinct canonical backing arenas have disjoint physical
bytes, even if their signed virtual addresses cross zero. -/
theorem Region.separate_arenas (first : Region length) {other : ℕ} (second : Region other)
    (apart : first.pointer.toNat + 8 * length ≤ second.pointer.toNat ∨
      second.pointer.toNat + 8 * other ≤ first.pointer.toNat)
    (left nl right nr : ℕ)
    (leftPos : 0 < nl) (rightPos : 0 < nr) (leftInside : left + nl ≤ length) (rightInside : right + nr ≤ other)
    (leftShort : 8 * nl ≤ 2 ^ 31) (rightShort : 8 * nr ≤ 2 ^ 31)
    (l : Fin nl) (r : Fin nr) :
    Disjoint (footprint ((first.slice left nl leftPos leftInside leftShort).cell l).address)
      (footprint ((second.slice right nr rightPos rightInside rightShort).cell r).address) := by
  apply Finset.disjoint_left.mpr
  intro key leftHit rightHit
  obtain ⟨a, hbA, hitA⟩ := first.byte_in_field left nl leftPos leftInside leftShort l leftHit
  obtain ⟨b, hbB, hitB⟩ := second.byte_in_field right nr rightPos rightInside rightShort r rightHit
  have boundL := l.isLt
  have boundR := r.isLt
  have same := X86CanonicalSpan.physicalKey_injective _ _ (first.area.2 _ (by omega))
    (second.area.2 _ (by omega)) (hitA.symm.trans hitB)
  have coordinates := congrArg BitVec.toNat same
  have extentL := first.area.1
  have extentR := second.area.1
  rw [X86CanonicalSpan.add_toNat _ _ (by omega), X86CanonicalSpan.add_toNat _ _ (by omega)] at coordinates
  omega

end Mettapedia.Machines.TIsa.StoreInstructions.NativeArenaGeometry
