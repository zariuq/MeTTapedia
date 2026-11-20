import Mettapedia.Machines.TIsa.X86PositiveImmediate
import Mettapedia.Machines.TIsa.X86SubByteImmediate
import Mettapedia.Machines.TIsa.P1Memory

/-!
# Integer bounds behind the native memory-check templates

For every nonnegative signed-32-bit displacement and small access count,
unsigned overflow, subtraction borrow and range comparison agree with the
unbounded relative-access inequality. Under a nonwrapping capability and an
in-region pointer, that inequality is the existing source access predicate.
This is arithmetic correspondence; fetched control flow is proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BoundsArithmetic
open X86RegisterRefinement
abbrev Offset := X86PositiveImmediate.Immediate

theorem relative_add_nat (pointer base : Word) (offset : Offset)
    (noWrap : (pointer - base).toNat + offset.val < 2 ^ 64) :
    (pointer - base + X86PositiveImmediate.immediate64 offset).toNat = (pointer - base).toNat + offset.val := by
  rw [BitVec.toNat_add,X86PositiveImmediate.word_nat,Nat.mod_eq_of_lt noWrap]

theorem remaining_nat (length : Word) (count : Fin 128) (enough : count.val ≤ length.toNat) :
    (length - X86SubByteImmediate.word count).toNat = length.toNat - count.val := by
  have bound : (X86SubByteImmediate.word count).toNat ≤ length.toNat := by
    rw [X86SubByteImmediate.word_nat]
    exact enough
  rw [BitVec.toNat_sub_of_le bound,X86SubByteImmediate.word_nat]

theorem native_guard_iff (base pointer length : Word) (offset : Offset) (count : Fin 128) :
    ((pointer - base).toNat + offset.val < 2 ^ 64 ∧ count.val ≤ length.toNat ∧
      (pointer - base + X86PositiveImmediate.immediate64 offset).toNat ≤
        (length - X86SubByteImmediate.word count).toNat) ↔
      (pointer - base).toNat + offset.val + count.val ≤ length.toNat := by
  constructor
  · rintro ⟨noWrap,enough,inside⟩
    rw [relative_add_nat pointer base offset noWrap,remaining_nat length count enough] at inside
    omega
  · intro inside
    have noWrap : (pointer - base).toNat + offset.val < 2 ^ 64 := by have := length.isLt; omega
    have enough : count.val ≤ length.toNat := by omega
    refine ⟨noWrap,enough,?_⟩
    rw [relative_add_nat pointer base offset noWrap,remaining_nat length count enough]
    omega

theorem offset_toInt (offset : Offset) : (X86PositiveImmediate.immediate32 offset).toInt = (offset.val : Int) := by
  have value : (X86PositiveImmediate.immediate32 offset).toNat = offset.val := by
    simp only [X86PositiveImmediate.immediate32,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := offset.isLt; omega)
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [value]; have := offset.isLt; omega),value]

theorem offset_signExtend (offset : Offset) :
    (X86PositiveImmediate.immediate32 offset).signExtend 64 = BitVec.ofNat 64 offset.val := by
  have natural : (BitVec.ofNat 64 offset.val).toNat = offset.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := offset.isLt;omega)]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide),offset_toInt,BitVec.toInt_eq_toNat_of_lt
    (by rw [natural];have := offset.isLt;omega),natural]

theorem source_guard (base length pointer : Word) (offset : Offset) (count : Fin 128)
    (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (pointerLower : base.toNat ≤ pointer.toNat) (pointerUpper : pointer.toNat ≤ base.toNat + length.toNat) :
    (pointer - base).toNat + offset.val + count.val ≤ length.toNat ↔
      Memory.access? base length pointer (X86PositiveImmediate.immediate32 offset).toInt count.val =
        some (pointer.toNat + offset.val) := by
  have subtract : (pointer - base).toNat = pointer.toNat - base.toNat :=
    BitVec.toNat_sub_of_le (by change base.toNat ≤ pointer.toNat; exact pointerLower)
  rw [subtract,P1Memory.access?_iff_inside base length pointer (X86PositiveImmediate.immediate32 offset)
    count.val (pointer.toNat + offset.val) rangeFits pointerLower pointerUpper,offset_toInt]
  have formed : ((pointer.toNat : Int) + (offset.val : Int)).toNat = pointer.toNat + offset.val := by omega
  simp only [formed,and_true]
  omega

theorem native_source_agree (base length pointer : Word) (offset : Offset) (count : Fin 128)
    (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (pointerLower : base.toNat ≤ pointer.toNat) (pointerUpper : pointer.toNat ≤ base.toNat + length.toNat) :
    ((pointer - base).toNat + offset.val < 2 ^ 64 ∧ count.val ≤ length.toNat ∧
      (pointer - base + X86PositiveImmediate.immediate64 offset).toNat ≤
        (length - X86SubByteImmediate.word count).toNat) ↔
      Memory.access? base length pointer (X86PositiveImmediate.immediate32 offset).toInt count.val =
        some (pointer.toNat + offset.val) :=
  (native_guard_iff base pointer length offset count).trans
    (source_guard base length pointer offset count rangeFits pointerLower pointerUpper)

theorem pointer_inside_of_fits (base length pointer : Word) (offset : Offset) (count : Fin 128)
    (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (fits : (pointer - base).toNat + offset.val + count.val ≤ length.toNat) :
    base.toNat ≤ pointer.toNat ∧ pointer.toNat ≤ base.toNat + length.toNat := by
  have relative : (pointer - base).toNat ≤ length.toNat := by omega
  have lower : base.toNat ≤ pointer.toNat := by
    by_contra outside
    have wrapped := BitVec.toNat_sub_of_lt (x := pointer) (y := base)
      (by rw [BitVec.lt_def];omega)
    rw [wrapped] at relative
    have := base.isLt
    omega
  refine ⟨lower,?_⟩
  rw [BitVec.toNat_sub_of_le (by change base.toNat ≤ pointer.toNat;exact lower)] at relative
  omega

theorem access_of_fits (base length pointer : Word) (offset : Offset) (count : Fin 128)
    (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (fits : (pointer - base).toNat + offset.val + count.val ≤ length.toNat) :
    Memory.access? base length pointer (X86PositiveImmediate.immediate32 offset).toInt count.val =
      some (pointer.toNat + offset.val) := by
  obtain ⟨lower,upper⟩ := pointer_inside_of_fits base length pointer offset count rangeFits fits
  exact (source_guard base length pointer offset count rangeFits lower upper).mp fits

#print axioms native_guard_iff
#print axioms native_source_agree
#print axioms pointer_inside_of_fits
#print axioms access_of_fits

end Mettapedia.Machines.TIsa.X86BoundsArithmetic
