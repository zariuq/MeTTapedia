import Mettapedia.Machines.TIsa.X86Alu

/-!
# Signed interpretation from the original Sail extension helper

The integer bit test identifies the sign bit of every positive-width word.
The original loghead and binary_logext bodies then compute its unsigned
residue and signed integer interpretation without changing architectural state.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86SignExtension
open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

theorem sign_slice (width : Nat) (value : BitVec (width + 1)) :
    Sail.get_slice_int 1 (value.toNat : Int) width = BitVec.ofBool value.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have zero : index = 0 := by omega
  subst index
  simp [Sail.get_slice_int,BitVec.ofInt_natCast,BitVec.msb_eq_getLsbD_last]
  omega

theorem logbit (state : State) (width : Nat) (value : BitVec (width + 1)) :
    (Functions.logbitp_int (width : Int) (value.toNat : Int)).run state = .ok value.msb state := by
  unfold Functions.logbitp_int
  have nonnegative : ((width : Int) ≥b 0) = true := by simp
  rw [nonnegative]
  simp only [run_bind,run_assert,ite_true,Int.toNat_natCast,sign_slice]
  cases value.msb <;> rfl

theorem loghead (width : Nat) (value : Int) :
    Functions.loghead_int (width : Int) value = (BitVec.ofInt width value).toNat := by
  cases width with
  | zero => simp [Functions.loghead_int]
  | succ width =>
    unfold Functions.loghead_int
    have nonzero : ((((width + 1 : Nat) : Int)) == (0 : Int)) = false := by simp; omega
    rw [nonzero]
    simp only [Bool.false_eq_true,ite_false]
    change Sail.BitVec.toNatInt (Functions.bits_of_int value (width + 1)) = _
    rw [X86Alu.bits_of_int_eq]
    rfl

theorem logext (state : State) (width : Nat) (value : BitVec (width + 1)) :
    (Functions.binary_logext ((width + 1 : Nat) : Int) (value.toNat : Int)).run state =
      .ok value.toInt state := by
  unfold Functions.binary_logext
  have positive : ((0 : Int) <b ((width + 1 : Nat) : Int)) = true := by simp
  rw [positive]
  simp only [run_bind,run_assert,ite_true]
  have index : ((width + 1 : Nat) : Int) - 1 = (width : Int) := by omega
  rw [index,logbit state width value]
  have bound : value.toNat < 2 ^ width * 2 := by simpa [Nat.pow_succ] using value.isLt
  cases sign : value.msb with
  | false =>
    simp only [Bool.false_eq_true,ite_false,pure_bind,run_pure]
    unfold Functions.binary_logapp
    rw [loghead]
    have small : value.toNat < 2 ^ width := by
      have h := BitVec.msb_eq_false_iff_two_mul_lt.mp sign
      simp only [Nat.pow_succ] at h
      omega
    simp [BitVec.ofInt_natCast,Nat.mod_eq_of_lt small,
      BitVec.toInt_eq_msb_cond,sign]
  | true =>
    simp only [ite_true,pure_bind,run_pure]
    unfold Functions.binary_logapp
    rw [loghead]
    have large : 2 ^ width ≤ value.toNat := by
      have h := BitVec.msb_eq_true_iff_two_mul_ge.mp sign
      simp only [Nat.pow_succ] at h
      omega
    have rest : value.toNat - 2 ^ width < 2 ^ width := by omega
    simp only [BitVec.ofInt_natCast,BitVec.toNat_ofNat,BitVec.toInt_eq_msb_cond,sign,ite_true]
    rw [Nat.mod_eq_sub_mod large,Nat.mod_eq_of_lt rest]
    congr 1
    change ((value.toNat - 2 ^ width : Nat) : Int) + (-1) * (2 : Int) ^ width = _
    rw [Int.natCast_sub large,Nat.pow_succ]
    push_cast
    omega

#print axioms sign_slice
#print axioms logbit
#print axioms loghead
#print axioms logext
end Mettapedia.Machines.TIsa.X86SignExtension
