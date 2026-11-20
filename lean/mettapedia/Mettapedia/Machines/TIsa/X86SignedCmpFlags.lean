import Mettapedia.Machines.TIsa.X86NativeJcc
import Mettapedia.Machines.TIsa.X86Comparison
import Mettapedia.Machines.TIsa.PreparedWordGuards

/-!
# Signed comparisons from the subtraction flags

The widened difference fits in a signed 65-bit word. The low result
sign is corrected by overflow in both directions. This relates JGE
to ordered signed operands even at the two endpoints.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86SignedCmpFlags

open _root_.X86Registers X86RegisterRefinement
open PreparedWordGuards (Fits word_fits)

private theorem result_sign (value : Word) :
    Functions.sf_spec64 value = Functions.bool_to_bits (value.toInt < 0) := by
  have msb : value.msb = decide (value.toInt < 0) := BitVec.msb_eq_toInt
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp only [Functions.sf_spec64, Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.bool_to_bits]
  rw [BitVec.getLsbD_extractLsb']
  change (true && value.getLsbD 63) =
    (match decide (value.toInt < 0) with | true => 1#1 | false => 0#1).getLsbD 0
  rw [Bool.true_and, show value.getLsbD 63 = value.msb from rfl, msb]
  cases decide (value.toInt < 0) <;> rfl

private theorem overflow (state : State) (left right : Word) :
    (Functions.of_spec64 (Functions.bits_of_int (left.toInt - right.toInt) 65)).run state =
      .ok (Functions.bool_to_bits (¬ Fits (2^63) (left.toInt - right.toInt))) state := by
  obtain ⟨leftMin, leftMax⟩ := word_fits left
  obtain ⟨rightMin, rightMax⟩ := word_fits right
  have exactDifference :
      (Functions.bits_of_int (left.toInt - right.toInt) 65).toInt = left.toInt - right.toInt := by
    rw [X86Alu.bits_of_int_eq]
    exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
  unfold Functions.of_spec64 Functions.signed_byte_p_int
  rw [exactDifference]
  simp only [run_bind, run_assert, run_pure, show ((64 : Int) ≥b 0) = true from rfl, if_true]
  have predicate :
      (!(decide (-(2^63 : Int) ≤ left.toInt - right.toInt) &&
        decide (left.toInt - right.toInt < (2^63 : Int)))) =
          decide (¬ Fits (2^63) (left.toInt - right.toInt)) := by
    rw [← Bool.decide_and, ← decide_not]
    rfl
  change EStateM.Result.ok (Functions.bool_to_bits
    (!(decide (-(2^63 : Int) ≤ left.toInt - right.toInt) &&
      decide (left.toInt - right.toInt < (2^63 : Int))))) state = _
  exact congrArg (fun value => EStateM.Result.ok (Functions.bool_to_bits value) state) predicate

private theorem sign_and_overflow (state : State) (left right : Word) (incoming outgoing : BitVec 32)
    (computed : (Functions.gpr_sub_spec_8 left right incoming).run state =
      .ok (left - right, outgoing, 0#32) state) :
    Functions._get_rflagsbits_sf (X86Flags.mergeFlags incoming outgoing) = Functions.sf_spec64 (left - right) ∧
    Functions._get_rflagsbits_of (X86Flags.mergeFlags incoming outgoing) =
      Functions.bool_to_bits (¬ Fits (2^63) (left.toInt - right.toInt)) := by
  let observe := fun value : Word × BitVec 32 × BitVec 32 =>
    (Functions._get_rflagsbits_sf (X86Flags.mergeFlags incoming value.2.1),
     Functions._get_rflagsbits_of (X86Flags.mergeFlags incoming value.2.1))
  have projected : (observe <$> Functions.gpr_sub_spec_8 left right incoming).run state =
      .ok (observe (left - right, outgoing, 0#32)) state := by
    rw [map_eq_pure_bind, run_bind, computed]
    rfl
  unfold Functions.gpr_sub_spec_8 at projected
  simp only [map_eq_pure_bind, run_bind, run_pure, overflow, X86Alu.sub_result] at projected
  unfold Functions.pf_spec64 Functions.logbitp_int at projected
  simp only [run_bind, run_assert, run_pure, show ((0 : Int) ≥b 0) = true from rfl, if_true] at projected
  have bits := (EStateM.Result.ok.inj projected).1.symm
  dsimp only [observe] at bits
  obtain ⟨bitsSF, bitsOF⟩ := Prod.mk.inj bits
  constructor
  · rw [bitsSF]
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    have : index = 0 := by omega
    subst index
    simp [X86Flags.mergeFlags, Functions._get_rflagsbits_sf, Functions._get_rflagsbits_of,
      Functions._get_rflagsbits_cf, Functions._get_rflagsbits_pf, Functions._get_rflagsbits_zf,
      Functions._get_rflagsbits_af, Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
      Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf, Functions._update_rflagsbits_zf,
      Functions._update_rflagsbits_af, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  · rw [bitsOF]
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    have : index = 0 := by omega
    subst index
    simp [X86Flags.mergeFlags, Functions._get_rflagsbits_sf, Functions._get_rflagsbits_of,
      Functions._get_rflagsbits_cf, Functions._get_rflagsbits_pf, Functions._get_rflagsbits_zf,
      Functions._get_rflagsbits_af, Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
      Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf, Functions._update_rflagsbits_zf,
      Functions._update_rflagsbits_af, Sail.BitVec.extractLsb, BitVec.extractLsb,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

theorem signed_gate (state : State) (left right : Word) (incoming outgoing : BitVec 32)
    (computed : (Functions.gpr_sub_spec_8 left right incoming).run state =
      .ok (left - right, outgoing, 0#32) state) :
    X86NativeJcc.selects .signedGE (X86Flags.mergeFlags incoming outgoing) =
      decide (right.toInt ≤ left.toInt) := by
  obtain ⟨sign, carry⟩ := sign_and_overflow state left right incoming outgoing computed
  simp only [X86NativeJcc.selects, sign, carry, result_sign]
  let gap := left.toInt - right.toInt
  have encoded : left - right = BitVec.ofInt 64 gap := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sub, BitVec.toInt_ofInt]
  obtain ⟨leftMin, leftMax⟩ := word_fits left
  obtain ⟨rightMin, rightMax⟩ := word_fits right
  have boundary : right.toInt ≤ left.toInt ↔ 0 ≤ gap := by change _ ↔ 0 ≤ left.toInt - right.toInt; omega
  simp only [encoded, boundary]
  change ((Functions.bool_to_bits ((BitVec.ofInt 64 gap).toInt < 0)) ==
    (Functions.bool_to_bits (¬ Fits (2^63) gap))) = decide (0 ≤ gap)
  by_cases low : gap < -(2^63 : Int)
  · have high := (show -(2^64 : Int) ≤ gap by change -(2^64 : Int) ≤ left.toInt - right.toInt; omega)
    have above : ¬ 0 ≤ gap := by omega
    have out : ¬ Fits (2^63) gap := fun range => by have := range.1; omega
    have wrap : BitVec.ofInt 64 gap = BitVec.ofInt 64 (gap + 2^64) := by
      rw [BitVec.ofInt_add, show BitVec.ofInt 64 (2^64 : Int) = 0#64 by decide +kernel, BitVec.add_zero]
    have signedEq : (BitVec.ofInt 64 gap).toInt = gap + 2^64 := by
      rw [wrap]
      exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
    rw [signedEq, decide_eq_false (show ¬ gap + (2^64 : Int) < 0 by omega),
      decide_eq_true out, decide_eq_false above]
    rfl
  · by_cases high : (2^63 : Int) ≤ gap
    · have upper := (show gap < (2^64 : Int) by change left.toInt - right.toInt < (2^64 : Int); omega)
      have out : ¬ Fits (2^63) gap := fun range => by have := range.2; omega
      have wrap : BitVec.ofInt 64 gap = BitVec.ofInt 64 (gap - 2^64) := by
        rw [Int.sub_eq_add_neg, BitVec.ofInt_add,
          show BitVec.ofInt 64 (-(2^64 : Int)) = 0#64 by decide +kernel, BitVec.add_zero]
      have signedEq : (BitVec.ofInt 64 gap).toInt = gap - 2^64 := by
        rw [wrap]
        exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)
      rw [signedEq, decide_eq_true (show gap - (2^64 : Int) < 0 by omega),
        decide_eq_true out, decide_eq_true (show 0 ≤ gap by omega)]
      rfl
    · have bounds : Fits (2^63) gap := ⟨by omega, by omega⟩
      have signedEq : (BitVec.ofInt 64 gap).toInt = gap :=
        BitVec.toInt_ofInt_eq_self (by decide) bounds.1 bounds.2
      by_cases negative : gap < 0
      · rw [signedEq, decide_eq_true negative, decide_eq_false (not_not_intro bounds),
          decide_eq_false (show ¬ 0 ≤ gap by omega)]
        rfl
      · rw [signedEq, decide_eq_false negative, decide_eq_false (not_not_intro bounds),
          decide_eq_true (show 0 ≤ gap by omega)]
        rfl

end Mettapedia.Machines.TIsa.X86SignedCmpFlags
