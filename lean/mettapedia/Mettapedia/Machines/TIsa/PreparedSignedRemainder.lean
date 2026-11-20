import Mettapedia.Machines.TIsa.PreparedLiteralRemainder

/-!
# Signed and floor remainder of a prepared literal divisor

The absolute value is an unsigned word, including the magnitude of the
lowest signed input. The truncating remainder uses the dividend's sign.
Floor remainder adds the divisor exactly when a nonzero truncating
remainder has the opposite sign. A zero divisor declines.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedSignedRemainder

open PreparedWordGuards (Fits word_fits decode_in_range)

def conditionalNegate (flag : Bool) (word : Word) : Word :=
  if flag then Binary.sub.evaluate 0 word else word

def magnitude (word : Word) : Word :=
  conditionalNegate (Comparison.lessSigned.evaluate word 0) word

theorem magnitude_exact (word : Word) : (magnitude word).toNat = word.toInt.natAbs := by
  unfold magnitude conditionalNegate
  simp only [Comparison.evaluate, BitVec.slt_eq_decide, show (0 : Word).toInt = 0 by decide,
    decide_eq_true_eq, Binary.evaluate]
  by_cases negative : word.toInt < 0
  · rw [if_pos negative]
    have lower := BitVec.toInt_neg_iff.mp negative
    have positive : (0#64) < word := by
      change 0 < word.toNat
      omega
    change ((0#64) - word).toNat = word.toInt.natAbs
    rw [BitVec.zero_sub, BitVec.toNat_neg_of_pos positive]
    have signed : word.toInt = (word.toNat : Int) - (2^64 : Nat) := by
      rw [BitVec.toInt_eq_toNat_cond, if_neg (by omega)]
    rw [signed]
    omega
  · rw [if_neg negative]
    have upper : 2 * word.toNat < 2^64 := by
      have outside := mt BitVec.toInt_neg_iff.mpr negative
      omega
    rw [BitVec.toInt_eq_toNat_of_lt upper]
    rfl

private theorem abs_fits (word : Word) : word.toInt.natAbs ≤ 2^63 := by
  obtain ⟨lower, upper⟩ := word_fits word
  omega

private theorem restore_magnitude (dividend divisor remainder : Word)
    (nonzero : divisor.toInt ≠ 0)
    (exactRemainder : remainder.toNat = dividend.toInt.natAbs % divisor.toInt.natAbs) :
    (conditionalNegate (Comparison.lessSigned.evaluate dividend 0) remainder).toInt =
      dividend.toInt.tmod divisor.toInt := by
  have dPos : 0 < divisor.toInt.natAbs := by omega
  have rSmall : remainder.toNat < 2^63 := by
    have bounded := Nat.mod_lt dividend.toInt.natAbs dPos
    have divisorSmall := abs_fits divisor
    omega
  have signed : remainder.toInt = (remainder.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have negated : ((0 : Word) - remainder).toInt = -(remainder.toNat : Int) := by
    rw [BitVec.toInt_sub, show (0 : Word).toInt = 0 by decide, signed, Int.zero_sub]
    have exactValue := decode_in_range (-(remainder.toNat : Int)) ⟨by omega, by omega⟩
    simpa only [BitVec.toInt_ofInt] using exactValue
  have fromAbs (a b : Int) :
      (if a < 0 then -(↑(a.natAbs % b.natAbs) : Int) else ↑(a.natAbs % b.natAbs)) = a.tmod b := by
    cases a <;> cases b <;> simp [Int.tmod]
  unfold conditionalNegate
  simp only [Comparison.evaluate, Binary.evaluate, BitVec.slt_eq_decide,
    show (0 : Word).toInt = 0 by decide, decide_eq_true_eq]
  by_cases negative : dividend.toInt < 0
  · rw [if_pos negative, negated, exactRemainder]
    simpa only [if_pos negative] using fromAbs dividend.toInt divisor.toInt
  · rw [if_neg negative, signed, exactRemainder]
    simpa only [if_neg negative] using fromAbs dividend.toInt divisor.toInt

def floorAdjustment (remainder divisor : Word) : Bool :=
  Comparison.notEqual.evaluate remainder 0 &&
    Comparison.lessSigned.evaluate (Binary.bxor.evaluate remainder divisor) 0

theorem floor_adjustment_exact (remainder divisor : Word) :
    floorAdjustment remainder divisor = true ↔
      remainder.toInt ≠ 0 ∧ ¬(remainder.toInt < 0 ↔ divisor.toInt < 0) := by
  have interop : (remainder != (0 : Word)) = true ↔ remainder.toInt ≠ 0 := by
    simp [bne_eq, ← BitVec.toInt_inj]
  simp only [floorAdjustment, Comparison.evaluate, Bool.and_eq_true, interop, Binary.evaluate,
    BitVec.slt_eq_decide, show (0 : Word).toInt = 0 by decide, ← BitVec.msb_eq_toInt,
    BitVec.msb_xor]
  simp only [BitVec.msb_eq_toInt]
  by_cases left : remainder.toInt < 0 <;> by_cases right : divisor.toInt < 0 <;> simp [left, right]

private theorem floor_from_truncating (a d : Int) :
    let r := a.tmod d
    (if r ≠ 0 ∧ ¬(r < 0 ↔ d < 0) then r + d else r) = a.fmod d := by
  dsimp
  by_cases divides : d ∣ a
  · have zero := Int.tmod_eq_zero_of_dvd divides
    simp [Int.fmod_eq_tmod, divides, zero]
  · have nonzero : a.tmod d ≠ 0 := mt Int.dvd_iff_tmod_eq_zero.mpr divides
    have signMatches : a.tmod d < 0 ↔ a < 0 := by
      rw [← Int.sign_eq_neg_one_iff_neg, Int.sign_tmod, if_neg divides,
        Int.sign_eq_neg_one_iff_neg]
    by_cases nonnegA : 0 ≤ a <;> by_cases nonnegD : 0 ≤ d <;>
      have trA : (a < 0) = (¬ 0 ≤ a) := propext (by omega) <;>
      have trD : (d < 0) = (¬ 0 ≤ d) := propext (by omega) <;>
      simp only [nonzero, true_and, signMatches, trA, trD, nonnegA, nonnegD,
        not_true_eq_false, not_false_eq_true, iff_self, iff_true, iff_false, if_true, if_false,
        Int.fmod_eq_tmod, if_neg divides, Int.add_zero]
    · rw [Int.ofNat_natAbs_of_nonneg nonnegD]
    · have zero : d.toNat = 0 := by omega
      simp [zero]

private theorem floor_fits (dividend divisor : Word) (nonzero : divisor.toInt ≠ 0) :
    Fits (2^63) (dividend.toInt.fmod divisor.toInt) := by
  obtain ⟨lo, hi⟩ := word_fits divisor
  by_cases positive : 0 < divisor.toInt
  · have lower := Int.fmod_nonneg_of_pos dividend.toInt positive
    have upper := Int.fmod_lt_of_pos dividend.toInt positive
    exact ⟨by omega, by omega⟩
  · have negated : 0 < -divisor.toInt := by omega
    have lower := Int.fmod_nonneg_of_pos (-dividend.toInt) negated
    have upper := Int.fmod_lt_of_pos (-dividend.toInt) negated
    rw [Int.neg_fmod_neg] at lower upper
    exact ⟨by omega, by omega⟩

def remainder (flooring : Bool) (dividend divisor : Word) : Option Word := do
  let absolute ← PreparedLiteralRemainder.remainder (magnitude divisor) (magnitude dividend)
  let truncated := conditionalNegate (Comparison.lessSigned.evaluate dividend 0) absolute
  if flooring && floorAdjustment truncated divisor then
    return Binary.add.evaluate truncated divisor
  else
    return truncated

theorem remainder_exact (flooring : Bool) (dividend divisor : Word) :
    (remainder flooring dividend divisor).map BitVec.toInt =
      if divisor.toInt = 0 then none else
        some (if flooring then dividend.toInt.fmod divisor.toInt else dividend.toInt.tmod divisor.toInt) := by
  have absolute := PreparedLiteralRemainder.remainder_exact (magnitude divisor) (magnitude dividend)
  rw [magnitude_exact divisor, magnitude_exact dividend] at absolute
  unfold remainder
  by_cases zero : divisor.toInt = 0
  · rw [if_pos zero]
    simp only [zero, Int.natAbs_zero, if_true] at absolute
    cases done : PreparedLiteralRemainder.remainder (magnitude divisor) (magnitude dividend) with
    | none => rfl
    | some word => simp [done] at absolute
  · have natNonzero : divisor.toInt.natAbs ≠ 0 := by omega
    rw [if_neg zero]
    rw [if_neg natNonzero] at absolute
    cases done : PreparedLiteralRemainder.remainder (magnitude divisor) (magnitude dividend) with
    | none => simp [done] at absolute
    | some word =>
      have magExact : word.toNat = dividend.toInt.natAbs % divisor.toInt.natAbs := by
        simpa [done] using absolute
      let truncated := conditionalNegate (Comparison.lessSigned.evaluate dividend 0) word
      have decoded : truncated.toInt = dividend.toInt.tmod divisor.toInt :=
        restore_magnitude dividend divisor word zero magExact
      change (if flooring && floorAdjustment truncated divisor then some (truncated + divisor)
        else some truncated).map BitVec.toInt = _
      cases flooring
      · simp only [Bool.false_and, Bool.false_eq_true, if_false, Option.map_some, decoded]
      · simp only [Bool.true_and, if_true, floor_adjustment_exact, decoded]
        have math := floor_from_truncating dividend.toInt divisor.toInt
        dsimp at math
        split
        next adjust =>
          have result : dividend.toInt.tmod divisor.toInt + divisor.toInt =
              dividend.toInt.fmod divisor.toInt := by simpa only [if_pos adjust] using math
          have inRange := decode_in_range _ (floor_fits dividend divisor zero)
          simp only [Option.map_some, BitVec.toInt_add, decoded, result, Option.some.injEq]
          simpa only [BitVec.toInt_ofInt] using inRange
        next noAdjustment =>
          simp only [Option.map_some, decoded]
          exact congrArg some (by simpa only [if_neg noAdjustment] using math)

end Mettapedia.Machines.TIsa.PreparedSignedRemainder
