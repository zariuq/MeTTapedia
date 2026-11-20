import Mettapedia.Machines.TIsa.PreparedWideProduct

/-!
# Unsigned magnitude remainder for a literal divisor

The exponent of the highest set bit identifies the power-of-two mask.
The other branch uses the reciprocal, the high product, and the two
shifts. All the intermediate word arithmetic in the quotient and in the
final product and subtraction is justified by explicit bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedLiteralRemainder

open PreparedReciprocal (multiplier multiplier_fits quotient_by_high_product)
open PreparedWideProduct (mulHigh mul_high_exact)

private theorem log_upper (n : Nat) (positive : 0 < n) : n < 2 * 2^n.log2 := by
  have upper := (Nat.log2_lt (Nat.ne_of_gt positive)).mp (Nat.lt_succ_self n.log2)
  rw [Nat.pow_succ, Nat.mul_comm] at upper
  exact upper

private theorem upper_bit (value exponent : Nat)
    (lower : 2^exponent ≤ value) (upper : value < 2 * 2^exponent) :
    Nat.testBit value exponent = true := by
  have divide : value / 2^exponent = 1 := Nat.div_eq_of_lt_le (by simpa only [Nat.one_mul])
    (by simpa only [Nat.one_add, Nat.reduceAdd])
  rw [Nat.testBit_eq_decide_div_mod_eq, divide]
  decide

theorem power_test_exact (divisor : Nat) (positive : 0 < divisor) :
    divisor &&& (divisor - 1) = 0 ↔ divisor = 2^divisor.log2 := by
  have lower := Nat.log2_self_le (Nat.ne_of_gt positive)
  have upper := log_upper divisor positive
  constructor
  · intro zero
    by_contra different
    have left := upper_bit divisor divisor.log2 lower upper
    have right := upper_bit (divisor - 1) divisor.log2 (by omega) (by omega)
    have observed := congrArg (fun value => Nat.testBit value divisor.log2) zero
    rw [Nat.testBit_and, left, right] at observed
    simp at observed
  · intro power
    conv_lhs => rw [power]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]

theorem shift_for_reciprocal (divisor : Nat) (positive : 0 < divisor)
    (noMask : divisor &&& (divisor - 1) ≠ 0) :
    let half := 2^(divisor - 1).log2
    half < divisor ∧ divisor ≤ 2 * half := by
  have nonPower : divisor ≠ 2^divisor.log2 := fun same =>
    noMask ((power_test_exact divisor positive).mpr same)
  have isStrict : 2^divisor.log2 < divisor := by
    have lower := Nat.log2_self_le (Nat.ne_of_gt positive)
    omega
  have largerThanOne : 1 < divisor := by
    have powerPos := Nat.two_pow_pos divisor.log2
    omega
  change 2^(divisor - 1).log2 < divisor ∧ divisor ≤ 2*2^(divisor - 1).log2
  have lowerPred := Nat.log2_self_le (show divisor - 1 ≠ 0 by omega)
  have upperPred := log_upper (divisor - 1) (by omega)
  exact ⟨by omega, by omega⟩

theorem shift_fits_p1 (divisor : Word) : (divisor.toNat - 1).log2 < 64 := by
  by_cases zero : divisor.toNat - 1 = 0
  · simp [zero, Nat.log2_zero]
  · apply (Nat.log2_lt zero).mpr
    have bounded := divisor.isLt
    omega

def mask (exponent : Nat) (numerator : Word) : Word :=
  Binary.band.evaluate numerator (.ofNat 64 (2^exponent - 1))

theorem mask_exact (exponent : Nat) (numerator : Word) (within : exponent ≤ 64) :
    (mask exponent numerator).toNat = numerator.toNat % 2^exponent := by
  have fits : 2^exponent - 1 < 2^64 := by
    have order := Nat.pow_le_pow_right (by decide : 0 < 2) within
    omega
  simp only [mask, Binary.evaluate, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
    Nat.and_two_pow_sub_one_eq_mod]

def quotient (shift : Nat) (divisor numerator : Word) : Word :=
  let factor := BitVec.ofNat 64 (multiplier (2^64) (2 * 2^shift) divisor.toNat)
  let high := mulHigh factor numerator
  (high + ((numerator - high) >>> 1)) >>> shift

theorem quotient_exact (shift : Nat) (divisor numerator : Word)
    (lower : 2^shift < divisor.toNat) (upper : divisor.toNat ≤ 2 * 2^shift) :
    (quotient shift divisor numerator).toNat = numerator.toNat / divisor.toNat := by
  let factorNat := multiplier (2^64) (2 * 2^shift) divisor.toNat
  let factor := BitVec.ofNat 64 factorNat
  let high := mulHigh factor numerator
  have factorSmall : factorNat < 2^64 :=
    multiplier_fits (2^64) (2^shift) divisor.toNat lower upper divisor.isLt
  have factorNatExact : factor.toNat = factorNat := by
    simp only [factor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt factorSmall]
  have highExact : high.toNat = factorNat * numerator.toNat / 2^64 := by
    rw [mul_high_exact, factorNatExact]
  have highBound : high.toNat ≤ numerator.toNat := by
    apply Nat.lt_succ_iff.mp
    rw [highExact, Nat.div_lt_iff_lt_mul (by decide)]
    calc
      factorNat * numerator.toNat ≤ 2^64 * numerator.toNat :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt factorSmall)
      _ < (numerator.toNat + 1) * 2^64 := by
        rw [Nat.mul_comm (2^64) numerator.toNat, Nat.add_mul]
        omega
  have subtraction : (numerator - high).toNat = numerator.toNat - high.toNat :=
    BitVec.toNat_sub_of_le highBound
  have sumSmall : high.toNat + ((numerator - high) >>> 1).toNat < 2^64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, subtraction]
    have limit := numerator.isLt
    omega
  change ((high + ((numerator - high) >>> 1)) >>> shift).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add_of_lt sumSmall,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, subtraction, highExact]
  exact quotient_by_high_product (2^64) (2^shift) divisor.toNat numerator.toNat
    lower upper divisor.isLt numerator.isLt

def reciprocal (shift : Nat) (divisor numerator : Word) : Word :=
  numerator - quotient shift divisor numerator * divisor

theorem reciprocal_exact (shift : Nat) (divisor numerator : Word)
    (lower : 2^shift < divisor.toNat) (upper : divisor.toNat ≤ 2 * 2^shift) :
    (reciprocal shift divisor numerator).toNat = numerator.toNat % divisor.toNat := by
  let q := quotient shift divisor numerator
  have divide := quotient_exact shift divisor numerator lower upper
  have productSmall : q.toNat * divisor.toNat ≤ numerator.toNat := by
    dsimp [q]
    rw [divide]
    exact (Nat.le_div_iff_mul_le (by omega)).mp (Nat.le_refl _)
  have productWord := BitVec.toNat_mul_of_lt (productSmall.trans_lt numerator.isLt)
  have safeSubtract : q * divisor ≤ numerator := by
    change (q * divisor).toNat ≤ numerator.toNat
    rwa [productWord]
  change (numerator - q * divisor).toNat = _
  rw [BitVec.toNat_sub_of_le safeSubtract, productWord]
  dsimp [q]
  rw [divide, Nat.mul_comm]
  have identity := Nat.div_add_mod numerator.toNat divisor.toNat
  omega

def remainder (divisor numerator : Word) : Option Word :=
  let d := divisor.toNat
  if d = 0 then none
  else if d &&& (d - 1) = 0 then some (mask d.log2 numerator)
  else some (reciprocal (d - 1).log2 divisor numerator)

theorem remainder_exact (divisor numerator : Word) :
    (remainder divisor numerator).map BitVec.toNat =
      if divisor.toNat = 0 then none else some (numerator.toNat % divisor.toNat) := by
  have small := divisor.isLt
  unfold remainder
  split
  · simp_all
  · rename_i nonzero
    have positive : 0 < divisor.toNat := Nat.pos_of_ne_zero nonzero
    rw [if_neg nonzero]
    split
    · rename_i masked
      have shape := (power_test_exact divisor.toNat positive).mp masked
      have bits : divisor.toNat.log2 ≤ 64 := by
        have stricter := (Nat.log2_lt nonzero).mpr small
        omega
      simp only [Option.map_some, mask_exact _ _ bits]
      rw [← shape]
    · rename_i reciprocalCase
      obtain ⟨lower, upper⟩ := shift_for_reciprocal divisor.toNat positive reciprocalCase
      simp only [Option.map_some, reciprocal_exact _ _ _ lower upper]

end Mettapedia.Machines.TIsa.PreparedLiteralRemainder
