import Mettapedia.Machines.TIsa.PreparedReciprocal
import Mettapedia.Machines.TIsa.PreparedWordGuards

/-! The emitter's high word from four unsigned 32-bit products. -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedWideProduct

open PreparedReciprocal (crossCarry highProduct high_product_exact)

def low (word : Word) : Word :=
  Shift.rightUnsigned.evaluate (Shift.left.evaluate word 32) 32

def high (word : Word) : Word := Shift.rightUnsigned.evaluate word 32

theorem low_exact (word : Word) : (low word).toNat = word.toNat % 2^32 := by
  simp only [low, Shift.evaluate, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, show (2^64 : Nat) = 2^32 * 2^32 by decide,
    Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ (by decide)]

theorem high_exact (word : Word) : (high word).toNat = word.toNat / 2^32 := by
  simp only [high, Shift.evaluate, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem low_small (word : Word) : (low word).toNat < 2^32 := by
  rw [low_exact]
  exact Nat.mod_lt _ (by decide)

private theorem high_small (word : Word) : (high word).toNat < 2^32 := by
  rw [high_exact, Nat.div_lt_iff_lt_mul (by decide)]
  exact word.isLt

private theorem product_bound (bound left right : Nat) (positive : 0 < bound)
    (leftSmall : left < bound) (rightSmall : right < bound) : left * right < bound * bound :=
  (Nat.mul_le_mul_left left (Nat.le_of_lt rightSmall)).trans_lt
    (Nat.mul_lt_mul_of_pos_right leftSmall positive)

private theorem product_exact {left right : Word}
    (leftSmall : left.toNat < 2^32) (rightSmall : right.toNat < 2^32) :
    (left * right).toNat = left.toNat * right.toNat :=
  BitVec.toNat_mul_of_lt (product_bound _ _ _ (by decide) leftSmall rightSmall)

def mulHigh (left right : Word) : Word :=
  let ll := low left * low right
  let hh := high left * high right
  let lh := low left * high right
  let hl := high left * low right
  let middle := high ll + low lh + low hl
  hh + high lh + high hl + high middle

theorem mul_high_exact (left right : Word) :
    (mulHigh left right).toNat = left.toNat * right.toNat / 2^64 := by
  let ll := (left.toNat % 2^32) * (right.toNat % 2^32)
  let hh := (left.toNat / 2^32) * (right.toNat / 2^32)
  let lh := (left.toNat % 2^32) * (right.toNat / 2^32)
  let hl := (left.toNat / 2^32) * (right.toNat % 2^32)
  let middle := ll / 2^32 + lh % 2^32 + hl % 2^32
  have loBound : ll < 2^64 :=
    product_bound _ _ _ (by decide) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have loHighBound : ll / 2^32 < 2^32 :=
    (Nat.div_lt_iff_lt_mul (by decide)).mpr loBound
  have middleBound : middle < 2^64 := by
    have a := Nat.mod_lt lh (by decide : 0 < 2^32)
    have b := Nat.mod_lt hl (by decide : 0 < 2^32)
    dsimp [middle]
    omega
  have exactHigh : hh + lh / 2^32 + hl / 2^32 + middle / 2^32 =
      left.toNat * right.toNat / 2^64 := by
    have computed := high_product_exact (2^32) left.toNat right.toNat (by decide)
    unfold highProduct crossCarry at computed
    change hh + hl / 2^32 + lh / 2^32 + (ll / 2^32 + hl % 2^32 + lh % 2^32) / 2^32 = _ at computed
    have middleOrder : ll / 2^32 + hl % 2^32 + lh % 2^32 = middle := by
      dsimp [middle]
      omega
    rw [middleOrder, show (2^32 : Nat) * 2^32 = 2^64 by decide] at computed
    rw [← computed]
    omega
  have totalSmall : hh + lh / 2^32 + hl / 2^32 + middle / 2^32 < 2^64 := by
    rw [exactHigh, Nat.div_lt_iff_lt_mul (by decide)]
    exact product_bound _ _ _ (by decide) left.isLt right.isLt
  simp only [mulHigh, BitVec.toNat_add, low_exact, high_exact,
    product_exact (low_small left) (low_small right),
    product_exact (high_small left) (high_small right),
    product_exact (low_small left) (high_small right),
    product_exact (high_small left) (low_small right),
    Nat.mod_add_mod]
  change (hh + lh / 2^32 + hl / 2^32 + (middle % 2^64) / 2^32) % 2^64 = _
  rw [Nat.mod_eq_of_lt middleBound, Nat.mod_eq_of_lt totalSmall, exactHigh]

end Mettapedia.Machines.TIsa.PreparedWideProduct
