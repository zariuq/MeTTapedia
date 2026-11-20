import Mettapedia.Machines.TIsa.Scalar
import Mathlib.Tactic.NormNum

/-!
# Guards emitted for prepared native words

The arithmetic guard computations use the scalar operations of p1. The
addition and subtraction guards detect both signed overflow endpoints. The
multiplication guard checks a sufficient operand range before multiplying.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedWordGuards

/-- The signed range with an inclusive lower endpoint. -/
def Fits (radius value : Int) : Prop := -radius ≤ value ∧ value < radius

instance (radius value : Int) : Decidable (Fits radius value) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem word_fits (word : Word) : Fits (2^63) word.toInt :=
  ⟨BitVec.le_toInt word, BitVec.toInt_lt⟩

/-- The emitter adds a bias and performs an unsigned comparison. -/
def biasedRange (radius : Nat) (word : Word) : Bool :=
  Comparison.lessUnsigned.evaluate
    (Binary.add.evaluate word (.ofNat 64 radius)) (.ofNat 64 (2 * radius))

theorem biased_range_exact (radius : Nat) (word : Word) (small : radius < 2^63) :
    biasedRange radius word = true ↔ Fits (radius : Int) word.toInt := by
  simp only [biasedRange, Binary.evaluate, Comparison.evaluate, decide_eq_true_eq,
    BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat, Fits, BitVec.toInt_eq_toNat_cond]
  norm_num at small ⊢
  have width := word.isLt
  norm_num at width
  have limit : (2 * radius) % 18446744073709551616 = 2 * radius :=
    Nat.mod_eq_of_lt (by omega)
  rw [limit]
  by_cases wraps : word.toNat + radius < 18446744073709551616
  · rw [Nat.mod_eq_of_lt wraps]
    split <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split <;> omega

private theorem signed_reduce (value : Int) (range : Fits (2^64) value) :
    value.bmod (2^64) =
      if value < -(2^63) then value + 2^64
      else if value < 2^63 then value else value - 2^64 := by
  rcases range with ⟨lower, upper⟩
  apply (Int.bmod_eq_iff (by decide)).2
  norm_num at lower upper ⊢
  split
  · refine ⟨by omega, by omega, 1, ?_⟩
    omega
  · split
    · refine ⟨by omega, by omega, 0, ?_⟩
      omega
    · refine ⟨by omega, by omega, -1, ?_⟩
      omega

theorem decode_in_range (value : Int) (range : Fits (2^63) value) :
    (BitVec.ofInt 64 value).toInt = value :=
  BitVec.toInt_ofInt_eq_self (by decide) range.1 range.2

private theorem xor_decide_true (p q : Prop) [Decidable p] [Decidable q] :
    (decide p ^^ decide q) = true ↔ ¬ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The sign bit of the mask the emitter tests after a wrapped addition. -/
def addOverflows (left right : Word) : Bool :=
  let result := Binary.add.evaluate left right
  Comparison.lessSigned.evaluate
    (Binary.band.evaluate (Binary.bxor.evaluate left result) (Binary.bxor.evaluate right result)) 0

/-- The sign bit of the mask the emitter tests after a wrapped subtraction. -/
def subOverflows (left right : Word) : Bool :=
  let result := Binary.sub.evaluate left right
  Comparison.lessSigned.evaluate
    (Binary.band.evaluate (Binary.bxor.evaluate left right) (Binary.bxor.evaluate left result)) 0

theorem add_overflow_exact (left right : Word) :
    addOverflows left right = true ↔ ¬ Fits (2^63) (left.toInt + right.toInt) := by
  obtain ⟨loL, hiL⟩ := word_fits left
  obtain ⟨loR, hiR⟩ := word_fits right
  have range : Fits (2^64) (left.toInt + right.toInt) := by
    unfold Fits
    constructor <;> omega
  simp only [addOverflows, Binary.evaluate, Comparison.evaluate, BitVec.slt_eq_decide,
    show (0 : Word).toInt = 0 by decide, ← BitVec.msb_eq_toInt,
    BitVec.msb_and, BitVec.msb_xor]
  simp only [BitVec.msb_eq_toInt, BitVec.toInt_add, signed_reduce _ range,
    Bool.and_eq_true, xor_decide_true, Fits]
  split <;> (try split) <;> omega

theorem sub_overflow_exact (left right : Word) :
    subOverflows left right = true ↔ ¬ Fits (2^63) (left.toInt - right.toInt) := by
  obtain ⟨loL, hiL⟩ := word_fits left
  obtain ⟨loR, hiR⟩ := word_fits right
  have range : Fits (2^64) (left.toInt - right.toInt) := by
    unfold Fits
    constructor <;> omega
  simp only [subOverflows, Binary.evaluate, Comparison.evaluate, BitVec.slt_eq_decide,
    show (0 : Word).toInt = 0 by decide, ← BitVec.msb_eq_toInt,
    BitVec.msb_and, BitVec.msb_xor]
  simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, signed_reduce _ range,
    Bool.and_eq_true, xor_decide_true, Fits]
  split <;> (try split) <;> omega

def checkedAdd (left right : Word) : Option Word :=
  if addOverflows left right then none else some (Binary.add.evaluate left right)

def checkedSub (left right : Word) : Option Word :=
  if subOverflows left right then none else some (Binary.sub.evaluate left right)

private theorem checked_exact (overflow : Bool) (result : Word) (value : Int)
    (tested : overflow = true ↔ ¬ Fits (2^63) value)
    (wrap : result.toInt = value.bmod (2^64)) :
    (if overflow then none else some result).map BitVec.toInt =
      if Fits (2^63) value then some value else none := by
  by_cases range : Fits (2^63) value
  · have clear : overflow = false := Bool.eq_false_iff.mpr fun h => (tested.mp h) range
    have exactValue := decode_in_range value range
    rw [BitVec.toInt_ofInt] at exactValue
    simp only [clear, Bool.false_eq_true, if_false, if_pos range, Option.map_some, wrap, exactValue]
  · simp only [tested.mpr range, if_true, if_neg range, Option.map_none]

theorem checked_add_exact (left right : Word) :
    (checkedAdd left right).map BitVec.toInt =
      if Fits (2^63) (left.toInt + right.toInt) then some (left.toInt + right.toInt) else none :=
  checked_exact _ _ _ (add_overflow_exact left right) (BitVec.toInt_add left right)

theorem checked_sub_exact (left right : Word) :
    (checkedSub left right).map BitVec.toInt =
      if Fits (2^63) (left.toInt - right.toInt) then some (left.toInt - right.toInt) else none :=
  checked_exact _ _ _ (sub_overflow_exact left right) (BitVec.toInt_sub)

def checkedMul (left right : Word) : Option Word :=
  if biasedRange (2^31) left && biasedRange (2^31) right then
    some (Binary.mulLo.evaluate left right)
  else none

theorem checked_mul_exact (left right : Word) :
    (checkedMul left right).map BitVec.toInt =
      if Fits (2^31) left.toInt ∧ Fits (2^31) right.toInt then
        some (left.toInt * right.toInt)
      else none := by
  have small : (2^31 : Nat) < 2^63 := by decide
  simp only [checkedMul, Bool.and_eq_true, biased_range_exact _ _ small,
    Nat.cast_pow, Nat.cast_ofNat]
  split
  next admitted =>
    obtain ⟨⟨loL, hiL⟩, ⟨loR, hiR⟩⟩ := admitted
    have upper : left.toInt * right.toInt ≤ (2^31 : Int) * 2^31 :=
      Int.mul_le_mul_of_natAbs_le (s := 2147483648) (t := 2147483648) (by omega) (by omega)
    have lower : -((2^31 : Int) * 2^31) ≤ left.toInt * right.toInt :=
      Int.neg_mul_le_mul (s := 2147483648) (t := 2147483648) (by omega) (by omega) (by omega) (by omega)
    have exactValue := decode_in_range (left.toInt * right.toInt) ⟨by omega, by omega⟩
    rw [BitVec.toInt_ofInt] at exactValue
    simpa only [Option.map_some, Binary.evaluate, BitVec.toInt_mul] using congrArg some exactValue
  next => rfl

end Mettapedia.Machines.TIsa.PreparedWordGuards
