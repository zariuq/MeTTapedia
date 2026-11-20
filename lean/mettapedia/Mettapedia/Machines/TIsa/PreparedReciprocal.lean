import Mathlib.Tactic.Ring

/-!
# Invariant-divisor quotient used by the prepared emitter

First establish exact division by a scaled reciprocal over a bounded
numerator. Then factor its quotient into the high-product extraction and
the two shifts used by the emitter for a positive non-power-of-two
divisor. The algebra is independent of word size.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedReciprocal

theorem bounded_scaled_division (base scale divisor numerator : Nat)
    (positive : 0 < divisor) (scaleLarge : divisor ≤ scale) (bounded : numerator < base) :
    numerator * (base * scale / divisor + 1) / (base * scale) = numerator / divisor := by
  let whole := base * scale
  let multiplier := whole / divisor + 1
  let excess := divisor - whole % divisor
  let quotient := numerator / divisor
  have residue := Nat.mod_lt whole positive
  have excessLarge : excess ≤ scale := by
    dsimp [excess]
    omega
  have adjusted : multiplier * divisor = whole + excess := by
    dsimp [multiplier, excess]
    have decomposed := Nat.div_add_mod whole divisor
    rw [Nat.add_mul, Nat.mul_comm (whole / divisor), Nat.one_mul]
    omega
  have floorLower : quotient * divisor ≤ numerator :=
    (Nat.le_div_iff_mul_le positive).mp (Nat.le_refl _)
  have floorUpper : numerator + 1 ≤ (quotient + 1) * divisor :=
    (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_self _)
  have below : quotient * whole ≤ numerator * multiplier := calc
    quotient * whole ≤ quotient * (multiplier * divisor) := by rw [adjusted, Nat.mul_add]; omega
    _ = (quotient * divisor) * multiplier := by ring
    _ ≤ numerator * multiplier := Nat.mul_le_mul_right _ floorLower
  have excessBound : numerator * excess < whole := calc
    numerator * excess ≤ numerator * scale := Nat.mul_le_mul_left _ excessLarge
    _ < base * scale := Nat.mul_lt_mul_of_pos_right bounded (by omega)
  have above : numerator * multiplier * divisor < (quotient + 1) * whole * divisor := calc
    numerator * multiplier * divisor = numerator * (whole + excess) := by
      rw [Nat.mul_assoc, adjusted]
    _ = numerator * whole + numerator * excess := Nat.mul_add _ _ _
    _ < numerator * whole + whole := Nat.add_lt_add_left excessBound _
    _ = (numerator + 1) * whole := by ring
    _ ≤ ((quotient + 1) * divisor) * whole := Nat.mul_le_mul_right _ floorUpper
    _ = (quotient + 1) * whole * divisor := by ring
  exact Nat.div_eq_of_lt_le below (Nat.lt_of_mul_lt_mul_right above)

def multiplier (base scale divisor : Nat) : Nat :=
  base * (scale - divisor) / divisor + 1

theorem multiplier_full (base scale divisor : Nat) (positive : 0 < divisor)
    (belowScale : divisor ≤ scale) :
    base + multiplier base scale divisor = base * scale / divisor + 1 := by
  have sum : scale = scale - divisor + divisor := by omega
  have scaled : base * scale = base * (scale - divisor) + divisor * base := by
    conv_lhs => rw [sum]
    rw [Nat.mul_add, Nat.mul_comm base divisor]
  rw [scaled, Nat.add_mul_div_left _ _ positive]
  unfold multiplier
  omega

theorem multiplier_fits (base half divisor : Nat) (aboveHalf : half < divisor)
    (belowScale : divisor ≤ 2 * half) (belowBase : divisor < base) :
    multiplier base (2 * half) divisor < base := by
  have positive : 0 < divisor := by omega
  have delta : 2 * half - divisor ≤ divisor - 1 := by omega
  have scaled := Nat.mul_le_mul_left base delta
  rw [Nat.mul_sub_left_distrib base divisor 1, Nat.mul_one] at scaled
  have product : base * (2 * half - divisor) < (base - 1) * divisor := by
    rw [Nat.mul_sub_right_distrib, Nat.one_mul]
    have large : base ≤ base * divisor := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left base (show 1 ≤ divisor by omega)
    omega
  have floor := (Nat.div_lt_iff_lt_mul positive).mpr product
  unfold multiplier
  omega

/-- The middle sum, divided by two and then by the remaining scale,
    reconstructs the exact scaled reciprocal quotient. -/
theorem quotient_by_high_product (base half divisor numerator : Nat)
    (aboveHalf : half < divisor)
    (belowScale : divisor ≤ 2 * half) (belowBase : divisor < base)
    (bounded : numerator < base) :
    let high := multiplier base (2 * half) divisor * numerator / base
    (high + (numerator - high) / 2) / half = numerator / divisor := by
  let factor := multiplier base (2 * half) divisor
  let high := factor * numerator / base
  have basePositive : 0 < base := by omega
  have factorSmall := multiplier_fits base half divisor aboveHalf belowScale belowBase
  have highBound : high ≤ numerator := by
    apply Nat.lt_succ_iff.mp
    exact (Nat.div_lt_iff_lt_mul basePositive).mpr (calc
      factor * numerator ≤ base * numerator := Nat.mul_le_mul_right _ (Nat.le_of_lt factorSmall)
      _ < (numerator + 1) * base := by rw [Nat.mul_comm base numerator, Nat.add_mul]; omega)
  have middle : high + (numerator - high) / 2 = (numerator + high) / 2 := by
    conv_rhs => rw [show numerator + high = numerator - high + 2 * high by omega]
    rw [Nat.add_mul_div_left _ _ (by decide)]
    omega
  have reconstruct : (factor * numerator + base * numerator) / base = high + numerator :=
    Nat.add_mul_div_left _ _ basePositive
  change (high + (numerator - high) / 2) / half = _
  calc
    (high + (numerator - high) / 2) / half = (numerator + high) / (2 * half) := by
      rw [middle, Nat.div_div_eq_div_mul]
    _ = ((factor * numerator + base * numerator) / base) / (2 * half) := by
      rw [reconstruct, Nat.add_comm high numerator]
    _ = numerator * (base + factor) / (base * (2 * half)) := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    _ = numerator / divisor := by
      have positive : 0 < divisor := by omega
      rw [show base + factor = base * (2 * half) / divisor + 1 from
        multiplier_full base (2 * half) divisor positive belowScale]
      exact bounded_scaled_division base (2 * half) divisor numerator positive belowScale bounded

def crossCarry (limb left right : Nat) : Nat :=
  let low := (left % limb) * (right % limb)
  let crossA := (left / limb) * (right % limb)
  let crossB := (left % limb) * (right / limb)
  low / limb + crossA % limb + crossB % limb

/-- The high half via four short products. The middle carry keeps the
    low product's high limb and both cross products' low limbs. -/
def highProduct (limb left right : Nat) : Nat :=
  let high := (left / limb) * (right / limb)
  let crossA := (left / limb) * (right % limb)
  let crossB := (left % limb) * (right / limb)
  high + crossA / limb + crossB / limb + crossCarry limb left right / limb

theorem high_product_exact (limb left right : Nat) (positive : 0 < limb) :
    highProduct limb left right = left * right / (limb * limb) := by
  let low := (left % limb) * (right % limb)
  let high := (left / limb) * (right / limb)
  let crossA := (left / limb) * (right % limb)
  let crossB := (left % limb) * (right / limb)
  let middle := crossCarry limb left right
  let remainder := low % limb + limb * (middle % limb)
  have remSmall : remainder < limb * limb := calc
    remainder < limb + limb * (middle % limb) := Nat.add_lt_add_right (Nat.mod_lt _ positive) _
    _ = limb * (middle % limb + 1) := by ring
    _ ≤ limb * limb := Nat.mul_le_mul_left _ (Nat.mod_lt _ positive)
  have lowMiddle : low + limb * (crossA + crossB) =
      limb * (crossA + crossB + low / limb) + low % limb := by
    rw [Nat.mul_add limb (crossA + crossB)]
    have lowSplit := Nat.div_add_mod low limb
    omega
  have middleExact : crossA + crossB + low / limb =
      limb * (crossA / limb) + limb * (crossB / limb) + middle := by
    have leftSplit := Nat.div_add_mod crossA limb
    have rightSplit := Nat.div_add_mod crossB limb
    change crossA + crossB + low / limb =
      limb * (crossA / limb) + limb * (crossB / limb) +
        (low / limb + crossA % limb + crossB % limb)
    omega
  have exactProduct : left * right = highProduct limb left right * (limb * limb) + remainder := calc
    left * right = (limb * (left / limb) + left % limb) *
        (limb * (right / limb) + right % limb) := by rw [Nat.div_add_mod, Nat.div_add_mod]
    _ = high * (limb * limb) + (low + limb * (crossA + crossB)) := by dsimp [high, low, crossA, crossB]; ring
    _ = highProduct limb left right * (limb * limb) + remainder := by
      rw [lowMiddle, middleExact, ← Nat.div_add_mod middle limb]
      change high * (limb * limb) +
          (limb * (limb * (crossA / limb) + limb * (crossB / limb) +
            (limb * (middle / limb) + middle % limb)) + low % limb) =
        (high + crossA / limb + crossB / limb + middle / limb) * (limb * limb) +
          (low % limb + limb * (middle % limb))
      ring
  symm
  apply Nat.div_eq_of_lt_le
  · rw [exactProduct]
    omega
  · rw [exactProduct, Nat.add_mul, Nat.one_mul]
    omega

end Mettapedia.Machines.TIsa.PreparedReciprocal
