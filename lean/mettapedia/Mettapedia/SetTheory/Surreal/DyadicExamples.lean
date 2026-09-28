import Mettapedia.SetTheory.Surreal.DyadicEmbedding

/-!
# Computed examples through the dyadic interpretation

Each example below is computed on the **executable** side — arithmetic and
comparison of dyadic rationals, which reduce — and then transported through
`toSurreal`. Because the transport theorems are equivalences, a computed
dyadic fact and the corresponding surreal fact stand or fall together; that is
what makes these checks rather than illustrations.

The general statements are in `DyadicEmbedding.lean`. What is here is the
evidence that they are not vacuous: values on both sides of zero, halves,
cancellation, two spellings of one number, and controls that reject the
statements that ought to be rejected.

## Why rejection controls

Every theorem here has the shape "the interpretation agrees with the
computation". A map that sent everything to `0` would satisfy the preservation
half of that and fail the reflection half. The controls exercise the
reflection half: distinct dyadics must have distinct images, and a comparison
that is false on the executable side must be false in the surreals.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

namespace DyadicExamples

open Algebra.Order

/-! ## Halves -/

/-- `1/2` is the first rung of the ladder. -/
theorem toSurreal_half : toSurreal (Dyadic.ofPair 1 1) = ladder 1 := by
  rw [toSurreal_ofPair, ofPairSurreal, one_zsmul]

/-- `1/4` is the second. -/
theorem toSurreal_quarter : toSurreal (Dyadic.ofPair 1 2) = ladder 2 := by
  rw [toSurreal_ofPair, ofPairSurreal, one_zsmul]

/-- **Computed**: `1/2 + 1/2 = 1` on the executable side. -/
theorem half_add_half_dyadic :
    Dyadic.ofPair 1 1 + Dyadic.ofPair 1 1 = 1 := by
  refine Dyadic.ext ?_
  simp only [Dyadic.val_add, Dyadic.val_ofPair, Dyadic.val_one]
  norm_num

/-- **And transported**: so `1/2 + 1/2 = 1` holds of the surreals, obtained
from the computation rather than from a separate surreal argument. -/
theorem half_add_half_surreal : ladder 1 + ladder 1 = ofNat 1 := by
  have h := congrArg toSurreal half_add_half_dyadic
  rw [toSurreal_add, toSurreal_half, toSurreal_one] at h
  exact h

/-- **Computed**: `1/4 + 1/4 = 1/2`, and transported. -/
theorem quarter_add_quarter_surreal : ladder 2 + ladder 2 = ladder 1 := by
  have hd : Dyadic.ofPair 1 2 + Dyadic.ofPair 1 2 = Dyadic.ofPair 1 1 := by
    refine Dyadic.ext ?_
    simp only [Dyadic.val_add, Dyadic.val_ofPair]
    norm_num
  have h := congrArg toSurreal hd
  rw [toSurreal_add, toSurreal_quarter, toSurreal_half] at h
  exact h

/-! ## Negative values -/

/-- `-3/4` lands below zero, and the interpretation says so. -/
theorem neg_three_quarters_neg :
    toSurreal (Dyadic.ofPair (-3) 2) < 0 := by
  have h : Dyadic.ofPair (-3) 2 < 0 := by
    simp only [Dyadic.lt_iff, Dyadic.val_ofPair, Dyadic.val_zero]
    norm_num
  have := toSurreal_lt_iff.mpr h
  rwa [toSurreal_zero] at this

/-- Negation commutes with the interpretation at a value with a genuine
fractional part. -/
theorem toSurreal_neg_three_quarters :
    toSurreal (-Dyadic.ofPair 3 2) = -(toSurreal (Dyadic.ofPair 3 2)) :=
  toSurreal_neg _

/-- A negative and a positive dyadic compare the right way round. -/
theorem neg_lt_pos :
    toSurreal (Dyadic.ofPair (-3) 2) < toSurreal (Dyadic.ofPair 1 1) := by
  refine toSurreal_lt_iff.mpr ?_
  simp only [Dyadic.lt_iff, Dyadic.val_ofPair]
  norm_num

/-! ## Two spellings of one number -/

/-- `3/4` and `6/8` are the same dyadic — no normalization step is involved,
because the pair is a view and not the representation. -/
theorem three_quarters_two_ways : Dyadic.ofPair 3 2 = Dyadic.ofPair 6 3 := by
  refine Dyadic.ext ?_
  simp only [Dyadic.val_ofPair]
  norm_num

/-- **So they have the same image**, which is well-definedness exercised on a
concrete pair rather than asserted. -/
theorem three_quarters_same_surreal :
    ofPairSurreal 3 2 = ofPairSurreal 6 3 :=
  ofPairSurreal_congr (by norm_num)

/-- And at the level of the map on dyadics. -/
theorem three_quarters_same_image :
    toSurreal (Dyadic.ofPair 3 2) = toSurreal (Dyadic.ofPair 6 3) := by
  rw [three_quarters_two_ways]

/-! ## Cancellation -/

/-- Cancellation transported: subtracting what was added returns the original,
in the surreals, from the dyadic computation. -/
theorem cancel_transported (d e : Algebra.Order.Dyadic) :
    toSurreal (d + e) - toSurreal e = toSurreal d := by
  rw [toSurreal_add, add_sub_cancel_right]

/-- Exercised at concrete fractions rather than only in general. -/
theorem cancel_at_three_quarters :
    toSurreal (Dyadic.ofPair 3 2 + Dyadic.ofPair 1 1) - toSurreal (Dyadic.ofPair 1 1)
      = toSurreal (Dyadic.ofPair 3 2) :=
  cancel_transported _ _

/-! ## Rejection controls -/

/-- **Rejected**: `1/4` and `1/2` are different dyadics, so their images are
different surreals. A map that collapsed the dyadics would pass every
preservation theorem above and fail this one. -/
theorem quarter_ne_half :
    toSurreal (Dyadic.ofPair 1 2) ≠ toSurreal (Dyadic.ofPair 1 1) := by
  refine fun h => absurd (toSurreal_inj.mp h) ?_
  intro hd
  have : ((1 : ℚ) / 2 ^ 2) = ((1 : ℚ) / 2 ^ 1) := congrArg Dyadic.val hd
  norm_num at this

/-- **Rejected**: `3/4 < 1/2` is false on the executable side, and the
interpretation refuses it too. -/
theorem not_three_quarters_lt_half :
    ¬ (toSurreal (Dyadic.ofPair 3 2) < toSurreal (Dyadic.ofPair 1 1)) := by
  rw [toSurreal_lt_iff]
  simp only [Dyadic.lt_iff, Dyadic.val_ofPair]
  norm_num

/-- **Rejected**: `3/4` and `5/8` are *not* two spellings of one number, so the
well-definedness theorem is not saying that any two pairs agree. -/
theorem three_quarters_ne_five_eighths :
    toSurreal (Dyadic.ofPair 3 2) ≠ toSurreal (Dyadic.ofPair 5 3) := by
  refine fun h => absurd (toSurreal_inj.mp h) ?_
  intro hd
  have : ((3 : ℚ) / 2 ^ 2) = ((5 : ℚ) / 2 ^ 3) := congrArg Dyadic.val hd
  norm_num at this

/-- **Rejected**: the interpretation does not send a nonzero dyadic to `0`. -/
theorem half_ne_zero : toSurreal (Dyadic.ofPair 1 1) ≠ 0 := by
  rw [toSurreal_half]
  exact ne_of_gt (ladder_pos 1)

/-! ## General statements the examples instantiate -/

/-- The interpretation is strictly monotone, hence injective — the general
form of every rejection control above. -/
theorem strictMono_toSurreal : StrictMono toSurreal :=
  fun _ _ h => toSurreal_lt_iff.mpr h

/-- Every value in the image is an integer multiple of a rung, and every such
multiple is in the image: the image is exactly the set of dyadic surreals. -/
theorem mem_range_toSurreal_iff {x : Surreal} :
    (∃ d : Algebra.Order.Dyadic, toSurreal d = x) ↔ ∃ (m : ℤ) (k : ℕ), x = m • ladder k := by
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨m, k, rfl⟩ := Dyadic.exists_pair d
    exact ⟨m, k, by rw [toSurreal_ofPair, ofPairSurreal]⟩
  · rintro ⟨m, k, rfl⟩
    exact ⟨Dyadic.ofPair m k, by rw [toSurreal_ofPair, ofPairSurreal]⟩

/-- **And every value in the image is born finitely early.**  With
`mem_range_toSurreal_iff` this is one half of the characterisation of the
finite-birthday surreals. -/
theorem birthday_lt_omega0_of_mem_range {x : Surreal}
    (h : ∃ d : Algebra.Order.Dyadic, toSurreal d = x) : birthday x < Ordinal.omega0 := by
  obtain ⟨d, rfl⟩ := h
  exact birthday_toSurreal_lt_omega0 d

end DyadicExamples

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.DyadicExamples.half_add_half_surreal
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.DyadicExamples.three_quarters_same_image
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.DyadicExamples.quarter_ne_half
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.DyadicExamples.mem_range_toSurreal_iff
