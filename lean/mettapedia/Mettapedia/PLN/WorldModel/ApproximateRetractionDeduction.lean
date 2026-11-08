import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction

/-!
# Deduction on strengths after forgetting: explicit sensitivities and the guard at `pB = 1`

The deduction strength formula of `PLNDeduction`,

  `sAC = sAB · sBC + (1 - sAB) · (pC - pB · sBC) / (1 - pB)`,

is a readout on strengths, applied after forgetting has moved its inputs.  Its core
(`deductionCore`) is the formula of `simpleDeductionStrengthFormula` on consistent inputs with
`pB ≤ 0.99` (`simpleDeduction_eq_core`).

* **Explicit sensitivities** (`deductionCore_sensitivity`).  With `pB, pB' ≤ 1 - η`, `pC` and
  `sBC` in `[0, 1]` on one side and `sAB'` in `[0, 1]` on the other, the output moves by at most
  `(1 + 1/η) |ΔsAB| + |ΔpB| / η² + |ΔpC| / η + (1 + 1/η) |ΔsBC|`.
  Each constant comes from an exact identity in one input (`deductionCore_sub_sAB`,
  `deductionCore_sub_pB`, `deductionCore_sub_pC`, `deductionCore_sub_sBC`).
* **No constant works up to `pB = 1`** (`deductionCore_not_lipschitz`), on coherent inputs too:
  a bound on the deduction needs a certified gap below `pB = 1`.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ApproximateRetractionDeduction

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
  (simpleDeductionStrengthFormula conditionalProbabilityConsistency)

/-- The core of the deduction strength formula. -/
noncomputable def deductionCore (sAB pB pC sBC : ℝ) : ℝ :=
  sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)

/-- On consistent inputs below the switch at `0.99`, the formula of `PLNDeduction` is the core. -/
theorem simpleDeduction_eq_core {pA pB pC sAB sBC : ℝ}
    (consistent : conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (below : ¬ pB > 0.99) :
    simpleDeductionStrengthFormula pA pB pC sAB sBC = deductionCore sAB pB pC sBC := by
  unfold simpleDeductionStrengthFormula deductionCore
  rw [if_neg (not_not.mpr consistent), if_neg below]

/-! ## One input at a time -/

theorem deductionCore_sub_sAB (sAB sAB' pB pC sBC : ℝ) :
    deductionCore sAB pB pC sBC - deductionCore sAB' pB pC sBC =
      (sAB - sAB') * (sBC - (pC - pB * sBC) / (1 - pB)) := by
  unfold deductionCore
  ring

theorem deductionCore_sub_pB (sAB pB pB' pC sBC : ℝ) (hb : (1 : ℝ) - pB ≠ 0)
    (hb' : (1 : ℝ) - pB' ≠ 0) :
    deductionCore sAB pB pC sBC - deductionCore sAB pB' pC sBC =
      (1 - sAB) * (pC - sBC) * (pB - pB') / ((1 - pB) * (1 - pB')) := by
  unfold deductionCore
  field_simp
  ring

theorem deductionCore_sub_pC (sAB pB pC pC' sBC : ℝ) :
    deductionCore sAB pB pC sBC - deductionCore sAB pB pC' sBC =
      (1 - sAB) * (pC - pC') / (1 - pB) := by
  unfold deductionCore
  ring

theorem deductionCore_sub_sBC (sAB pB pC sBC sBC' : ℝ) :
    deductionCore sAB pB pC sBC - deductionCore sAB pB pC sBC' =
      (sAB - (1 - sAB) * pB / (1 - pB)) * (sBC - sBC') := by
  unfold deductionCore
  ring

/-- A quotient with a numerator of size at most one and a denominator at least `η` is at most
`1 / η`. -/
theorem abs_div_le_inv {x y η : ℝ} (hη : 0 < η) (hy : η ≤ y) (hx : |x| ≤ 1) :
    |x / y| ≤ 1 / η := by
  have hy₀ : 0 < y := hη.trans_le hy
  rw [abs_div, abs_of_pos hy₀, div_le_div_iff₀ hy₀ hη]
  nlinarith [abs_nonneg x]

/-- **Explicit sensitivities of deduction away from `pB = 1`.** -/
theorem deductionCore_sensitivity {η sAB sAB' pB pB' pC pC' sBC sBC' : ℝ} (hη : 0 < η)
    (ha' : 0 ≤ sAB' ∧ sAB' ≤ 1) (hb : 0 ≤ pB ∧ pB ≤ 1 - η) (hb' : 0 ≤ pB' ∧ pB' ≤ 1 - η)
    (hc : 0 ≤ pC ∧ pC ≤ 1) (hd : 0 ≤ sBC ∧ sBC ≤ 1) :
    |deductionCore sAB pB pC sBC - deductionCore sAB' pB' pC' sBC'| ≤
      (1 + 1 / η) * |sAB - sAB'| + |pB - pB'| / η ^ 2 + |pC - pC'| / η +
        (1 + 1 / η) * |sBC - sBC'| := by
  obtain ⟨a₀', a₁'⟩ := ha'
  obtain ⟨b₀, b₁⟩ := hb
  obtain ⟨b₀', b₁'⟩ := hb'
  obtain ⟨c₀, c₁⟩ := hc
  obtain ⟨d₀, d₁⟩ := hd
  have e₁ : η ≤ 1 - pB := by linarith
  have e₂ : η ≤ 1 - pB' := by linarith
  have p₁ : 0 < 1 - pB := hη.trans_le e₁
  have p₂ : 0 < 1 - pB' := hη.trans_le e₂
  have split : deductionCore sAB pB pC sBC - deductionCore sAB' pB' pC' sBC' =
      (deductionCore sAB pB pC sBC - deductionCore sAB' pB pC sBC) +
        (deductionCore sAB' pB pC sBC - deductionCore sAB' pB' pC sBC) +
        (deductionCore sAB' pB' pC sBC - deductionCore sAB' pB' pC' sBC) +
        (deductionCore sAB' pB' pC' sBC - deductionCore sAB' pB' pC' sBC') := by
    ring
  rw [split, deductionCore_sub_sAB, deductionCore_sub_pB _ _ _ _ _ p₁.ne' p₂.ne',
    deductionCore_sub_pC, deductionCore_sub_sBC]
  -- the sAB term
  have q₁ : |(pC - pB * sBC) / (1 - pB)| ≤ 1 / η :=
    abs_div_le_inv hη e₁ (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
  have t₁ : |(sAB - sAB') * (sBC - (pC - pB * sBC) / (1 - pB))| ≤ (1 + 1 / η) * |sAB - sAB'| := by
    rw [abs_mul]
    have bound : |sBC - (pC - pB * sBC) / (1 - pB)| ≤ 1 + 1 / η := by
      obtain ⟨lo, hi⟩ := abs_le.mp q₁
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact (mul_le_mul_of_nonneg_left bound (abs_nonneg _)).trans_eq (mul_comm _ _)
  -- the pB term
  have t₂ : |(1 - sAB') * (pC - sBC) * (pB - pB') / ((1 - pB) * (1 - pB'))| ≤
      |pB - pB'| / η ^ 2 := by
    rw [abs_div, abs_of_pos (mul_pos p₁ p₂), abs_mul, abs_mul]
    have u : |1 - sAB'| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have v : |pC - sBC| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have num : |1 - sAB'| * |pC - sBC| * |pB - pB'| ≤ |pB - pB'| :=
      (mul_le_mul_of_nonneg_right (mul_le_one₀ u (abs_nonneg _) v) (abs_nonneg _)).trans_eq
        (one_mul _)
    have den : η ^ 2 ≤ (1 - pB) * (1 - pB') := by
      rw [pow_two]
      exact mul_le_mul e₁ e₂ hη.le p₁.le
    exact div_le_div₀ (abs_nonneg _) num (by positivity) den
  -- the pC term
  have t₃ : |(1 - sAB') * (pC - pC') / (1 - pB')| ≤ |pC - pC'| / η := by
    rw [abs_div, abs_mul, abs_of_pos p₂]
    have u : |1 - sAB'| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have num : |1 - sAB'| * |pC - pC'| ≤ |pC - pC'| :=
      (mul_le_mul_of_nonneg_right u (abs_nonneg _)).trans_eq (one_mul _)
    exact div_le_div₀ (abs_nonneg _) num hη e₂
  -- the sBC term
  have t₄ : |(sAB' - (1 - sAB') * pB' / (1 - pB')) * (sBC - sBC')| ≤
      (1 + 1 / η) * |sBC - sBC'| := by
    rw [abs_mul]
    have small : |(1 - sAB') * pB' / (1 - pB')| ≤ 1 / η :=
      abs_div_le_inv hη e₂ (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    have bound : |sAB' - (1 - sAB') * pB' / (1 - pB')| ≤ 1 + 1 / η := by
      obtain ⟨lo, hi⟩ := abs_le.mp small
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact mul_le_mul_of_nonneg_right bound (abs_nonneg _)
  calc _ ≤ |(sAB - sAB') * (sBC - (pC - pB * sBC) / (1 - pB))| +
          |(1 - sAB') * (pC - sBC) * (pB - pB') / ((1 - pB) * (1 - pB'))| +
          |(1 - sAB') * (pC - pC') / (1 - pB')| +
          |(sAB' - (1 - sAB') * pB' / (1 - pB')) * (sBC - sBC')| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

/-! ## No constant up to `pB = 1` -/

/-- With `sAB = sBC = 0` the core reads `pC / (1 - pB)`. -/
theorem deductionCore_zero_zero (pB pC : ℝ) : deductionCore 0 pB pC 0 = pC / (1 - pB) := by
  unfold deductionCore
  ring

/-- **No constant works up to `pB = 1`.**  For every `K`, coherent inputs with `pB` close to `1`
move the output by more than `K` times the change in `pB`: at `pC = δ`, moving `pB` from `1 - δ`
to `1 - 2δ` moves the output from `1` to `1/2`. -/
theorem deductionCore_not_lipschitz (K : ℝ) :
    ∃ pB pB' pC : ℝ, (0 ≤ pB ∧ pB < 1) ∧ (0 ≤ pB' ∧ pB' < 1) ∧ (0 ≤ pC ∧ pC ≤ 1) ∧
      pC ≤ 1 - pB ∧ pC ≤ 1 - pB' ∧
      K * |pB - pB'| < |deductionCore 0 pB pC 0 - deductionCore 0 pB' pC 0| := by
  set δ : ℝ := 1 / (4 * (|K| + 1)) with hδ
  have hK : 0 ≤ |K| := abs_nonneg K
  have hpos : 0 < δ := by rw [hδ]; positivity
  have hsmall : δ * (4 * (|K| + 1)) = 1 := by
    rw [hδ]
    exact div_mul_cancel₀ 1 (by positivity)
  have hle : δ ≤ 1 / 4 := by nlinarith [mul_nonneg hpos.le hK]
  have first : deductionCore 0 (1 - δ) δ 0 = 1 := by
    rw [deductionCore_zero_zero, sub_sub_cancel, div_self hpos.ne']
  have second : deductionCore 0 (1 - 2 * δ) δ 0 = 1 / 2 := by
    rw [deductionCore_zero_zero, sub_sub_cancel, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  refine ⟨1 - δ, 1 - 2 * δ, δ, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨hpos.le, by linarith⟩, by linarith, by linarith, ?_⟩
  rw [first, second, show (1 : ℝ) - δ - (1 - 2 * δ) = δ by ring, abs_of_pos hpos,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hKδ : K * δ ≤ |K| * δ := mul_le_mul_of_nonneg_right (le_abs_self K) hpos.le
  nlinarith [mul_nonneg hpos.le hK]

end Mettapedia.PLN.WorldModel.ApproximateRetractionDeduction

open Mettapedia.PLN.WorldModel.ApproximateRetractionDeduction in
#print axioms simpleDeduction_eq_core
open Mettapedia.PLN.WorldModel.ApproximateRetractionDeduction in
#print axioms deductionCore_sub_pB
open Mettapedia.PLN.WorldModel.ApproximateRetractionDeduction in
#print axioms deductionCore_sensitivity
open Mettapedia.PLN.WorldModel.ApproximateRetractionDeduction in
#print axioms deductionCore_not_lipschitz
