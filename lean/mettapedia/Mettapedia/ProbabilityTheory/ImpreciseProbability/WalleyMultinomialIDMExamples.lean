import Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM

/-!
# Worked Examples for Walley's Multinomial IDM

Small exact examples for the categorical IDM credal-set bridge.  These are
reader-facing sanity checks for the theorem layer in `WalleyMultinomialIDM`.
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDMExamples

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM
open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

abbrev cat0 : Fin 3 := ⟨0, by decide⟩
abbrev cat1 : Fin 3 := ⟨1, by decide⟩

/-- A three-category evidence vector with counts `(2, 3, 5)`. -/
def triEvidence : MultiEvidence 3 :=
  ⟨![2, 3, 5]⟩

theorem triEvidence_total :
    triEvidence.total = 10 := by
  simp only [triEvidence, MultiEvidence.total, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : (![2, 3, 5] : Fin 3 → ℕ) 2 = 5 := rfl
  rw [h2]

/-- With `s = 2`, category `0` has lower predictive probability `2/(10+2)`. -/
theorem triEvidence_cat0_lower :
    lowerProb (credalSet triEvidence 2 (by norm_num)) (categoryGamble cat0) =
      1 / 6 := by
  rw [lowerProb_categoryGamble_eq_of_other
    (e := triEvidence) (s := 2) (hs := by norm_num)
    (i := cat0) (j := cat1) (hji := by decide)]
  unfold lowerEndpoint
  rw [triEvidence_total]
  norm_num [triEvidence, cat0]

/-- With `s = 2`, category `0` has upper predictive probability `(2+2)/(10+2)`. -/
theorem triEvidence_cat0_upper :
    upperProb (credalSet triEvidence 2 (by norm_num)) (categoryGamble cat0) =
      1 / 3 := by
  rw [upperProb_categoryGamble_eq]
  unfold upperEndpoint
  rw [triEvidence_total]
  norm_num [triEvidence, cat0]

/-- The category interval width is the IDM imprecision `s/(n+s) = 2/12`. -/
theorem triEvidence_cat0_width :
    upperProb (credalSet triEvidence 2 (by norm_num)) (categoryGamble cat0) -
        lowerProb (credalSet triEvidence 2 (by norm_num)) (categoryGamble cat0) =
      1 / 6 := by
  rw [category_width_eq_idmWidth_of_other
    (e := triEvidence) (s := 2) (hs := by norm_num)
    (i := cat0) (j := cat1) (hji := by decide)]
  rw [triEvidence_total]
  norm_num

/-- The credal-set result agrees with the existing `EvidenceDirichlet` formula. -/
theorem triEvidence_cat0_matches_EvidenceDirichlet :
    lowerProb
        (credalSet triEvidence IDMPredictiveContext.default.s
          IDMPredictiveContext.default.s_pos)
        (categoryGamble cat0) =
          idmLower IDMPredictiveContext.default triEvidence cat0 ∧
      upperProb
        (credalSet triEvidence IDMPredictiveContext.default.s
          IDMPredictiveContext.default.s_pos)
        (categoryGamble cat0) =
          idmUpper IDMPredictiveContext.default triEvidence cat0 ∧
      upperProb
        (credalSet triEvidence IDMPredictiveContext.default.s
          IDMPredictiveContext.default.s_pos)
        (categoryGamble cat0) -
        lowerProb
          (credalSet triEvidence IDMPredictiveContext.default.s
            IDMPredictiveContext.default.s_pos)
          (categoryGamble cat0) =
            idmWidth IDMPredictiveContext.default triEvidence := by
  exact ⟨
    lowerProb_categoryGamble_eq_idmLower_of_other
      (ctx := IDMPredictiveContext.default) (e := triEvidence)
      (i := cat0) (j := cat1) (hji := by decide),
    upperProb_categoryGamble_eq_idmUpper
      (ctx := IDMPredictiveContext.default) (e := triEvidence) (i := cat0),
    category_width_eq_EvidenceDirichlet_idmWidth_of_other
      (ctx := IDMPredictiveContext.default) (e := triEvidence)
      (i := cat0) (j := cat1) (hji := by decide)
  ⟩

end Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDMExamples
